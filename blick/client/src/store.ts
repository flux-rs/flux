// Application state. Each program tab has its own source, flags, last run (trace and output)
// and view state. Everything but the transient state (the selected row, a run in progress)
// persists in the browser: the last runs in IndexedDB (see persist.ts), the rest in localStorage.

import { create } from "zustand";
import { persist } from "zustand/middleware";
import { runOverSocket } from "./api";
import { plain } from "./components/Ansi";
import { deleteRun, loadRun, saveRun } from "./persist";
import { parseTrace, type Fn, type Mode, type Trace } from "./trace/model";

export type ViewKind = "graph" | "all" | "block";

/** What the trace view shows: a function, one of its modes (checker passes), and a view of it. */
export interface ViewState {
  fnId: string | null;
  mode: string | null;
  kind: ViewKind;
  /** the blocks open side by side in the block view */
  bbs: string[];
}

export interface Program {
  id: number;
  name: string;
  /** the user named the tab; otherwise it is named after the program's first function */
  nameSet: boolean;
  source: string;
  flags: string;
  view: ViewState;
  /** "fn|mode|section:item": statements the user collapsed */
  folded: string[];
  /** fn id -> locations hidden from the environments */
  hidden: Record<string, string[]>;
  /** collapsed sections in the all-blocks view (section idx), plus "sol-open" */
  collapsed: string[];
  /** "fn|mode" -> the graph's state */
  graphs: Record<string, GraphState>;
}

/** What the user did to a graph: the nodes they dragged, and where they panned and zoomed to. */
export interface GraphState {
  drag: Record<string, { x: number; y: number }>;
  viewport?: { x: number; y: number; zoom: number };
}

export type RunStatus = "none" | "running" | "ok" | "err";

/** The last run of a program. */
export interface Run {
  /** the trace, parsed from `trace` */
  data: Trace | null;
  /** the trace as Flux wrote it */
  trace: string;
  ranSource: string | null;
  ranFlags: string | null;
  status: RunStatus;
  statusText: string;
  statusErr: boolean;
  /** set when Flux ran but wrote no trace */
  noTrace: boolean;
  buildLog: string[];
}

export interface Ui {
  theme: "light" | "dark" | null;
  hideinert: boolean;
  hidelt: boolean;
  localnames: boolean;
  srcOpen: boolean;
  /** the editor's font size, in px */
  editorFontSize: number;
  /** vim keybindings in the editor */
  vim: boolean;
}

export const EDITOR_FONT_SIZE = 14;

interface State {
  ui: Ui;
  programs: Program[];
  active: number;
  nextId: number;
  runs: Record<number, Run>;
  running: boolean;
  serverInfo: string;
  /** the selected statement row: "<section idx>:<item i>" */
  selRow: string | null;
}

const emptyView = (): ViewState => ({ fnId: null, mode: null, kind: "graph", bbs: [] });
const emptyRun = (): Run => ({
  data: null, trace: "", ranSource: null, ranFlags: null, status: "none", statusText: "", statusErr: false,
  noTrace: false, buildLog: [],
});

function derivedName(source: string, others: Program[]): string {
  const m = /\bfn\s+([A-Za-z_]\w*)/.exec(source);
  if (m) return m[1];
  const taken = new Set(others.map(q => q.name));
  for (let i = 1; ; i++) if (!taken.has(`untitled ${i}`)) return `untitled ${i}`;
}

function newProgram(id: number, others: Program[]): Program {
  return {
    id, name: derivedName("", others), nameSet: false, source: "", flags: "", view: emptyView(), folded: [], hidden: {},
    collapsed: [], graphs: {},
  };
}

export const useStore = create<State>()(
  persist(
    (): State => ({
      ui: { theme: null, hideinert: true, hidelt: false, localnames: true, srcOpen: true, editorFontSize: EDITOR_FONT_SIZE, vim: false },
      programs: [newProgram(1, [])],
      active: 1,
      nextId: 2,
      runs: {},
      running: false,
      serverInfo: "",
      selRow: null,
    }),
    {
      name: "blick",
      partialize: s => ({ ui: s.ui, programs: s.programs, active: s.active, nextId: s.nextId }),
      // options added since the state was saved get their defaults
      merge: (persisted, current) => {
        const p = persisted as Partial<State>;
        const programs = p.programs?.map(q => ({ ...newProgram(q.id, []), ...q }));
        return { ...current, ...p, ui: { ...current.ui, ...p.ui }, ...(programs ? { programs } : {}) };
      },
    },
  ),
);

const set = useStore.setState;
const get = useStore.getState;

// ---- selectors ----

export const curProgram = (s: State) => s.programs.find(p => p.id === s.active) ?? s.programs[0];
export const curRun = (s: State): Run => s.runs[curProgram(s).id] ?? EMPTY_RUN;
const EMPTY_RUN = emptyRun();
export const isDirty = (p: Program, r: Run | undefined) =>
  !!r && r.ranSource !== null && (p.source !== r.ranSource || p.flags !== r.ranFlags);

/** The function and mode the view shows, resolved against the trace (they may be gone after a re-run). */
export function resolveView(data: Trace | null, v: ViewState): { fn: Fn; mode: Mode; view: ViewState } | null {
  if (!data || !data.fns.length) return null;
  const fn = data.fns.find(f => f.id === v.fnId) ?? data.fns[0];
  const mode = (v.mode && fn.modes.get(v.mode)) || fn.modes.get("refine") || [...fn.modes.values()][0];
  if (!mode) return null;
  let view = v;
  if (v.kind === "block") {
    const bbs = v.bbs.filter(bb => mode.sections.some(s => s.bb === bb));
    view = bbs.length ? { ...v, bbs } : { ...v, kind: "graph", bbs: [] };
  }
  return { fn, mode, view: { ...view, fnId: fn.id, mode: mode.name } };
}

// ---- actions ----

function updateProgram(id: number, f: (p: Program) => Partial<Program>) {
  set(s => ({ programs: s.programs.map(p => (p.id === id ? { ...p, ...f(p) } : p)) }));
}
function updateRun(id: number, f: (r: Run) => Partial<Run>) {
  set(s => {
    const r = s.runs[id] ?? emptyRun();
    return { runs: { ...s.runs, [id]: { ...r, ...f(r) } } };
  });
}

export function setUi(patch: Partial<Ui>) {
  set(s => ({ ui: { ...s.ui, ...patch } }));
}

/** Zooms the editor's font in or out by `step` px, or back to the default size (`step` null). */
export function zoomEditor(step: number | null) {
  const size = get().ui.editorFontSize;
  setUi({ editorFontSize: step === null ? EDITOR_FONT_SIZE : Math.min(32, Math.max(8, Math.round(size + step))) });
}

export function activate(id: number) {
  if (get().active === id) return;
  set({ active: id, selRow: null });
}

export function addProgram() {
  set(s => {
    const p = newProgram(s.nextId, s.programs);
    return { programs: [...s.programs, p], nextId: s.nextId + 1, active: p.id, selRow: null };
  });
}

export function closeProgram(id: number) {
  const s = get();
  const i = s.programs.findIndex(p => p.id === id);
  const p = s.programs[i];
  if (!p || s.runs[id]?.status === "running") return;
  if (p.source.trim() && !confirm(`Close "${p.name}"? Its source is not saved anywhere else.`)) return;
  let programs = s.programs.filter(q => q.id !== id);
  let nextId = s.nextId;
  if (!programs.length) programs = [newProgram(nextId++, [])];
  const runs = { ...s.runs };
  delete runs[id];
  const active = id === s.active ? programs[Math.min(i, programs.length - 1)].id : s.active;
  set({ programs, runs, nextId, active, ...(active !== s.active ? { selRow: null } : {}) });
  deleteRun(id);
}

export function renameProgram(id: number, name: string) {
  const v = name.trim();
  updateProgram(id, p => ({
    nameSet: v !== "", // an empty name goes back to the derived one
    name: v || derivedName(p.source, get().programs.filter(q => q.id !== id)),
  }));
}

export function setSource(source: string) {
  const id = get().active;
  updateProgram(id, p => ({
    source,
    name: p.nameSet ? p.name : derivedName(source, get().programs.filter(q => q.id !== id)),
  }));
}

export function setFlags(flags: string) {
  updateProgram(get().active, () => ({ flags }));
}

/** Changes the active program's view. Leaving a view clears the selected row. */
export function go(patch: Partial<ViewState>) {
  const p = curProgram(get());
  updateProgram(p.id, q => ({ view: { ...q.view, ...patch } }));
  set({ selRow: null });
}

export function selectFn(fnId: string) {
  go({ fnId, kind: "graph", bbs: [] });
  updateProgram(get().active, () => ({ collapsed: [] }));
}

/** Switches mode, staying on the open blocks that exist in the other mode (see `resolveView`). */
export function selectMode(mode: string) {
  const p = curProgram(get());
  updateProgram(p.id, q => ({ view: { ...q.view, mode }, collapsed: [] }));
}

export function toggleCollapsed(key: string) {
  updateProgram(get().active, p => ({
    collapsed: p.collapsed.includes(key) ? p.collapsed.filter(k => k !== key) : [...p.collapsed, key],
  }));
}

/** Updates the state of the active program's graph of "fn|mode" `key`. */
export function setGraphState(key: string, f: (g: GraphState) => GraphState) {
  updateProgram(get().active, p => ({ graphs: { ...p.graphs, [key]: f(p.graphs[key] ?? { drag: {} }) } }));
}

export function setSelRow(selRow: string | null) {
  set({ selRow });
}

/** Folds the statements `keys`, or unfolds them if they are all folded. */
export function toggleFold(keys: string[]) {
  updateProgram(get().active, p => {
    const folded = new Set(p.folded);
    if (keys.every(k => folded.has(k))) for (const k of keys) folded.delete(k);
    else for (const k of keys) folded.add(k);
    return { folded: [...folded] };
  });
}

export function setHidden(fnId: string, locs: string[]) {
  updateProgram(get().active, p => ({ hidden: { ...p.hidden, [fnId]: locs } }));
}

export function setServerInfo(serverInfo: string) {
  set({ serverInfo });
}

// ---- running Flux ----

export function setStatus(text: string, err: boolean) {
  updateRun(get().active, () => ({ statusText: text, statusErr: err }));
}

/**
 * Runs Flux on the active program. One run at a time (the server serializes `cargo x run`
 * anyway). The result goes to the tab that started the run, even if another tab is active by the
 * time it finishes.
 */
export async function runFlux() {
  if (get().running) return;
  const p = curProgram(get());
  const { id, source, flags } = p;
  if (!source.trim()) {
    setStatus("Nothing to run: the program is empty.", true);
    return;
  }
  set({ running: true });
  updateRun(id, () => ({
    status: "running", statusText: "Running cargo x run (rebuilds Flux if the sources changed)...", statusErr: false, buildLog: [],
  }));

  // Output lines arrive quickly while cargo builds: they are added once per frame.
  let pending: string[] = [];
  let frame = 0;
  const flush = () => {
    frame = 0;
    if (!pending.length) return;
    const lines = pending;
    pending = [];
    // the latest line doubles as the status while the run is going ("Compiling flux-refineck ...")
    const last = lines.map(plain).reverse().find(l => !l.startsWith("$ "));
    updateRun(id, r => ({ buildLog: [...r.buildLog, ...lines], ...(last !== undefined ? { statusText: last.trim().slice(0, 160) } : {}) }));
  };

  try {
    const out = await runOverSocket({ source, flags: flags.trim().split(/\s+/).filter(Boolean) }, line => {
      pending.push(line);
      if (!frame) frame = requestAnimationFrame(flush);
    });
    cancelAnimationFrame(frame);
    flush();
    const when = out.elapsed != null ? ` in ${out.elapsed}s` : "";
    const statusText = out.ok ? `ok${when}`
      : out.elapsed == null ? "Run failed (see the output)"
      : out.exit === null ? `timed out${when}`
      : `cargo x run exited with ${out.exit}${when} (see the output)`;
    updateRun(id, () => ({
      status: out.ok ? "ok" : "err", statusText, statusErr: !out.ok, ranSource: source, ranFlags: flags,
      // Keep the view state when re-running: it is restored if the function still exists.
      data: out.trace ? parseTrace(out.trace) : null,
      trace: out.trace,
      noTrace: !out.trace,
    }));
    // The new trace has new graphs (and nodes of other sizes). Statement ids may name other
    // statements in it.
    updateProgram(id, () => ({ graphs: {} }));
    if (get().active === id) set({ selRow: null });
  } catch (e) {
    cancelAnimationFrame(frame);
    flush();
    updateRun(id, () => ({ status: "err", statusText: `Request failed: ${e instanceof Error ? e.message : e}`, statusErr: true }));
  } finally {
    set({ running: false });
    const r = get().runs[id];
    if (r && get().programs.some(q => q.id === id)) {
      const { data: _, ...saved } = r;
      saveRun(id, saved);
    }
  }
}

/** Loads the saved last runs of the programs (at startup). */
export async function loadRuns() {
  await Promise.all(get().programs.map(async p => {
    const saved = await loadRun(p.id);
    // a run started in the meantime wins
    if (!saved || get().runs[p.id]) return;
    updateRun(p.id, () => ({ ...saved, status: saved.status === "running" ? "none" : saved.status, data: saved.trace ? parseTrace(saved.trace) : null }));
  }));
}
