// The trace model: parsing the checker trace. Pure functions, no DOM.
//
// A trace is JSON lines written by `tracing` (see `crates/flux-common/src/dbg.rs`):
//   {fields: {event, ...}, span: {name: <mode>, def_id: <function>}}

/** The fields of a trace event, as `tracing` wrote them. */
export type Fields = Record<string, any>;

/** `{file, start_line, start_col, end_line, end_col}` (1-based lines). */
export interface SrcLoc {
  file?: string;
  start_line: number;
  start_col: number;
  end_line: number;
  end_col: number;
}

export interface Stmt {
  t: "stmt";
  /** "mir" for MIR statements, otherwise the ghost statement's kind (`fold`, `unfold`, ...) */
  kind: string;
  text: string;
  span: string;
  loc: SrcLoc | null;
}
export interface Term {
  t: "term";
  kind: "term";
  text: string;
}
export interface Goto {
  t: "goto";
  kind: "goto";
  text: string;
  target: string;
}
/**
 * An edge separator: the items after it, up to the next separator, are checked on the edge to
 * `target`. `how` is "goto" (a join point), "enter" (the target block was checked right after)
 * or "open" (unknown).
 */
export interface Sep {
  t: "sep";
  target: string | null;
  how: "goto" | "enter" | "open" | null;
}

interface Events {
  /** index within the section */
  i: number;
  before: Fields | null;
  after: Fields | null;
  /** the item never got its end event: the check failed here */
  noend?: boolean;
}
export type Item = (Stmt | Term | Goto) & Events;
export type SecItem = Item | (Sep & { i: number });

export interface Section {
  kind: "entry" | "block";
  bb: string;
  visit: number;
  items: SecItem[];
  term: Item | null;
  startRaw: Fields | null;
  idx: number;
}

export interface Mode {
  name: string;
  sections: Section[];
  /** statements without an end event */
  errors: number;
}

export interface Kvar {
  name: string;
  args?: string[];
  body?: { text: string };
}

export interface Fn {
  id: string;
  modes: Map<string, Mode>;
  solution: Kvar[] | null;
  /** local (`_3`) -> source name */
  names: Map<string, string>;
}

export interface Trace {
  fns: Fn[];
}

const GHOST_RE = /^(fold|unfold|ptr_to_ref|unblock|init|kill)\(/;
const INERT_RE = /^(StorageLive|StorageDead|Nop|nop)\b/;
export const isGhost = (it: SecItem) => it.t === "stmt" && it.kind !== "mir";
export const isInert = (it: SecItem) => it.t === "stmt" && INERT_RE.test(it.text);

function tryJSON(s: string): any {
  try {
    return JSON.parse(s);
  } catch {
    return null;
  }
}
// `*_json` fields arrive either as a JSON string or as an object.
const asJSON = (v: unknown) => (typeof v === "string" ? tryJSON(v) : v);

/**
 * Parsing state of a mode: `cur` is the open section, `stack` the items waiting for their end
 * event, `afterTerm` whether the open section's terminator has been checked (what follows it is
 * checked on an outgoing edge), `edge` the open edge separator.
 */
interface ModeBuilder {
  mode: Mode;
  cur: Section;
  stack: Item[];
  visits: Map<string, number>;
  afterTerm: boolean;
  edge: (Sep & { i: number }) | null;
  lastGoto: Item | null;
}

export function parseTrace(text: string): Trace {
  const fns = new Map<string, Fn>();
  const builders = new Map<Mode, ModeBuilder>();
  let lastRefineFn: Fn | null = null;
  for (const line of text.split("\n")) {
    const d = line.trim() ? tryJSON(line) : null;
    const f: Fields | undefined = d?.fields;
    const ev: string | undefined = f?.event;
    if (!f || !ev) continue;
    if (ev === "solution") {
      // the solution has no function span: it belongs to the function checked last in refine mode
      if (lastRefineFn) lastRefineFn.solution = tryJSON(f.solution) || [];
      continue;
    }
    const sp = d.span || {};
    if (!sp.def_id) continue;
    let fn = fns.get(sp.def_id);
    if (!fn) {
      fn = { id: sp.def_id, modes: new Map(), solution: null, names: new Map() };
      fns.set(sp.def_id, fn);
    }
    // Statement events carry each local's source name (none for temporaries). A local keeps its
    // name for the whole function, so the names apply to every event of it.
    const bs = f.env_json && asJSON(f.env_json);
    if (Array.isArray(bs)) {
      for (const b of bs) {
        const local = b?.local?.Local;
        if (local && b.name && !fn.names.has(local)) fn.names.set(local, b.name);
      }
    }
    const mname: string = sp.name || "?";
    let mode = fn.modes.get(mname);
    if (!mode) {
      mode = { name: mname, sections: [], errors: 0 };
      fn.modes.set(mname, mode);
      builders.set(mode, newBuilder(mode));
    }
    if (mname === "refine") lastRefineFn = fn;
    feed(builders.get(mode)!, ev, f);
  }
  for (const b of builders.values()) finish(b);
  return { fns: [...fns.values()] };
}

function newBuilder(mode: Mode): ModeBuilder {
  const entry: Section = { kind: "entry", bb: "entry", visit: 0, items: [], term: null, startRaw: null, idx: 0 };
  mode.sections.push(entry);
  return { mode, cur: entry, stack: [], visits: new Map(), afterTerm: false, edge: null, lastGoto: null };
}

/** The innermost open item satisfying `pred` gets `f` as its end event. */
function closeItem(m: ModeBuilder, pred: (it: Item) => boolean, f: Fields) {
  for (let i = m.stack.length - 1; i >= 0; i--) {
    if (pred(m.stack[i])) {
      m.stack[i].after = f;
      m.stack.splice(i, 1);
      return;
    }
  }
}

function feed(m: ModeBuilder, ev: string, f: Fields) {
  const items = m.cur.items;
  switch (ev) {
    case "basic_block_start": {
      closeEdge(m, f.bb, "enter");
      const visit = (m.visits.get(f.bb) || 0) + 1;
      m.visits.set(f.bb, visit);
      m.cur = { kind: "block", bb: f.bb, visit, items: [], term: null, startRaw: f, idx: 0 };
      m.mode.sections.push(m.cur);
      m.afterTerm = false;
      break;
    }
    case "statement_start": {
      if (m.afterTerm && !m.edge) openEdge(m);
      const ghost = GHOST_RE.exec(f.stmt);
      const it: Item = {
        t: "stmt", kind: ghost ? ghost[1] : "mir", text: f.stmt, span: shortSpan(f.stmt_span),
        loc: srcLoc(f.stmt_span_json), before: f, after: null, i: 0,
      };
      items.push(it);
      m.stack.push(it);
      break;
    }
    case "statement_end":
      closeItem(m, it => it.text === f.stmt, f);
      break;
    case "terminator_start": {
      const it: Item = { t: "term", kind: "term", text: f.terminator, before: f, after: null, i: 0 };
      items.push(it);
      m.cur.term = it;
      m.stack.push(it);
      break;
    }
    case "terminator_end":
      closeItem(m, it => it.t === "term" && it.text === f.terminator, f);
      m.afterTerm = true;
      m.edge = null;
      break;
    case "refine_goto":
    case "shape_goto_enter": {
      if (!m.edge) openEdge(m);
      const it: Item = { t: "goto", kind: "goto", text: "goto " + f.target, target: f.target, before: f, after: null, i: 0 };
      items.push(it);
      m.lastGoto = it;
      closeEdge(m, f.target, "goto");
      break;
    }
    case "shape_goto_exit":
      if (m.lastGoto && m.lastGoto.t === "goto" && m.lastGoto.target === f.target) m.lastGoto.after = f;
      break;
  }
}

function openEdge(m: ModeBuilder) {
  m.edge = { t: "sep", target: null, how: null, i: 0 };
  m.cur.items.push(m.edge);
}

function closeEdge(m: ModeBuilder, target: string, how: Sep["how"]) {
  if (m.edge) {
    m.edge.target = target;
    m.edge.how = how;
  }
  m.edge = null;
}

function finish(b: ModeBuilder) {
  const m = b.mode;
  for (const it of b.stack) it.noend = true;
  m.errors = b.stack.length;
  if (!m.sections[0].items.length) m.sections.shift();
  // An edge closed by entering a join point was not followed by that block: join points are
  // checked later, from the queue. So the edge actually went to an inlined exit block (or unknown).
  const joins = new Set<string>();
  for (const s of m.sections) for (const it of s.items) if (it.t === "goto") joins.add(it.target);
  for (const s of m.sections) {
    for (const it of s.items) {
      if (it.t !== "sep") continue;
      if (!it.target || (it.how === "enter" && joins.has(it.target))) {
        it.how = "open";
        it.target = null;
      }
    }
  }
  // stable ids: section `idx`, item `i` within its section
  m.sections.forEach((s, n) => {
    s.idx = n;
    s.items.forEach((it, i) => {
      it.i = i;
    });
  });
}

function srcLoc(j: unknown): SrcLoc | null {
  const o = asJSON(j);
  return o && o.start_line ? o : null;
}

/** `/path/to/input.rs:3:5: 3:10` -> `input.rs:3:5` */
function shortSpan(s: string | undefined): string {
  if (!s) return "";
  const m = /([^/]+\.rs):(\d+):(\d+)/.exec(s);
  return m ? `${m[1]}:${m[2]}:${m[3]}` : s;
}

/** Every location that appears in some environment of the function, `_0`, `_1`, ... first. */
const locsCache = new WeakMap<Fn, string[]>();
export function fnLocations(fn: Fn, envKeys: (env: string) => string[]): string[] {
  const cached = locsCache.get(fn);
  if (cached) return cached;
  const keys = new Set<string>();
  const add = (env: unknown) => {
    if (typeof env === "string") for (const k of envKeys(env)) keys.add(k);
  };
  for (const m of fn.modes.values()) {
    for (const s of m.sections) {
      add(s.startRaw?.env);
      for (const it of s.items) {
        if (it.t === "sep") continue;
        add(it.before?.env);
        add(it.after?.env);
      }
    }
  }
  const num = (k: string) => {
    const m = /^_(\d+)$/.exec(k);
    return m ? +m[1] : Infinity;
  };
  const locs = [...keys].sort((a, b) => num(a) - num(b) || a.localeCompare(b, undefined, { numeric: true }));
  locsCache.set(fn, locs);
  return locs;
}
