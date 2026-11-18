// The block views: the open blocks side by side ("block"), or every block of the mode ("all"),
// each statement followed by the environment after it.

import { useEffect, useMemo, useRef, type ReactNode } from "react";
import { useHotkeys } from "react-hotkeys-hook";
import { go, setSelRow, toggleCollapsed, toggleFold, useStore, type ViewState } from "../store";
import { buildCfg } from "../trace/cfg";
import { type Fn, type Item, isGhost, isInert, type Mode, type Section, type SecItem, type Sep } from "../trace/model";
import { envBindings, matchClose, rcxFacts } from "../trace/text";
import { GhostIcon } from "./icons";
import { BindingView, commaList, ptrHoverHandlers, Rich } from "./text";

interface Props {
  fn: Fn;
  mode: Mode;
  view: ViewState;
  hideinert: boolean;
}

export function edgeLabel(sep: Sep, target: ReactNode): ReactNode {
  return sep.how === "goto" ? <>edge to {target} (join point)</>
    : sep.how === "enter" ? <>edge to {target}</>
    : "edge to exit block (inlined) or unknown";
}

export function BlockView({ fn, mode, view, hideinert }: Props) {
  const collapsed = useStore(s => s.collapsed);
  const selRow = useStore(s => s.selRow);
  const folded = useStore(s => s.programs.find(p => p.id === s.active)?.folded);
  const hiddenList = useStore(s => s.programs.find(p => p.id === s.active)?.hidden[fn.id]);
  const foldedSet = useMemo(() => new Set(folded), [folded]);
  const hidden = useMemo(() => new Set(hiddenList), [hiddenList]);
  const cfg = buildCfg(mode);
  const single = view.kind === "block";
  const ref = useRef<HTMLDivElement>(null);
  const hover = useMemo(ptrHoverHandlers, []);

  // a new view starts at the top
  useEffect(() => {
    ref.current?.scrollTo(0, 0);
  }, [fn.id, view.kind, view.bbs.join(",")]);

  useHotkeys("escape", () => go({ kind: "graph", bbs: [] }));
  // move the row selection down / up
  useHotkeys(["j", "k"], e => {
    const rows = [...(ref.current?.querySelectorAll<HTMLElement>(".row[data-id]") ?? [])];
    if (!rows.length) return;
    let i = rows.findIndex(r => r.dataset.id === selRow);
    i = e.key === "j" ? Math.min(rows.length - 1, i + 1) : Math.max(0, i < 0 ? 0 : i - 1);
    setSelRow(rows[i].dataset.id!);
    requestAnimationFrame(() => ref.current?.querySelector(`.row[data-id="${rows[i].dataset.id}"]`)?.scrollIntoView({ block: "nearest" }));
  }, [selRow]);

  const ctx: BodyCtx = { fn, mode, hideinert, selRow, folded: foldedSet, hidden };

  const section = (s: Section) => {
    const isCollapsed = !single && collapsed.includes(String(s.idx));
    const closable = single && view.bbs.length > 1;
    return (
      <div className="sec" key={s.idx}>
        <div className={single ? "hd" : "hd click"} onClick={single ? undefined : () => toggleCollapsed(String(s.idx))}>
          {!single && <span className="tw">{isCollapsed ? "▸" : "▾"}</span>}
          <span className="bb">{s.bb}</span>
          {(s.visit > 1 || (single && cfg.nodes.get(s.bb)!.secs.length > 1)) && <span className="hint">visit {s.visit}</span>}
          {closable && (
            <button className="bbclose" aria-label={`Close ${s.bb}`} title={`Close ${s.bb}`}
              onClick={() => go({ kind: "block", bbs: view.bbs.filter(b => b !== s.bb) })}>
              ×
            </button>
          )}
        </div>
        {!isCollapsed && <div className="bd">{renderBody(ctx, s)}</div>}
      </div>
    );
  };

  const solOpen = collapsed.includes("sol-open");
  return (
    <div id="view" ref={ref} {...hover}>
      {single && (
        <div className="nav">
          <a className="crumb" onClick={() => go({ kind: "graph", bbs: [] })}>{fn.id}</a>
          <span className="slash">/</span>
          {view.bbs.map((bb, i) => (
            <span key={bb} className="navbbs">
              {i > 0 && <span className="slash">+</span>}
              <span className="cur">{bb}</span>
            </span>
          ))}
          <span className="pill">{mode.name}</span>
        </div>
      )}
      {fn.solution && fn.solution.length > 0 && mode.name === "refine" && (
        <div className="sec">
          <div className="hd click" onClick={() => toggleCollapsed("sol-open")}>
            <span className="tw">{solOpen ? "▾" : "▸"}</span>
            <span className="bb">kvar solution</span>
            <span className="meta">{fn.solution.length} kvars · hover a kvar to see its solution</span>
          </div>
          {solOpen && (
            <div className="bd solution">
              {fn.solution.map(k => (
                <div key={k.name}>
                  <span className="kv">{k.name}</span>({(k.args || []).join(", ")}) := {k.body?.text ?? ""}
                </div>
              ))}
            </div>
          )}
        </div>
      )}
      {single ? (
        // one column per open block, each with all visits of that block
        <div className="cols" style={{ "--ncols": view.bbs.length } as React.CSSProperties}>
          {view.bbs.map(bb => (
            <div className="col" key={bb}>
              {mode.sections.filter(s => s.bb === bb).map(section)}
            </div>
          ))}
        </div>
      ) : (
        mode.sections.map(section)
      )}
    </div>
  );
}

interface BodyCtx {
  fn: Fn;
  mode: Mode;
  hideinert: boolean;
  selRow: string | null;
  folded: Set<string>;
  hidden: Set<string>;
}

interface Ctx {
  rcx?: string | null;
  env?: string | null;
}

/**
 * Prints the rcx/env lines between rows. Differences are highlighted only against an explicit
 * `base`: the state shown above the selected row.
 */
class Printer {
  out: ReactNode[] = [];
  /** the env line printed last: where it is (it may be outside the current edge group) and its env */
  lastEnv: { arr: ReactNode[]; idx: number; env: string } | null = null;
  lastRcx: string | null = null;
  constructor(private hidden: Set<string>) {}

  private shown = (key: string) => !this.hidden.has(key);
  push(node: ReactNode) {
    this.out.push(node);
  }
  get key() {
    return this.out.length;
  }

  context(c: Ctx | null | undefined, base: Ctx | null = null) {
    if (!c) return;
    this.rcxLine(c.rcx, base);
    this.envLine(c.env, base);
  }

  rcxLine(rcx: string | null | undefined, base: Ctx | null = null) {
    if (rcx == null) return;
    const old = base && base.rcx != null ? new Set(rcxFacts(base.rcx)) : null;
    const facts = rcxFacts(rcx).map((x, i) =>
      old && !old.has(x) ? <span key={i} className="new"><Rich text={x} /></span> : <Rich key={i} text={x} />,
    );
    this.lastRcx = rcx;
    this.push(<div key={this.key} className="ctx rcx">{"{"}{commaList(facts)}{"}"}</div>);
  }

  envLine(env: string | null | undefined, base: Ctx | null = null) {
    if (env == null) return;
    const cur = envBindings(env).filter(b => this.shown(b.key));
    const oldMap = base && base.env != null
      ? new Map(envBindings(base.env).filter(b => this.shown(b.key)).map(b => [b.key, b.text]))
      : null;
    // Removed bindings are not listed here; `preLine` marks them on the line above instead.
    const parts = cur.map(b => {
      const st = !oldMap ? "" : !oldMap.has(b.key) ? "add" : oldMap.get(b.key) !== b.text ? "chg" : "";
      return <BindingView key={b.key} b={b} cls={st} />;
    });
    this.lastEnv = { arr: this.out, idx: this.out.length, env };
    this.push(<div key={this.key} className="ctx env">{"{"}{commaList(parts)}{"}"}</div>);
  }

  /**
   * Marks, on the env line printed last (the closest visible state above the selected row), the
   * bindings the row changes (yellow) or removes (red).
   */
  preLine(postEnv: string | null | undefined) {
    if (!this.lastEnv) return;
    const post = new Map(envBindings(postEnv ?? "").map(b => [b.key, b.text]));
    const parts = envBindings(this.lastEnv.env).filter(b => this.shown(b.key)).map(b => {
      const st = postEnv == null ? "" : !post.has(b.key) ? "gone" : post.get(b.key) !== b.text ? "chg" : "";
      return <BindingView key={b.key} b={b} cls={st} />;
    });
    const { arr, idx } = this.lastEnv;
    arr[idx] = <div key={idx} className="ctx env">{"{"}{commaList(parts)}{"}"}</div>;
  }
}

const foldKey = (c: BodyCtx, id: string) => `${c.fn.id}|${c.mode.name}|${id}`;

function renderBody(c: BodyCtx, s: Section): ReactNode {
  const p = new Printer(c.hidden);
  // the block's entry state
  const first = s.items[0];
  const entry = s.startRaw || (first && first.t !== "sep" ? first.before : null);
  if (entry) p.context(entry);
  let pendingSep: Sep | null = null;
  // Items after an edge separator are grouped under it.
  let group: ReactNode[] | null = null;
  const outer = p.out;
  const closeGroup = () => {
    if (group) {
      outer.push(<div key={`g${outer.length}`} className="edgegrp">{group}</div>);
      group = null;
      p.out = outer;
    }
  };
  // Consecutive collapsed statements share one placeholder line; clicking it expands all of them.
  let foldRun: Item[] = [];
  const flushFolds = () => {
    if (!foldRun.length) return;
    const ids = foldRun.map(it => `${s.idx}:${it.i}`);
    const n = foldRun.length;
    p.push(
      <div key={p.key} className="row folded" title={foldRun.map(it => it.text).join("\n")}
        onClick={() => toggleFold(ids.map(id => foldKey(c, id)))}>
        <span className="tg" title={`Expand ${n === 1 ? "this statement" : `these ${n} statements`}`} />
        <span className="fl" />
      </div>,
    );
    foldRun = [];
  };
  for (const it of s.items as SecItem[]) {
    if (it.t === "sep") {
      pendingSep = it;
      continue;
    }
    if (c.hideinert && isInert(it)) continue;
    // an edge separator is printed only when a visible item follows it
    if (pendingSep) {
      flushFolds();
      closeGroup();
      const sep: Sep = pendingSep;
      const target = sep.target
        ? <span className="bblink" title={`Open ${sep.target}`} onClick={() => go({ kind: "block", bbs: [sep.target!] })}>{sep.target}</span>
        : "";
      outer.push(<div key={`e${outer.length}`} className="edge"><span>{edgeLabel(sep, target)}</span></div>);
      group = [];
      p.out = group;
      pendingSep = null;
    }
    if (c.folded.has(foldKey(c, `${s.idx}:${it.i}`))) {
      foldRun.push(it);
      continue;
    }
    flushFolds();
    renderItem(c, p, s, it);
  }
  flushFolds();
  closeGroup();
  return outer;
}

/** A row and the state after it. */
function renderItem(c: BodyCtx, p: Printer, s: Section, it: Item) {
  const id = `${s.idx}:${it.i}`;
  const selected = c.selRow === id;
  const cls = ["row"];
  if (isGhost(it)) cls.push("ghost");
  if (it.noend) cls.push("noend");
  if (selected) cls.push("sel");
  // A selected row is diffed against the closest visible state above it (not its own pre-state,
  // which may not be shown, e.g. after collapsed statements): captured before printing the row.
  const visiblePre = p.lastEnv ? { rcx: p.lastRcx, env: p.lastEnv.env } : null;
  const post = it.after || it.before;
  if (selected && it.t !== "goto" && post) p.preLine(post.env);
  p.push(
    <div key={p.key} className={cls.join(" ")} data-id={id}
      onClick={() => {
        if (getSelection()?.toString()) return; // allow copying text
        setSelRow(selected ? null : id);
      }}>
      <span className="tg" title="Collapse this statement and its environment"
        onClick={e => {
          e.stopPropagation();
          toggleFold([foldKey(c, id)]);
        }} />
      {isGhost(it) && (
        <span className="gl" title="Ghost statement: inserted by Flux, not part of the MIR">
          <svg viewBox="0 0 16 16" width="15" height="15" aria-label="ghost statement"><GhostIcon /></svg>
        </span>
      )}
      <span className="tx c-stmt"><Rich text={it.text} /></span>
      <span className="sp">{it.t === "stmt" ? it.span : ""}</span>
    </div>,
  );

  if (it.t === "goto") {
    const f = it.before!;
    if (c.mode.name === "refine") {
      p.context(f);
      p.push(<div key={p.key} className="ctx env"><span className="op">==&gt;</span> <BbEnv s={f.bb_env} hidden={c.hidden} /></div>);
    } else {
      p.push(<div key={p.key} className="ctx env"><BbEnv s={f.bb_env} hidden={c.hidden} /></div>);
      p.push(<div key={p.key} className="ctx env"><span className="op">⊓</span></div>);
      p.envLine(f.env);
      if (it.after) p.push(<div key={p.key} className="ctx env"><span className="op">=</span> <BbEnv s={it.after.bb_env} hidden={c.hidden} /></div>);
    }
    p.push(<div key={p.key} className="rule" />);
    return;
  }
  if (post) p.context(post, selected ? visiblePre : null);
  if (it.t === "term") p.push(<div key={p.key} className="rule" />);
}

/**
 * A goto's target env: `{_1: T, ...}` (shape) or `[bindings ...] $k ⇒ {_1: T, ...}` (refine). The
 * trailing binding group is filtered by the hidden locations; the prefix is printed as is.
 */
function BbEnv({ s, hidden }: { s: string | null | undefined; hidden: Set<string> }) {
  if (s == null) return null;
  s = s.trim();
  if (s.endsWith("}")) {
    for (let j = s.lastIndexOf("{"); j >= 0; j = s.lastIndexOf("{", j - 1)) {
      if (matchClose(s, j) === s.length - 1) {
        const parts = envBindings(s.slice(j)).filter(b => !hidden.has(b.key)).map(b => <BindingView key={b.key} b={b} />);
        return <><Rich text={s.slice(0, j)} />{"{"}{commaList(parts)}{"}"}</>;
      }
      if (j === 0) break;
    }
  }
  return <Rich text={s} />;
}
