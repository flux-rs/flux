// Rendering the checker's printed text: lifetimes and local names, kvars, types with their
// fields as hoverable places, and pointers.

import { createContext, useContext, type ReactNode } from "react";
import type { Fn } from "../trace/model";
import { type Binding, findTopOpen, matchClose, splitTop, topIndexOf } from "../trace/text";

export interface TextOpts {
  fn: Fn;
  hidelt: boolean;
  localnames: boolean;
}

export const TextCtx = createContext<TextOpts | null>(null);
const useOpts = () => useContext(TextCtx)!;

// With "Hide lifetimes" on, region variables and lifetimes are dropped:
//   `&'?3 mut T` -> `&mut T`, `ptr(mut['?7], s)` -> `ptr(mut, s)`, `Foo<'a, T>` -> `Foo<T>`.
// A lifetime is `'?N` or `'ident` not followed by another `'` (that would be a char literal).
const LT = String.raw`'(?:\?\d+|[A-Za-z_]\w*)(?![\w'])`;
const LT_RES: [RegExp, string][] = [
  [new RegExp(String.raw`&${LT}\s*`, "g"), "&"],
  [new RegExp(String.raw`\[\s*${LT}\s*\]`, "g"), ""],
  [new RegExp(String.raw`<\s*${LT}\s*>`, "g"), ""],
  [new RegExp(String.raw`${LT}\s*,\s*`, "g"), ""],
  [new RegExp(String.raw`,\s*${LT}(?=\s*>)`, "g"), ""],
];

/** Text as displayed. */
export function shown(s: string, o: TextOpts): string {
  if (o.hidelt) for (const [re, by] of LT_RES) s = s.replace(re, by);
  return withNames(s, o);
}

// "Show names": a local `_N` is shown by its source name. A name shared by several locals of the
// function (shadowing) is ambiguous: in text the local stays `_N`, as a binding key it is `x (_5)`.
const sharedCache = new WeakMap<Fn, Set<string>>();
function isShared(fn: Fn, name: string): boolean {
  let shared = sharedCache.get(fn);
  if (!shared) {
    const seen = new Set<string>();
    shared = new Set();
    for (const n of fn.names.values()) (seen.has(n) ? shared : seen).add(n);
    sharedCache.set(fn, shared);
  }
  return shared.has(name);
}
const localName = (local: string, o: TextOpts) => (o.localnames ? o.fn.names.get(local) : undefined);

export function withNames(s: string, o: TextOpts): string {
  if (!o.localnames || !o.fn.names.size) return s;
  return s.replace(/(?<![\w$])_\d+(?![\w$])/g, l => {
    const n = localName(l, o);
    return n && !isShared(o.fn, n) ? n : l;
  });
}

export function Local({ local }: { local: string }) {
  const o = useOpts();
  const n = localName(local, o);
  if (!n) return <>{local}</>;
  return (
    <>
      <span className="lvar" title={local}>{n}</span>
      {isShared(o.fn, n) && <> <span className="lname">({local})</span></>}
    </>
  );
}

/** Text with kvars ($k3) decorated with their solution and blocked markers (†). */
export function Rich({ text }: { text: string | null | undefined }) {
  const o = useOpts();
  if (text == null) return null;
  return <>{decorate(shown(text, o), o)}</>;
}

function decorate(s: string, o: TextOpts): ReactNode[] {
  const out: ReactNode[] = [];
  let last = 0;
  for (const m of s.matchAll(/\$k\d+|†/g)) {
    if (m.index > last) out.push(s.slice(last, m.index));
    const t = m[0];
    if (t === "†") out.push(<span key={m.index} className="blk">†</span>);
    else {
      const sol = o.fn.solution?.find(k => k.name === t);
      const title = sol ? `${t}(${(sol.args || []).join(", ")}) := ${sol.body?.text ?? ""}` : "";
      out.push(<span key={m.index} className="kv" title={title}>{t}</span>);
    }
    last = m.index + t.length;
  }
  if (last < s.length) out.push(s.slice(last));
  return out;
}

/** A place (`.hv`) that can be highlighted on its own when a pointer to it is hovered. */
function Place({ path, cls, children }: { path: string | null; cls?: string; children: ReactNode }) {
  return (
    <span className={cls ? `hv ${cls}` : "hv"} data-path={path ?? undefined}>
      {children}
    </span>
  );
}

/**
 * A binding's type with every struct field, tuple element and variant field wrapped in a place,
 * so a nested place can be highlighted on its own when a pointer to it is hovered:
 *   `Foo { foo: T, bar: U }`, `(T, U)`, `F::A(T)`.
 * Each place carries the path it stands for (`data-path`), in Flux's path syntax: the binding's
 * name followed by field indices (`s.1`, `_1.0.2`). Fields print in definition order, so the i-th
 * field is `.i`; a variant's fields are numbered the same way, as paths do not record the variant.
 * Other types are rendered as text, with pointers marked (see `PtrText`).
 */
export function Ty({ t, path = null }: { t: string; path?: string | null }) {
  const sub = (i: number) => (path === null ? null : `${path}.${i}`);
  t = t.trim();
  // struct: `Name { f: T, ... }` with the brace group at top level and closing at the end
  const ob = findTopOpen(t, "{");
  if (ob > 0 && matchClose(t, ob) === t.length - 1) {
    const parts = splitTop(t.slice(ob + 1, -1), ",").map(x => x.trim()).filter(Boolean);
    const fields = parts.map(p => {
      const i = topIndexOf(p, ":");
      return i > 0 && /^[A-Za-z_]\w*$/.test(p.slice(0, i).trim()) ? { name: p.slice(0, i).trim(), ty: p.slice(i + 1) } : null;
    });
    if (parts.length && fields.every(f => f !== null)) {
      return (
        <>
          <Rich text={t.slice(0, ob).trimEnd()} />
          {" { "}
          {fields.map((f, i) => (
            <span key={i}>
              {i > 0 && ", "}
              <Place path={sub(i)}>
                {f.name}: <Ty t={f.ty} path={sub(i)} />
              </Place>
            </span>
          ))}
          {" }"}
        </>
      );
    }
  }
  // tuple `(T, U)` or enum variant `Path::Variant(T, ...)`
  const op = findTopOpen(t, "(");
  const prefix = op >= 0 ? t.slice(0, op) : "";
  if (op >= 0 && matchClose(t, op) === t.length - 1 && (prefix === "" || /^[\w:]+::\w+$/.test(prefix))) {
    const elems = splitTop(t.slice(op + 1, -1), ",").map(x => x.trim()).filter(Boolean);
    if (elems.length) {
      return (
        <>
          {prefix}(
          {elems.map((e, i) => (
            <span key={i}>
              {i > 0 && ", "}
              <Place path={sub(i)}>
                <Ty t={e} path={sub(i)} />
              </Place>
            </span>
          ))}
          )
        </>
      );
    }
  }
  return <PtrText t={t} />;
}

// Every `ptr(<kind>, <path>)` is wrapped in a span naming the place it points to, so hovering it
// can highlight that place (see `usePtrHover`).
const PTR_RE = /ptr\(([^()]*?),\s*([A-Za-z_$][\w$]*(?:\.\d+)*)\)/g;
function PtrText({ t }: { t: string }) {
  const o = useOpts();
  const out: ReactNode[] = [];
  let last = 0;
  for (const m of t.matchAll(PTR_RE)) {
    // the path is the last thing before the closing `)`; it gets its own span to mark it on hover
    const head = m[0].slice(0, m[0].length - m[2].length - 1);
    out.push(<Rich key={`t${m.index}`} text={t.slice(last, m.index)} />);
    out.push(
      <span key={`p${m.index}`} className="ptr" data-target={m[2]}>
        <Rich text={head} />
        <span className="ppath">{withNames(m[2], o)}</span>)
      </span>,
    );
    last = m.index + m[0].length;
  }
  out.push(<Rich key="end" text={t.slice(last)} />);
  return <>{out}</>;
}

export function BindingView({ b, cls }: { b: Binding; cls?: string }) {
  return (
    <Place path={b.key} cls={cls}>
      <Local local={b.key} />: <Ty t={b.text} path={b.key} />
    </Place>
  );
}

/** Joins nodes with ", ". */
export function commaList(nodes: ReactNode[]): ReactNode[] {
  return nodes.flatMap((n, i) => (i === 0 ? [n] : [", ", n]));
}

/**
 * Hovering a pointer's path (`a0` in `ptr(mut, a0)`) highlights the place it points to in the same
 * environment line, with an arrow to it; hovering a place does the same for every pointer to it. A
 * pointer whose exact place is not there (it is hidden, or gone) points to the closest enclosing
 * place, marked as partial. Done on the DOM: it is a transient hover effect over many small spans.
 */
export function ptrHoverHandlers() {
  let hovered: Element | null = null; // the hovered pointer or place
  let undo: (() => void)[] = [];
  const clear = () => {
    for (const u of undo) u();
    undo = [];
  };
  const show = (line: Element, links: [Element, Target][]) => {
    for (const [ptr, t] of links) {
      ptr.classList.add("active");
      const arrow = drawArrow(line, ptr.querySelector(".ppath") ?? ptr, t.el, !t.exact);
      undo.push(() => {
        ptr.classList.remove("active");
        arrow.remove();
      });
    }
    // a target is partial only if no pointer to it is exact
    for (const el of new Set(links.map(([, t]) => t.el))) {
      el.classList.add("ptarget");
      if (!links.some(([, t]) => t.el === el && t.exact)) el.classList.add("partial");
      undo.push(() => el.classList.remove("ptarget", "partial"));
    }
  };
  const onMouseOver = (e: React.MouseEvent) => {
    const at = e.target as Element;
    const line = at.closest?.(".ctx");
    // a pointer's path (`a0` in `ptr(mut, a0)`), or else the innermost place under the mouse that
    // some pointer points to
    let next: Element | null = null, links: [Element, Target][] = [];
    const ptr = line && at.closest(".ctx .ptr .ppath")?.closest(".ptr");
    if (ptr) {
      const t = ptrTarget(line, ptr);
      next = ptr;
      links = t ? [[ptr, t]] : [];
    } else if (line) {
      const ptrs = [...line.querySelectorAll(".ptr")].map(p => [p, ptrTarget(line, p)] as const);
      for (let el = at.closest(".hv"); el && line.contains(el); el = el.parentElement?.closest(".hv") ?? null) {
        links = ptrs.filter((x): x is [Element, Target] => x[1]?.el === el);
        if (links.length) {
          next = el;
          break;
        }
      }
    }
    if (next === hovered) return;
    clear();
    hovered = next;
    if (line) show(line, links);
  };
  return {
    onMouseOver,
    onMouseLeave: () => {
      clear();
      hovered = null;
    },
  };
}

interface Target {
  el: Element;
  /** false: the pointer's exact place is not there, `el` is the closest enclosing one */
  exact: boolean;
}

/** The place in `line` that pointer `ptr` points to. */
function ptrTarget(line: Element, ptr: Element): Target | null {
  let path = (ptr as HTMLElement).dataset.target ?? "", exact = true;
  while (path) {
    const el = line.querySelector(`.hv[data-path="${CSS.escape(path)}"]`);
    if (el) return { el, exact };
    const dot = path.lastIndexOf(".");
    path = dot < 0 ? "" : path.slice(0, dot);
    exact = false;
  }
  return null;
}

const SVG = "http://www.w3.org/2000/svg";

/**
 * A dashed arrow, in `line`, from the pointer `from` to its target `to`: a curve arcing above the
 * text from the middle of the pointer's path to the start of the target (the target may be a whole
 * binding; its start is where its name is). Dashed more sparsely when the target is only partial.
 * An element wrapped over several rows has a box per row: the first one is where it starts.
 */
function drawArrow(line: Element, from: Element, to: Element, partial: boolean): SVGSVGElement {
  const first = (e: Element) => e.getClientRects()[0] ?? e.getBoundingClientRect();
  const l = line.getBoundingClientRect(), a = first(from), b = first(to);
  const x1 = a.left + a.width / 2 - l.left, y1 = a.top - l.top - 2;
  const x2 = b.left + Math.min(b.width / 2, 14) - l.left, y2 = b.top - l.top - 3;
  const lift = Math.min(28, Math.max(12, Math.abs(x2 - x1) * 0.2));
  const cy = Math.min(y1, y2) - lift;
  // control points pulled in from the ends, so the curve (and the head, which follows it) leaves
  // and arrives at an angle, not vertically
  const dx = (x2 - x1) * 0.12;
  // The line stops where the head starts, and the head, anchored at its base, ends at the target:
  // the end moves back by the head's length along the curve's final direction (from the last
  // control point). The head is 5 stroke widths long (`markerWidth`), at the 1.5px of style.css.
  const HEAD = 5 * 1.5;
  const ux = dx, uy = y2 - cy, n = Math.hypot(ux, uy) || 1;
  const ex = x2 - (HEAD * ux) / n, ey = y2 - (HEAD * uy) / n;
  const svg = document.createElementNS(SVG, "svg");
  svg.setAttribute("class", "parrow");
  svg.innerHTML = `
    <defs><marker id="parrow-head" viewBox="0 0 8 8" refX="0" refY="4" markerWidth="5" markerHeight="5" orient="auto-start-reverse">
      <path d="M0,0 L8,4 L0,8 z" /></marker></defs>
    <path d="M${x1},${y1} C${x1 + dx},${cy} ${x2 - dx},${cy} ${ex},${ey}" stroke-dasharray="${partial ? "2 4" : "4 3"}" marker-end="url(#parrow-head)" />`;
  line.appendChild(svg);
  return svg;
}
