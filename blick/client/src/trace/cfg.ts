// The control-flow graph of a mode, built from the terminators in the trace, and its layout.

import ELK, { type ElkNode } from "elkjs/lib/elk.bundled.js";
import type { Mode, Section } from "./model";
import { splitTop } from "./text";

export interface Succ {
  to: string;
  label: string;
  /** an imaginary edge (false edges of loops), drawn dashed */
  aux: boolean;
}

/** A block. Successors the checker never visited are nodes without sections. */
export interface CfgNode {
  bb: string;
  /** the visits of the block */
  secs: Section[];
  succs: Succ[];
  preds: string[];
}

export interface Cfg {
  nodes: Map<string, CfgNode>;
  root: string;
  /** back edges, as "a>b", found by a depth-first search from the root */
  back: Set<string>;
}

/** `goto -> bb4`, `switchInt(..) -> [0: bb1, otherwise: bb3]`, `_0 = f() -> [return: bb2, unwind continue]` */
export function parseSuccs(term: string): Succ[] {
  const i = term.lastIndexOf("->");
  if (i < 0) return [];
  const rest = term.slice(i + 2).trim();
  if (!rest.startsWith("[")) {
    const m = /bb\d+/.exec(rest);
    return m ? [{ to: m[0], label: "", aux: false }] : [];
  }
  const out: Succ[] = [];
  for (const part of splitTop(rest.slice(1, -1), ",")) {
    const m = /^\s*(?:([^:]+):\s*)?(bb\d+)\s*$/.exec(part);
    if (!m) continue;
    const label = (m[1] || "").trim();
    if (/^(unwind|cleanup)$/.test(label)) continue;
    out.push({ to: m[2], label: /^(real|return)$/.test(label) ? "" : label, aux: label === "imaginary" });
  }
  return out;
}

const cfgCache = new WeakMap<Mode, Cfg>();

export function buildCfg(mode: Mode): Cfg {
  const cached = cfgCache.get(mode);
  if (cached) return cached;
  const nodes = new Map<string, CfgNode>();
  const node = (bb: string) => {
    let n = nodes.get(bb);
    if (!n) {
      n = { bb, secs: [], succs: [], preds: [] };
      nodes.set(bb, n);
    }
    return n;
  };
  for (const s of mode.sections) node(s.bb).secs.push(s);
  for (const n of nodes.values()) {
    const s = n.secs[0];
    if (s.kind === "entry") n.succs = nodes.has("bb0") ? [{ to: "bb0", label: "", aux: false }] : [];
    else if (s.term) n.succs = parseSuccs(s.term.text);
  }
  for (const n of [...nodes.values()]) for (const e of n.succs) node(e.to).preds.push(n.bb);
  const root = nodes.has("entry") ? "entry" : "bb0";

  const state = new Map<string, number>();
  const back = new Set<string>();
  const dfs = (bb: string) => {
    state.set(bb, 1);
    for (const e of nodes.get(bb)!.succs) {
      const st = state.get(e.to);
      if (st === 1) back.add(bb + ">" + e.to);
      else if (!st) dfs(e.to);
    }
    state.set(bb, 2);
  };
  if (nodes.has(root)) dfs(root);
  for (const bb of [...nodes.keys()].sort(bbCmp)) if (!state.has(bb)) dfs(bb);

  const cfg = { nodes, root, back };
  cfgCache.set(mode, cfg);
  return cfg;
}

export function bbCmp(a: string, b: string): number {
  const num = (s: string) => +(s.match(/\d+/) || [-1])[0];
  return num(a) - num(b);
}

const elk = new ELK();

export type Positions = Map<string, { x: number; y: number }>;

/**
 * A layered layout, top to bottom, with ELK. `sizes` are the nodes' measured sizes. Back edges
 * are left out, so loops do not disturb the layering: the loop head stays above its body.
 */
export async function layoutCfg(cfg: Cfg, sizes: Map<string, { width: number; height: number }>): Promise<Positions> {
  // Nodes and edges in control-flow order, which ELK keeps where it can (`considerModelOrder`).
  const order = [...cfg.nodes.keys()].sort((a, b) => (a === cfg.root ? -1 : b === cfg.root ? 1 : bbCmp(a, b)));
  const graph: ElkNode = {
    id: "root",
    layoutOptions: {
      "elk.algorithm": "layered",
      "elk.direction": "DOWN",
      "elk.spacing.nodeNode": "36",
      "elk.layered.spacing.nodeNodeBetweenLayers": "54",
      "elk.layered.nodePlacement.strategy": "BRANDES_KOEPF",
      "elk.layered.considerModelOrder.strategy": "NODES_AND_EDGES",
      "elk.padding": "[top=20,left=20,bottom=20,right=20]",
    },
    children: order.map(bb => ({ id: bb, width: sizes.get(bb)?.width ?? 120, height: sizes.get(bb)?.height ?? 40 })),
    edges: order.flatMap(bb =>
      cfg.nodes.get(bb)!.succs
        .filter(e => cfg.nodes.has(e.to) && !cfg.back.has(bb + ">" + e.to))
        .map((e, k) => ({ id: `${bb}>${e.to}#${k}`, sources: [bb], targets: [e.to] })),
    ),
  };
  const out = await elk.layout(graph);
  const pos: Positions = new Map();
  for (const c of out.children ?? []) pos.set(c.id, { x: c.x ?? 0, y: c.y ?? 0 });
  return pos;
}
