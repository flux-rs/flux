// The control-flow graph of a mode: blocks with their statements (no environments), laid out by
// ELK, drawn and made interactive (pan, zoom, drag, select) by React Flow.

import {
  ControlButton, Controls, type Edge, Handle, MarkerType, type Node, type NodeProps, Panel, Position, ReactFlow,
  ReactFlowProvider, useNodesInitialized, useNodesState, useReactFlow, type Viewport,
} from "@xyflow/react";
import { memo, useContext, useEffect, useMemo, useState } from "react";
import { useHotkeys } from "react-hotkeys-hook";
import { go } from "../store";
import { buildCfg, type Cfg, type CfgNode, layoutCfg, type Positions } from "../trace/cfg";
import { type Fn, type Item, isGhost, isInert, type Mode, type Sep } from "../trace/model";
import { GhostIcon, MOD } from "./icons";
import { shown, TextCtx } from "./text";

const MAX_CHARS = 64;

type BlockData = {
  bb: string;
  sub: string;
  visited: boolean;
  /** the block's own statements and terminator */
  body: Item[];
  /** the statements checked on each outgoing edge (only edges with visible statements) */
  edges: { label: string; lines: Item[] }[];
  hasGhost: boolean;
  /** number of out-edges, each with its own handle along the bottom */
  nOut: number;
};
type BlockNode = Node<BlockData, "block">;

// Per mode, kept while the page lives: the automatic layout (per display options, since they
// change the node sizes), the positions of the nodes the user dragged, and the viewport.
const layouts = new WeakMap<Mode, Map<string, Positions>>();
const drags = new WeakMap<Mode, Map<string, { x: number; y: number }>>();
const viewports = new WeakMap<Mode, Viewport>();
const dragsOf = (mode: Mode) => {
  let d = drags.get(mode);
  if (!d) drags.set(mode, (d = new Map()));
  return d;
};

interface Props {
  fn: Fn;
  mode: Mode;
  hideinert: boolean;
  hidelt: boolean;
  localnames: boolean;
}

export function GraphView(props: Props) {
  const { fn, mode, hideinert, hidelt, localnames } = props;
  const cfg = buildCfg(mode);
  const optsKey = `${hideinert}|${hidelt}|${localnames}`;
  return (
    <div id="view" className="graphview">
      <div className="nav">
        <span className="cur">{fn.id}</span>
        <span className="pill">{mode.name}</span>
        <span className="dim">{cfg.nodes.size} blocks</span>
        <span className="hint">
          Double-click a block to open it. Click to select, {MOD}+click to add or remove, {MOD}+A for all, then open them
          side by side. Esc or a click on empty space clears. Drag to move.
        </span>
      </div>
      {/* Remounted when the node sizes may change, so the nodes are measured and laid out again. */}
      <ReactFlowProvider key={`${fn.id}|${mode.name}|${optsKey}`}>
        <Graph {...props} cfg={cfg} optsKey={optsKey} />
      </ReactFlowProvider>
    </div>
  );
}

function nodeContent(n: CfgNode, hideinert: boolean): Omit<BlockData, "nOut"> {
  const sub = !n.secs.length ? "(not visited)"
    : n.bb === "entry" ? "(FunEntry ghost statements)"
    : n.secs.length > 1 ? `×${n.secs.length} visits` : "";
  const out: Omit<BlockData, "nOut"> = { bb: n.bb, sub, visited: n.secs.length > 0, body: [], edges: [], hasGhost: false };
  const s = n.secs[0];
  if (!s) return out;
  let edge: BlockData["edges"][number] | null = null;
  for (const it of s.items) {
    if (it.t === "sep") {
      edge = { label: edgeLabelText(it.how, it.target), lines: [] };
      out.edges.push(edge);
    } else if (it.t !== "goto" && !(hideinert && isInert(it))) {
      (edge ? edge.lines : out.body).push(it);
    }
  }
  out.edges = out.edges.filter(e => e.lines.length);
  out.hasGhost = [...out.body, ...out.edges.flatMap(e => e.lines)].some(isGhost);
  return out;
}

const edgeLabelText = (how: Sep["how"], target: string | null) =>
  how === "goto" ? `edge to ${target} (join point)`
  : how === "enter" ? `edge to ${target}`
  : "edge to exit block (inlined) or unknown";

function Graph({ mode, hideinert, cfg, optsKey }: Props & { cfg: Cfg; optsKey: string }) {
  const { fitView, setViewport } = useReactFlow();
  const cached = layouts.get(mode)?.get(optsKey);
  const drag = dragsOf(mode);

  const initial = useMemo(() => {
    const nodes: BlockNode[] = [];
    const edges: Edge[] = [];
    for (const n of cfg.nodes.values()) {
      const outs = n.succs.filter(e => cfg.nodes.has(e.to));
      const data = { ...nodeContent(n, hideinert), nOut: outs.length };
      nodes.push({
        id: n.bb, type: "block", data, position: drag.get(n.bb) ?? cached?.get(n.bb) ?? { x: 0, y: 0 },
        selectable: data.visited, connectable: false,
        // not shown until laid out
        style: cached ? undefined : { visibility: "hidden" },
      });
      outs.forEach((e, k) => {
        const back = cfg.back.has(n.bb + ">" + e.to);
        edges.push({
          id: `${n.bb}>${e.to}#${k}`, source: n.bb, target: e.to,
          sourceHandle: back ? "bout" : `out${k}`, targetHandle: back ? "bin" : "in",
          label: e.label || undefined,
          className: ["e", e.aux ? "aux" : "", back ? "back" : ""].join(" "),
          markerEnd: { type: MarkerType.ArrowClosed, width: 14, height: 14, color: back ? "var(--goto)" : "var(--edge)" },
          selectable: false, focusable: false,
        });
      });
    }
    return { nodes, edges };
  }, [cfg, hideinert]);

  const [nodes, setNodes, onNodesChange] = useNodesState<BlockNode>(initial.nodes);
  const [ready, setReady] = useState(!!cached);
  const initialized = useNodesInitialized();

  // Lays the nodes out once React Flow has measured them.
  useEffect(() => {
    if (ready || !initialized) return;
    const sizes = new Map(nodes.map(n => [n.id, { width: n.measured?.width ?? 0, height: n.measured?.height ?? 0 }]));
    let cancelled = false;
    layoutCfg(cfg, sizes).then(pos => {
      if (cancelled) return;
      if (!layouts.has(mode)) layouts.set(mode, new Map());
      layouts.get(mode)!.set(optsKey, pos);
      setNodes(ns => ns.map(n => ({ ...n, position: drag.get(n.id) ?? pos.get(n.id) ?? n.position, style: undefined })));
      setReady(true);
      const vp = viewports.get(mode);
      requestAnimationFrame(() => (vp ? setViewport(vp) : fitView({ maxZoom: 1, padding: 0.05 })));
    });
    return () => {
      cancelled = true;
    };
  }, [initialized, ready]);

  const selected = nodes.filter(n => n.selected).map(n => n.id);
  const select = (pred: (n: BlockNode) => boolean) => setNodes(ns => ns.map(n => ({ ...n, selected: pred(n) })));

  // Opens the selected blocks side by side, in control-flow order: by their place in the automatic
  // layout (top to bottom, then left to right), whatever order they were selected in.
  const openSelection = () => {
    const pos = layouts.get(mode)?.get(optsKey);
    const bbs = [...selected];
    if (!bbs.length) return;
    if (pos) bbs.sort((a, b) => pos.get(a)!.y - pos.get(b)!.y || pos.get(a)!.x - pos.get(b)!.x);
    go({ kind: "block", bbs });
  };

  // select every block the checker visited
  useHotkeys("mod+a", () => select(n => n.data.visited), { preventDefault: true });
  useHotkeys("escape", () => select(() => false));
  useHotkeys("enter", openSelection, { preventDefault: true }, [selected.join(",")]);

  const resetLayout = () => {
    drag.clear();
    const pos = layouts.get(mode)?.get(optsKey);
    if (pos) setNodes(ns => ns.map(n => ({ ...n, position: pos.get(n.id) ?? n.position })));
  };

  const initialViewport = viewports.get(mode);
  return (
    <ReactFlow<BlockNode>
      nodes={nodes}
      edges={ready ? initial.edges : []}
      onNodesChange={onNodesChange}
      nodeTypes={nodeTypes}
      onNodeDoubleClick={(_, n) => n.data.visited && go({ kind: "block", bbs: [n.id] })}
      onNodeDragStop={(_, __, moved) => moved.forEach(n => drag.set(n.id, n.position))}
      onMoveEnd={(_, vp) => viewports.set(mode, vp)}
      defaultViewport={initialViewport}
      nodesConnectable={false}
      edgesFocusable={false}
      deleteKeyCode={null}
      zoomOnDoubleClick={false}
      minZoom={0.1}
      maxZoom={3}
    >
      <Controls showInteractive={false} position="top-right">
        <ControlButton onClick={resetLayout} title="Undo node moves" aria-label="Undo node moves">↺</ControlButton>
      </Controls>
      {selected.length > 0 && (
        <Panel position="bottom-left">
          <div className="selbar" role="toolbar" aria-label="Selected blocks">
            <span className="selcount">{selected.length} selected</span>
            <button className="primary" title="Open the selected blocks side by side (Enter)" onClick={openSelection}>
              Open {selected.length === 1 ? "block" : `${selected.length} blocks`}
            </button>
            <button title="Clear the selection (Esc)" onClick={() => select(() => false)}>Clear</button>
          </div>
        </Panel>
      )}
    </ReactFlow>
  );
}

const BlockNodeView = memo(function BlockNodeView({ data, selected }: NodeProps<BlockNode>) {
  const o = useContext(TextCtx)!;
  const line = (it: Item, key: number) => {
    const s = shown(it.text, o);
    const long = s.length > MAX_CHARS;
    return (
      <div key={key} className="gline" title={long ? s : undefined}>
        {data.hasGhost && (
          <span className="gicon">{isGhost(it) && <svg viewBox="0 0 16 16" width="13" height="13"><GhostIcon /></svg>}</span>
        )}
        <span className="c-stmt">{long ? s.slice(0, MAX_CHARS - 1) + "…" : s}</span>
      </div>
    );
  };
  const title = data.visited
    ? `${data.bb}: click to select, ${MOD}+click to add or remove, double-click to open, drag to move`
    : `${data.bb}: not visited by the checker (inlined exit block or unreachable)`;
  return (
    <div className={["gnode", data.visited ? "" : "ghost", selected ? "selected" : ""].join(" ")} title={title}>
      <Handle type="target" position={Position.Top} id="in" isConnectable={false} />
      <Handle type="target" position={Position.Right} id="bin" isConnectable={false} style={{ top: 14 }} />
      <div className="ghd">
        <span className="title">{data.bb}</span>
        {data.sub && <span className="sub">{data.sub}</span>}
      </div>
      {data.body.length > 0 && <div className="glines">{data.body.map(line)}</div>}
      {data.edges.map((e, i) => (
        <div key={i} className="gedge">
          <div className="ehdr">{e.label}</div>
          <div className="glines">{e.lines.map(line)}</div>
        </div>
      ))}
      {Array.from({ length: data.nOut }, (_, k) => (
        <Handle key={k} type="source" position={Position.Bottom} id={`out${k}`} isConnectable={false}
          style={{ left: `${((k + 1) / (data.nOut + 1)) * 100}%` }} />
      ))}
      <Handle type="source" position={Position.Right} id="bout" isConnectable={false} />
    </div>
  );
});

const nodeTypes = { block: BlockNodeView };
