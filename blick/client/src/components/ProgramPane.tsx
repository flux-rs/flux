// The program pane: the run bar, the editor, and the output of the last run (build output and
// diagnostics) in resizable, collapsible panels.

import { useEffect, useLayoutEffect, useRef, useState } from "react";
import { Group, Panel, type PanelImperativeHandle, Separator, useDefaultLayout, usePanelRef } from "react-resizable-panels";
import { curProgram, curRun, resolveView, runFlux, setFlags, useStore } from "../store";
import { Editor, type LineRange } from "./Editor";
import { MOD } from "./icons";

/** height of a collapsed output panel: its header */
const HDR = 29;

export function ProgramPane() {
  const prog = useStore(curProgram);
  const run = useStore(curRun);
  const running = useStore(s => s.running);
  const serverInfo = useStore(s => s.serverInfo);
  const selRow = useStore(s => s.selRow);
  const buildRef = usePanelRef();
  const diagRef = usePanelRef();
  const layout = useDefaultLayout({ id: "blick:output", storage: localStorage });

  // The source lines of the selected statement, if it has a span in the program (spans into other
  // files, e.g. the standard library, are not shown).
  let mark: LineRange | null = null;
  const tv = resolveView(run.data, prog.view);
  if (tv && selRow) {
    const [si, ii] = selRow.split(":").map(Number);
    const it = tv.mode.sections.find(s => s.idx === si)?.items.find(it => it.i === ii);
    const loc = it && it.t === "stmt" ? it.loc : null;
    if (loc && (!loc.file || /(^|[/\\])input\.rs$/.test(loc.file))) {
      mark = { start: loc.start_line, end: Math.max(loc.start_line, loc.end_line) };
    }
  }

  // Switching tabs shows the diagnostics if the last run had errors.
  useEffect(() => {
    const p = diagRef.current;
    if (run.diagErr) p?.expand();
    else p?.collapse();
  }, [prog.id]);
  // A run shows its output while it goes, and its diagnostics when it failed.
  const lastStatus = useRef(run.status);
  useEffect(() => {
    if (run.status === lastStatus.current) return;
    lastStatus.current = run.status;
    if (run.status === "running") buildRef.current?.expand();
    else if (run.diagErr) diagRef.current?.expand();
  }, [run.status, prog.id]);

  const status = run.statusText || serverInfo;
  const statusCls = run.statusText ? (run.statusErr ? "err" : /^ok\b/.test(status) ? "ok" : "") : "";
  return (
    <div id="prog">
      <div className="srcbar">
        <button className="primary" title={`Run Flux on this program (${MOD}+Enter)`} disabled={running} onClick={runFlux}>
          Run Flux
        </button>
        <input type="text" id="flags" placeholder="extra flags, e.g. -Fcheck-overflow=strict" spellCheck={false}
          value={prog.flags} onChange={e => setFlags(e.target.value)} onKeyDown={e => e.key === "Enter" && runFlux()} />
        <span id="runstatus" className={statusCls} title={status}>{status}</span>
      </div>
      <Group orientation="vertical" id="blick:output" {...layout} className="outgroup">
        <Panel id="editor" minSize={120}>
          <Editor progId={prog.id} source={prog.source} mark={mark} markFor={selRow} />
        </Panel>
        <Separator className="vsplit" />
        <OutputPanel id="build" panelRef={buildRef} title={<>Build output {run.buildLog.length > 0 && <span id="buildcount">({run.buildLog.length} lines)</span>}</>}>
          <BuildLog lines={run.buildLog} />
        </OutputPanel>
        <Separator className="vsplit" />
        <OutputPanel id="diag" panelRef={diagRef} title="Diagnostics" err={run.diagErr}>
          <pre>{run.diag}</pre>
        </OutputPanel>
      </Group>
    </div>
  );
}

function OutputPanel({ id, panelRef, title, err, children }: {
  id: string;
  panelRef: React.RefObject<PanelImperativeHandle | null>;
  title: React.ReactNode;
  err?: boolean;
  children: React.ReactNode;
}) {
  const [open, setOpen] = useState(false);
  return (
    <Panel id={id} panelRef={panelRef} collapsible collapsedSize={HDR} minSize={HDR + 50} defaultSize={HDR}
      onResize={size => setOpen(size.inPixels > HDR + 1)}>
      <div className={`outpanel${err ? " has-err" : ""}${open ? " open" : ""}`}>
        <button className="summary" aria-expanded={open}
          onClick={() => (panelRef.current?.isCollapsed() ? panelRef.current.expand() : panelRef.current?.collapse())}>
          {title}
        </button>
        {open && children}
      </div>
    </Panel>
  );
}

/** The live output of `cargo x run`, following its end unless the user scrolled up to read. */
function BuildLog({ lines }: { lines: string[] }) {
  const ref = useRef<HTMLPreElement>(null);
  const atEnd = useRef(true);
  useLayoutEffect(() => {
    const pre = ref.current;
    if (pre && atEnd.current) pre.scrollTop = pre.scrollHeight;
  }, [lines]);
  return (
    <pre ref={ref} className="buildtext"
      onScroll={e => {
        const p = e.currentTarget;
        atEnd.current = p.scrollTop + p.clientHeight >= p.scrollHeight - 4;
      }}>
      {lines.join("\n")}
    </pre>
  );
}
