// The program pane: the run bar, the editor, and the output of the last run (the output of
// `cargo x run`) in a resizable, collapsible panel.

import { useEffect, useLayoutEffect, useRef, useState } from "react";
import { Group, Panel, type PanelImperativeHandle, Separator, useDefaultLayout, usePanelRef } from "react-resizable-panels";
import { curProgram, curRun, EDITOR_FONT_SIZE, resolveView, runFlux, setFlags, setUi, useStore, zoomEditor } from "../store";
import { AnsiPre } from "./Ansi";
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
  const hoverRow = useStore(s => s.hoverRow);
  const vimOn = useStore(s => s.ui.vim);
  const fontSize = useStore(s => s.ui.editorFontSize);
  const buildRef = usePanelRef();
  const layout = useDefaultLayout({ id: "blick:output", storage: localStorage });

  // The source lines of the hovered statement, or else of the selected one, if it has a span in the
  // program (spans into other files, e.g. the standard library, are not shown).
  let mark: LineRange | null = null;
  const markRow = hoverRow ?? selRow;
  const tv = resolveView(run.data, prog.view);
  if (tv && markRow) {
    const [si, ii] = markRow.split(":").map(Number);
    const it = tv.mode.sections.find(s => s.idx === si)?.items.find(it => it.i === ii);
    const loc = it && it.t === "stmt" ? it.loc : null;
    if (loc && (!loc.file || /(^|[/\\])input\.rs$/.test(loc.file))) {
      mark = { start: loc.start_line, end: Math.max(loc.start_line, loc.end_line) };
    }
  }

  // A run shows its output while it goes.
  const lastStatus = useRef(run.status);
  useEffect(() => {
    if (run.status === lastStatus.current) return;
    lastStatus.current = run.status;
    if (run.status === "running") buildRef.current?.expand();
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
          <div className="edwrap">
            <Editor progId={prog.id} source={prog.source} mark={mark} markFor={markRow} vim={vimOn} fontSize={fontSize} />
            <EditorBar vim={vimOn} fontSize={fontSize} />
          </div>
        </Panel>
        <Separator className="vsplit" />
        <OutputPanel id="build" panelRef={buildRef} err={run.status === "err"} title={<>Build output {run.buildLog.length > 0 && <span id="buildcount">({run.buildLog.length} lines)</span>}</>}>
          <BuildLog lines={run.buildLog} />
        </OutputPanel>
      </Group>
    </div>
  );
}

/** Editor settings, in a status bar under the editor (as in VS Code). */
function EditorBar({ vim, fontSize }: { vim: boolean; fontSize: number }) {
  return (
    <div className="edbar">
      <label className="chk" title="Vim keybindings in the editor">
        <input type="checkbox" checked={vim} onChange={e => setUi({ vim: e.target.checked })} /> Vim
      </label>
      <span className="tabs zoom" role="group" aria-label="Editor font size">
        <button title={`Smaller font (${MOD}+-)`} aria-label="Smaller font" onClick={() => zoomEditor(-1)}>−</button>
        <button title={`Reset to ${EDITOR_FONT_SIZE}px (${MOD}+0)`} onClick={() => zoomEditor(null)}>{fontSize}px</button>
        <button title={`Larger font (${MOD}+=)`} aria-label="Larger font" onClick={() => zoomEditor(1)}>+</button>
      </span>
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
    <AnsiPre ref={ref} className="buildtext" text={lines.join("\n")}
      onScroll={e => {
        const p = e.currentTarget;
        atEnd.current = p.scrollTop + p.clientHeight >= p.scrollHeight - 4;
      }} />
  );
}
