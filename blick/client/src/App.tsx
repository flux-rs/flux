// A three-pane workbench: program | trace | functions.

import { useEffect, useState } from "react";
import { useHotkeys } from "react-hotkeys-hook";
import { Group, Panel, Separator, useDefaultLayout, usePanelRef } from "react-resizable-panels";
import { BlockView } from "./components/BlockView";
import { GraphView } from "./components/GraphView";
import { Header } from "./components/Header";
import { MOD } from "./components/icons";
import { OpenDialog } from "./components/OpenDialog";
import { ProgramPane } from "./components/ProgramPane";
import { TextCtx } from "./components/text";
import { Toolbar } from "./components/Toolbar";
import { curProgram, curRun, resolveView, selectFn, setOpening, setSelRow, setUi, useStore } from "./store";
import type { Fn, Trace } from "./trace/model";

export function App() {
  const ui = useStore(s => s.ui);
  const srcRef = usePanelRef();
  const layout = useDefaultLayout({ id: "blick:main", storage: localStorage });

  useEffect(() => {
    if (ui.theme) document.documentElement.dataset.theme = ui.theme;
    else delete document.documentElement.dataset.theme;
  }, [ui.theme]);

  const togglePane = () => {
    const p = srcRef.current;
    if (p?.isCollapsed()) p.expand();
    else p?.collapse();
  };
  // VS Code's shortcut for its side bar
  useHotkeys("mod+b", togglePane, { preventDefault: true, enableOnFormTags: true, enableOnContentEditable: true });
  // VS Code's Quick Open
  useHotkeys("mod+p", () => useStore.getState().filesDir && setOpening(true),
    { preventDefault: true, enableOnFormTags: true, enableOnContentEditable: true });

  // A click anywhere that isn't a statement row or a control clears the selected row.
  useEffect(() => {
    const onClick = (e: MouseEvent) => {
      if (useStore.getState().selRow === null || getSelection()?.toString()) return;
      const t = e.target as Element;
      if (t.closest?.(".row, button, input, textarea, select, label, a, [role^=menuitem], #srcpane")) return;
      setSelRow(null);
    };
    document.addEventListener("click", onClick);
    return () => document.removeEventListener("click", onClick);
  }, []);

  return (
    <>
      <Header onTogglePane={togglePane} />
      <main>
        <Group orientation="horizontal" id="blick:main" {...layout} className="maingroup">
          <Panel id="src" panelRef={srcRef} collapsible collapsedSize={0} minSize={260} defaultSize={460} maxSize="70%"
            onResize={size => {
              const open = size.inPixels > 0;
              if (open !== useStore.getState().ui.srcOpen) setUi({ srcOpen: open });
            }}>
            <section id="srcpane" aria-label="Input">
              <ProgramPane />
            </section>
          </Panel>
          <Separator className="hsplit" />
          <Panel id="content" minSize={300}>
            <TraceArea />
          </Panel>
        </Group>
      </main>
      <OpenDialog />
    </>
  );
}

function TraceArea() {
  const prog = useStore(curProgram);
  const run = useStore(curRun);
  const ui = useStore(s => s.ui);
  const filesDir = useStore(s => s.filesDir);
  const tv = resolveView(run.data, prog.view);

  let content;
  if (!run.data) {
    content = (
      <div id="view">
        {run.noTrace ? (
          <p className="empty">
            <strong>No checker trace.</strong> The run stopped before the refinement checker ran; the output under the
            program says why.
          </p>
        ) : (
          <p className="empty">
            Nothing loaded yet. Paste a program in the <strong>Input</strong> pane and run Flux on it
            {filesDir ? <>, or open one of the programs in <code>{filesDir}</code> (<kbd>{MOD}</kbd>+<kbd>P</kbd>)</> : null}.
            <br />
            In the graph, double-click a block to see its environments and drag blocks to move them. Click a statement to
            highlight what it changed. <kbd>j</kbd> and <kbd>k</kbd> move between statements; <kbd>Esc</kbd> goes back to
            the graph.
          </p>
        )}
      </div>
    );
  } else if (!tv) {
    content = <div id="view"><p className="empty"><strong>No checker events in this trace.</strong></p></div>;
  } else {
    const { fn, mode, view } = tv;
    content = (
      <TextCtx.Provider value={{ fn, hidelt: ui.hidelt, localnames: ui.localnames }}>
        <Toolbar fn={fn} mode={mode} kind={view.kind} />
        {view.kind === "graph" ? (
          <GraphView fn={fn} mode={mode} hideinert={ui.hideinert} hidelt={ui.hidelt} localnames={ui.localnames} />
        ) : (
          <BlockView fn={fn} mode={mode} view={view} hideinert={ui.hideinert} />
        )}
      </TextCtx.Provider>
    );
  }
  return (
    <div className="tracearea">
      <section id="content">{content}</section>
      <FnList data={run.data} current={tv?.fn ?? null} />
    </div>
  );
}

function FnList({ data, current }: { data: Trace | null; current: Fn | null }) {
  const [q, setQ] = useState("");
  const fns = data ? data.fns.filter(fn => !q || fn.id.toLowerCase().includes(q.toLowerCase())) : [];
  return (
    <aside id="side">
      <div className="sidehd"><span>Functions</span><span id="fncount">{data ? data.fns.length : ""}</span></div>
      <input type="text" placeholder="Filter" value={q} onChange={e => setQ(e.target.value)} />
      <div id="fnlist">
        {fns.map(fn => {
          const errs = [...fn.modes.values()].reduce((a, m) => a + m.errors, 0);
          return (
            <div key={fn.id} className={`fn${fn === current ? " sel" : ""}`} onClick={() => selectFn(fn.id)}
              title={`${fn.id}: ${[...fn.modes.keys()].join(", ")}${errs ? `; ${errs} statements without an end event` : ""}`}>
              <span>{fn.id}</span>
              {errs > 0 && <span className="err">failed</span>}
            </div>
          );
        })}
      </div>
    </aside>
  );
}
