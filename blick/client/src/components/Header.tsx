// The header doubles as the tab bar: each program tab owns the whole interface below it.

import { useState } from "react";
import { activate, addProgram, closeProgram, isDirty, renameProgram, setUi, useStore } from "../store";
import { MOD, PaneIcon } from "./icons";

export function Header({ onTogglePane }: { onTogglePane: () => void }) {
  const programs = useStore(s => s.programs);
  const active = useStore(s => s.active);
  const runs = useStore(s => s.runs);
  const srcOpen = useStore(s => s.ui.srcOpen);
  const theme = useStore(s => s.ui.theme);
  const [renaming, setRenaming] = useState<number | null>(null);
  const paneLabel = `${srcOpen ? "Hide" : "Show"} program pane (${MOD}+B)`;

  return (
    <header>
      <button className="iconbtn" aria-expanded={srcOpen} aria-label={paneLabel} title={paneLabel} onClick={onTogglePane}>
        <PaneIcon />
      </button>
      <h1>Blick <span className="tag">flux</span></h1>
      <div id="ptabs" role="tablist" aria-label="Programs">
        {programs.map(p => {
          const r = runs[p.id];
          const st = r?.status ?? "none";
          const stTitle = { running: "running", ok: "verified", err: "errors", none: "not run yet" }[st];
          const dirty = isDirty(p, r);
          return (
            <div key={p.id} className={`ptab${p.id === active ? " on" : ""}`} role="tab" aria-selected={p.id === active}
              title={`${p.name}: ${stTitle}${dirty ? ", edited since the last run" : ""}. Double-click to rename.`}
              onClick={() => activate(p.id)}
              onDoubleClick={() => setRenaming(p.id)}
              // Middle click closes a tab, as in browsers and editors.
              onAuxClick={e => {
                if (e.button === 1) {
                  e.preventDefault();
                  closeProgram(p.id);
                }
              }}>
              <span className={`dot st-${st}`} />
              {renaming === p.id ? (
                <RenameInput name={p.name} onDone={name => {
                  if (name !== null) renameProgram(p.id, name);
                  setRenaming(null);
                }} />
              ) : (
                <span className="pname">{p.name}</span>
              )}
              {dirty && <span className="dirty">*</span>}
              <button className="pclose" aria-label={`Close ${p.name}`} title="Close"
                onClick={e => {
                  e.stopPropagation();
                  closeProgram(p.id);
                }}
                onDoubleClick={e => e.stopPropagation()}>
                ×
              </button>
            </div>
          );
        })}
        <button id="padd" aria-label="New program" title="New program" onClick={addProgram}>+</button>
      </div>
      <button id="theme" title="Switch between light and dark"
        onClick={() => {
          const dark = theme ? theme === "dark" : matchMedia("(prefers-color-scheme: dark)").matches;
          setUi({ theme: dark ? "light" : "dark" });
        }}>
        ◐
      </button>
    </header>
  );
}

/** Enter or leaving the field commits, Escape cancels (`onDone(null)`). */
function RenameInput({ name, onDone }: { name: string; onDone: (name: string | null) => void }) {
  const [value, setValue] = useState(name);
  let done = false;
  const finish = (v: string | null) => {
    if (done) return;
    done = true;
    onDone(v);
  };
  return (
    <input className="rename" aria-label="Program name" autoFocus value={value}
      onFocus={e => e.target.select()}
      onChange={e => setValue(e.target.value)}
      onClick={e => e.stopPropagation()}
      onDoubleClick={e => e.stopPropagation()}
      onKeyDown={e => {
        e.stopPropagation();
        if (e.key === "Enter") finish(value);
        else if (e.key === "Escape") finish(null);
      }}
      onBlur={() => finish(value)} />
  );
}
