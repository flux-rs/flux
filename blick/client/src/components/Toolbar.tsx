// The toolbar above the trace view: mode (checker pass), view, display options and the
// locations shown in the environments.

import * as DropdownMenu from "@radix-ui/react-dropdown-menu";
import * as ToggleGroup from "@radix-ui/react-toggle-group";
import { go, selectMode, setHidden, setUi, useStore, type ViewKind } from "../store";
import { type Fn, fnLocations, type Mode } from "../trace/model";
import { envBindings } from "../trace/text";
import { Local } from "./text";

const envKeys = (env: string) => envBindings(env).map(b => b.key);

export function Toolbar({ fn, mode, kind }: { fn: Fn; mode: Mode; kind: ViewKind }) {
  const ui = useStore(s => s.ui);
  return (
    <div id="toolbar">
      <ToggleGroup.Root type="single" className="tabs" aria-label="Checker pass" value={mode.name}
        onValueChange={v => v && selectMode(v)}>
        {[...fn.modes.keys()].map(m => <ToggleGroup.Item key={m} value={m}>{m}</ToggleGroup.Item>)}
      </ToggleGroup.Root>
      <ToggleGroup.Root type="single" className="tabs" aria-label="View" value={kind === "block" ? "" : kind}
        onValueChange={v => v && go({ kind: v as ViewKind, bbs: [] })}>
        <ToggleGroup.Item value="graph" title="Control-flow graph (Esc)">Graph</ToggleGroup.Item>
        <ToggleGroup.Item value="all" title="Every block with environments">All blocks</ToggleGroup.Item>
      </ToggleGroup.Root>
      <span className="divider" />
      <Check k="hideinert" label="Hide inert" title="Hide StorageLive, StorageDead and Nop" checked={ui.hideinert} />
      <Check k="hidelt" label="Hide lifetimes" title="Hide region variables and lifetimes, e.g. &'?3 mut T and ptr(mut['?7], s)" checked={ui.hidelt} />
      <Check k="localnames" label="Show names" title="Show locals by their source variable name, e.g. e instead of _1" checked={ui.localnames} />
      <Check k="ptrhover" label="Pointer targets" title="Hovering a pointer, e.g. ptr(mut, a0), highlights the place it points to and draws an arrow to it" checked={ui.ptrhover} />
      <Check k="lochover" label="Highlight locals" title="Hovering a local in a statement highlights its occurrences in statements and environments" checked={ui.lochover} />
      <Locations fn={fn} />
    </div>
  );
}

function Check({ k, label, title, checked }: { k: "hideinert" | "hidelt" | "localnames" | "ptrhover" | "lochover"; label: string; title: string; checked: boolean }) {
  return (
    <label className="chk" title={title}>
      <input type="checkbox" checked={checked} onChange={e => setUi({ [k]: e.target.checked })} /> {label}
    </label>
  );
}

function Locations({ fn }: { fn: Fn }) {
  const hiddenList = useStore(s => s.programs.find(p => p.id === s.active)?.hidden[fn.id]) ?? [];
  const hidden = new Set(hiddenList);
  const locs = fnLocations(fn, envKeys);
  const toggle = (k: string, show: boolean) => setHidden(fn.id, show ? hiddenList.filter(x => x !== k) : [...hiddenList, k]);
  return (
    <DropdownMenu.Root>
      <DropdownMenu.Trigger asChild>
        <button className={hidden.size ? "on" : ""} title="Choose which locations are shown in the environments">
          {hidden.size ? `Locations (${hidden.size} hidden)` : "Locations"}
        </button>
      </DropdownMenu.Trigger>
      <DropdownMenu.Portal>
        <DropdownMenu.Content className="ddmenu" align="start" sideOffset={6}>
          {locs.length ? (
            <>
              <div className="ddact">
                <button onClick={() => setHidden(fn.id, [])}>show all</button>
                <button onClick={() => setHidden(fn.id, [...locs])}>hide all</button>
              </div>
              {locs.map(k => (
                <DropdownMenu.CheckboxItem key={k} className="dditem" checked={!hidden.has(k)}
                  onCheckedChange={c => toggle(k, c)}
                  // keep the menu open to toggle several
                  onSelect={e => e.preventDefault()}>
                  <span className="ddcheck">{hidden.has(k) ? "" : "✓"}</span>
                  <Local local={k} />
                </DropdownMenu.CheckboxItem>
              ))}
            </>
          ) : (
            <div className="empty">no locations</div>
          )}
        </DropdownMenu.Content>
      </DropdownMenu.Portal>
    </DropdownMenu.Root>
  );
}
