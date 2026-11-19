// The dialog to open a program from the server's folder of programs (Flux's regression tests with
// `cargo xtask blick`). One text field drives it, as in VS Code's Quick Open and fzf:
//
// - With nothing typed, it browses the current folder: its subfolders, then its files (and, at the
//   top, the programs opened last).
// - Typing fuzzy-searches (fuzzysort) every file and folder under the current folder, so the
//   current folder doubles as the scope of the search.
//
// cmdk runs the list: ↑/↓ (and Ctrl+N/P, Ctrl+J/K) move, Enter opens a file or enters a folder,
// and it keeps focus in the field with the ARIA combobox pattern. On top of it, Backspace in the
// empty field (or ←) goes up a folder, → or Tab enters a folder, and Esc closes.

import { Command } from "cmdk";
import fuzzysort from "fuzzysort";
import { useEffect, useLayoutEffect, useMemo, useRef, useState } from "react";
import { fetchFile, fetchFiles } from "../api";
import type { FileList } from "../bindings/FileList";
import { highlightRust } from "../highlight";
import { openProgram, setOpening, setUi, useStore } from "../store";
import { FileIcon, FolderIcon } from "./icons";

/** Search results shown; there are rarely more worth reading. */
const MAX_RESULTS = 200;

export function OpenDialog() {
  const opening = useStore(s => s.opening);
  return opening ? <Picker /> : null;
}

interface Folder {
  dirs: string[];
  files: string[];
  /** the files in it and below */
  count: number;
}

interface Item {
  kind: "up" | "dir" | "file";
  path: string;
  /** what is shown and searched: the path relative to the current folder, or the name */
  label: string;
  group?: string;
  /** the matched characters of `label` */
  positions?: readonly number[];
}

const parent = (p: string) => p.slice(0, Math.max(0, p.lastIndexOf("/")));
const base = (p: string) => p.slice(p.lastIndexOf("/") + 1);
const RECENT = "Recently opened";
/** an item's value in cmdk: unique, as a recent file is listed twice */
const valueOf = (it: Pick<Item, "kind" | "path" | "group">) => `${it.group === RECENT ? "recent" : it.kind}:${it.path}`;

/** The folders of `files`, by path ("" is the root). */
function folders(files: string[]): Map<string, Folder> {
  const map = new Map<string, Folder>();
  const folder = (p: string) => {
    let f = map.get(p);
    if (!f) {
      f = { dirs: [], files: [], count: 0 };
      map.set(p, f);
      if (p) folder(parent(p)).dirs.push(p);
    }
    return f;
  };
  for (const file of files) {
    folder(parent(file)).files.push(file);
    for (let d = parent(file); ; d = parent(d)) {
      folder(d).count++;
      if (!d) break;
    }
  }
  return map;
}

function Picker() {
  const recent = useStore(s => s.recent);
  const [list, setList] = useState<FileList | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [dir, setDir] = useState(() => useStore.getState().ui.openDir);
  const [query, setQuery] = useState("");
  const [selected, setSelected] = useState("");
  const dialog = useRef<HTMLDialogElement>(null);
  const inputRef = useRef<HTMLInputElement>(null);
  const close = () => setOpening(false);
  const [read] = useState(fileCache);

  useLayoutEffect(() => {
    dialog.current?.showModal();
    // `showModal` focuses the first control, a breadcrumb: the field is where typing goes
    inputRef.current?.focus();
  }, []);
  // listed anew each time, so new tests show up
  useEffect(() => {
    fetchFiles().then(setList, e => setError(`Cannot list the programs: ${e.message}`));
  }, []);

  const tree = useMemo(() => folders(list?.files ?? []), [list]);
  // the folder may have gone since it was saved
  const cwd = tree.has(dir) || !list ? dir : "";
  useEffect(() => setUi({ openDir: cwd }), [cwd]);

  const items: Item[] = useMemo(() => {
    const folder = tree.get(cwd);
    if (!list || !folder) return [];
    const q = query.trim();
    if (!q) {
      const out: Item[] = cwd ? [{ kind: "up", path: parent(cwd), label: ".." }] : [];
      const known = new Set(list.files);
      const recents = cwd ? [] : recent.filter(p => known.has(p));
      for (const p of recents) out.push({ kind: "file", path: p, label: p, group: RECENT });
      // headed only to set them apart from the recent files
      const group = recents.length ? "All programs" : undefined;
      for (const d of folder.dirs) out.push({ kind: "dir", path: d, label: base(d), group });
      for (const f of folder.files) out.push({ kind: "file", path: f, label: base(f), group });
      return out;
    }
    // the files and folders under the current one, by their path relative to it
    const prefix = cwd ? `${cwd}/` : "";
    const rel = (kind: "dir" | "file", path: string): Item => ({ kind, path, label: path.slice(prefix.length) });
    const targets = [
      ...[...tree.keys()].filter(d => d && d.startsWith(prefix)).map(d => rel("dir", d)),
      ...list.files.filter(f => f.startsWith(prefix)).map(f => rel("file", f)),
    ];
    // the default threshold drops weak but useful matches, e.g. `t07` for `trait07.rs`
    return fuzzysort.go(q, targets, { key: "label", threshold: 0, limit: MAX_RESULTS })
      .map(r => ({ ...r.obj, positions: r.indexes }));
  }, [list, tree, cwd, query, recent]);
  // the selection, or the first item while it is not in the list
  const cur = items.find(it => valueOf(it) === selected) ?? items[0];

  const enter = (path: string, select?: string) => {
    setDir(path);
    setQuery("");
    setSelected(select ?? "");
  };
  /** Goes up a folder, onto the folder it came from. */
  const up = () => cwd && enter(parent(cwd), valueOf({ kind: "dir", path: cwd }));

  const choose = async (it: Item | undefined) => {
    if (!it) return;
    if (it.kind === "up") return up();
    if (it.kind === "dir") return enter(it.path);
    try {
      // read again: the file may have changed since it was previewed
      openProgram(it.path, await fetchFile(it.path));
      close();
    } catch (e) {
      setError(`Cannot open ${it.path}: ${e instanceof Error ? e.message : e}`);
    }
  };
  const onKeyDown = (e: React.KeyboardEvent) => {
    if (!query && (e.key === "Backspace" || e.key === "ArrowLeft") && cwd) up();
    else if ((e.key === "Tab" || (!query && e.key === "ArrowRight")) && cur?.kind === "dir") enter(cur.path);
    else if (e.key !== "Tab") return;
    e.preventDefault();
  };

  const crumbs = cwd ? cwd.split("/") : [];
  const searching = !!query.trim();
  // consecutive items of a group, in order
  const groups: { heading?: string; items: Item[] }[] = [];
  for (const it of items) {
    const last = groups[groups.length - 1];
    if (last && last.heading === it.group) last.items.push(it);
    else groups.push({ heading: it.group, items: [it] });
  }
  return (
    <dialog ref={dialog} id="opendlg" aria-label="Open a program"
      onCancel={e => {
        e.preventDefault();
        close();
      }}
      // a click on the backdrop lands on the dialog itself
      onMouseDown={e => e.target === dialog.current && close()}>
      <Command className="odmain" label="Open a program" shouldFilter={false} loop
        value={cur ? valueOf(cur) : ""} onValueChange={setSelected} onKeyDown={onKeyDown}>
        <nav className="odcrumbs" aria-label="Folder">
          <button tabIndex={-1} onClick={() => enter("")} title={list?.root}>{list ? base(list.root) : "…"}</button>
          {crumbs.map((c, i) => (
            <span key={i}>
              <span className="odsep">/</span>
              <button tabIndex={-1} onClick={() => enter(crumbs.slice(0, i + 1).join("/"))}>{c}</button>
            </span>
          ))}
        </nav>
        <Command.Input ref={inputRef} spellCheck={false} value={query} onValueChange={setQuery}
          placeholder={cwd ? `Search in ${cwd}/` : "Search all programs, or pick a folder"} />
        <Command.List>
          {groups.map((g, i) => (
            <Command.Group key={`${i}:${g.heading ?? ""}`} heading={g.heading}>
              {g.items.map(it => (
                <Command.Item key={valueOf(it)} value={valueOf(it)} className="opt" onSelect={() => choose(it)}>
                  <ItemRow it={it} tree={tree} searching={searching} />
                </Command.Item>
              ))}
            </Command.Group>
          ))}
          {list && <Command.Empty className="odnone">{query ? "No matches" : "No programs here"}</Command.Empty>}
          {!list && !error && <Command.Loading className="odnone">Loading…</Command.Loading>}
        </Command.List>
        <div className="odfoot">
          {error ? <span className="err">{error}</span> : (
            <>
              <span>{searching ? `${items.length}${items.length === MAX_RESULTS ? "+" : ""} matches` : list ? `${tree.get(cwd)?.count ?? 0} programs` : ""}</span>
              <span className="odkeys">
                <kbd>↑</kbd><kbd>↓</kbd> move <kbd>Enter</kbd> open {cwd && <><kbd>⌫</kbd> up </>}<kbd>Esc</kbd> close
              </span>
            </>
          )}
        </div>
      </Command>
      <Preview item={cur} tree={tree} read={read} />
    </dialog>
  );
}

/** An item: the name first, then the folder it is in (as in VS Code's Quick Open), with the matched characters marked. */
function ItemRow({ it, tree, searching }: { it: Item; tree: Map<string, Folder>; searching: boolean }) {
  const cut = it.label.lastIndexOf("/") + 1;
  const pos = new Set(searching ? it.positions : []);
  return (
    <>
      {it.kind === "file" ? <FileIcon /> : <FolderIcon />}
      <span className="odname"><Hl text={it.label} from={cut} to={it.label.length} pos={pos} /></span>
      {cut > 0 && <span className="oddir"><Hl text={it.label} from={0} to={cut - 1} pos={pos} /></span>}
      {it.kind === "dir" && <span className="odcount">{tree.get(it.path)?.count}</span>}
    </>
  );
}

/** `text[from..to]` with the characters at `pos` marked. */
function Hl({ text, from, to, pos }: { text: string; from: number; to: number; pos: Set<number> }) {
  const out: React.ReactNode[] = [];
  for (let i = from; i < to;) {
    const on = pos.has(i);
    let j = i;
    while (j < to && pos.has(j) === on) j++;
    out.push(on ? <mark key={i}>{text.slice(i, j)}</mark> : text.slice(i, j));
    i = j;
  }
  return <>{out}</>;
}

// ---- preview ----

/**
 * Reads files, each once: the preview shows a file again without a request. Made per opening of
 * the dialog, so a file edited on disk since is read anew.
 */
function fileCache(): (path: string) => Promise<string> {
  const cache = new Map<string, Promise<string>>();
  return path => {
    let p = cache.get(path);
    if (!p) {
      p = fetchFile(path);
      cache.set(path, p);
      // a failed read is tried again next time
      p.catch(() => cache.delete(path));
    }
    return p;
  };
}

/** Lines of a file shown in the preview. */
const PREVIEW_LINES = 400;

function Preview({ item, tree, read }: { item: Item | undefined; tree: Map<string, Folder>; read: (path: string) => Promise<string> }) {
  const [text, setText] = useState<{ path: string; text: string } | null>(null);
  const path = item?.kind === "file" ? item.path : null;
  // parsed once per file, not on each keystroke in the field
  const lines = useMemo(() => text && highlightRust(text.text), [text]);
  useEffect(() => {
    if (!path) return;
    let live = true;
    // wait for the selection to settle while the arrow keys are held
    const t = setTimeout(() => {
      read(path).then(text => live && setText({ path, text }), e => live && setText({ path, text: `(${e.message})` }));
    }, 60);
    return () => {
      live = false;
      clearTimeout(t);
    };
  }, [path, read]);

  let body;
  if (!item) body = null;
  else if (item.kind !== "file") {
    const f = tree.get(item.path);
    body = f && (
      <div className="odfolder">
        <div className="odpath">{item.path || "(top)"}/</div>
        <p>{f.count} programs{f.dirs.length ? ` in ${f.dirs.length} folders` : ""}</p>
        <ul>
          {f.dirs.slice(0, 30).map(d => <li key={d}><FolderIcon /> {base(d)} <span className="odcount">{tree.get(d)?.count}</span></li>)}
          {f.files.slice(0, Math.max(0, 30 - f.dirs.length)).map(x => <li key={x}><FileIcon /> {base(x)}</li>)}
        </ul>
      </div>
    );
  } else if (text?.path !== item.path || !lines) body = <div className="odpath">{item.path}</div>;
  else {
    body = (
      <>
        <div className="odpath">{item.path} <span className="odcount">{lines.length} lines</span></div>
        <pre className="odsrc">
          {lines.slice(0, PREVIEW_LINES).map((l, i) => (
            <div key={i}>
              <span className="ln">{i + 1}</span>
              {l.length ? l.map((p, j) => (p.cls ? <span key={j} className={p.cls}>{p.text}</span> : p.text)) : " "}
            </div>
          ))}
          {lines.length > PREVIEW_LINES && <div className="odmore">…</div>}
        </pre>
      </>
    );
  }
  return <aside className="odpreview" aria-label="Preview">{body}</aside>;
}
