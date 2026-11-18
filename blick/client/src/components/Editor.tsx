// The program editor (CodeMirror), with the source lines of the selected statement marked.

import { defaultKeymap, history, historyKeymap, indentWithTab } from "@codemirror/commands";
import { rust } from "@codemirror/lang-rust";
import { bracketMatching, HighlightStyle, indentOnInput, indentUnit, syntaxHighlighting } from "@codemirror/language";
import { highlightSelectionMatches, searchKeymap } from "@codemirror/search";
import { Compartment, EditorState, Prec, StateEffect, StateField } from "@codemirror/state";
import { Decoration, type DecorationSet, drawSelection, EditorView, keymap, lineNumbers, placeholder } from "@codemirror/view";
import { tags as t } from "@lezer/highlight";
import { vim } from "@replit/codemirror-vim";
import { useEffect, useRef } from "react";
import { runFlux, setSource, zoomEditor } from "../store";
import { MOD } from "./icons";

export interface LineRange {
  start: number;
  end: number;
}

const highlight = HighlightStyle.define([
  { tag: [t.keyword, t.controlKeyword, t.modifier, t.self, t.bool, t.definitionKeyword, t.moduleKeyword], color: "var(--hl-kw)" },
  { tag: [t.typeName, t.className, t.namespace], color: "var(--hl-ty)" },
  { tag: [t.string, t.character, t.special(t.string)], color: "var(--hl-str)" },
  { tag: [t.number, t.integer, t.float], color: "var(--hl-num)" },
  { tag: [t.comment, t.lineComment, t.blockComment], color: "var(--hl-com)", fontStyle: "italic" },
  { tag: [t.meta, t.attributeName, t.processingInstruction], color: "var(--hl-meta)" },
  { tag: [t.function(t.variableName), t.function(t.propertyName)], color: "var(--hl-fn)" },
  { tag: t.macroName, color: "var(--hl-mac)" },
  { tag: [t.labelName, t.special(t.variableName)], color: "var(--hl-life)" },
]);

const theme = EditorView.theme({
  "&": { height: "100%", background: "var(--bg)", color: "var(--fg)", fontSize: "var(--code-size)" },
  "&.cm-focused": { outline: "none" },
  ".cm-scroller": { fontFamily: "var(--mono)", lineHeight: "1.55" },
  ".cm-content": { caretColor: "var(--fg)", padding: "10px 0" },
  ".cm-cursor": { borderLeftColor: "var(--fg)" },
  ".cm-gutters": { background: "var(--bg)", color: "var(--faint)", border: "none" },
  "&.cm-focused .cm-selectionBackground, .cm-selectionBackground": { background: "var(--sel-src) !important" },
  ".cm-placeholder": { color: "var(--faint)" },
  ".cm-matchingBracket": { background: "var(--sel)", outline: "none" },
  ".cm-selectionMatch": { background: "var(--sel)" },
});

// The marked lines: the source lines of the selected statement.
const setMark = StateEffect.define<LineRange | null>();
const markField = StateField.define<DecorationSet>({
  create: () => Decoration.none,
  update(deco, tr) {
    deco = deco.map(tr.changes);
    for (const e of tr.effects) {
      if (!e.is(setMark)) continue;
      const doc = tr.state.doc;
      deco = Decoration.none;
      if (e.value && e.value.start <= doc.lines) {
        const lines = [];
        for (let l = e.value.start; l <= Math.min(e.value.end, doc.lines); l++) {
          lines.push(Decoration.line({ class: "cm-srcmark" }).range(doc.line(l).from));
        }
        deco = Decoration.set(lines);
      }
    }
    return deco;
  },
  provide: f => EditorView.decorations.from(f),
});

// Vim keybindings, switched on and off at runtime. Each program's editor state has the compartment.
const vimMode = new Compartment();
const vimExt = (on: boolean) => (on ? vim({ status: true }) : []);

function newState(doc: string, vimOn: boolean): EditorState {
  return EditorState.create({
    doc,
    extensions: [
      // first, so vim sees the keys before the other keymaps
      vimMode.of(vimExt(vimOn)),
      lineNumbers(),
      history(),
      drawSelection(),
      indentOnInput(),
      bracketMatching(),
      highlightSelectionMatches(),
      indentUnit.of("    "),
      EditorState.tabSize.of(4),
      rust(),
      syntaxHighlighting(highlight),
      theme,
      markField,
      placeholder(`Paste a Rust program here and press ${MOD}+Enter.`),
      Prec.highest(keymap.of([
        { key: "Mod-Enter", run: () => (runFlux(), true) },
        // zoom, as in VS Code (instead of the browser's page zoom while the editor has focus)
        { key: "Mod-=", run: () => (zoomEditor(1), true) },
        { key: "Mod-+", run: () => (zoomEditor(1), true) },
        { key: "Mod--", run: () => (zoomEditor(-1), true) },
        { key: "Mod-0", run: () => (zoomEditor(null), true) },
      ])),
      keymap.of([...defaultKeymap, ...historyKeymap, ...searchKeymap, indentWithTab]),
      EditorView.updateListener.of(u => {
        if (u.docChanged) setSource(u.state.doc.toString());
      }),
    ],
  });
}

// Each program keeps its own editor state (and so its own undo history) while the page lives.
const states = new Map<number, EditorState>();

interface Props {
  progId: number;
  source: string;
  mark: LineRange | null;
  /** identifies what the mark was set for: the mark is scrolled into view when it changes */
  markFor: string | null;
  vim: boolean;
  fontSize: number;
}

export function Editor({ progId, source, mark, markFor, vim: vimOn, fontSize }: Props) {
  const host = useRef<HTMLDivElement>(null);
  const view = useRef<EditorView | null>(null);
  const shownId = useRef<number | null>(null);

  useEffect(() => {
    const v = new EditorView({ parent: host.current! });
    view.current = v;
    return () => {
      if (shownId.current !== null) states.set(shownId.current, v.state);
      v.destroy();
      view.current = null;
      shownId.current = null;
    };
  }, []);

  // Shows the active program, keeping the state of the one being left.
  useEffect(() => {
    const v = view.current!;
    if (shownId.current === progId) return;
    if (shownId.current !== null) states.set(shownId.current, v.state);
    let st = states.get(progId);
    if (!st || st.doc.toString() !== source) st = newState(source, vimOn);
    v.setState(st);
    shownId.current = progId;
  }, [progId]);

  // after switching programs too: the program's state may have been saved with the other setting
  useEffect(() => {
    view.current!.dispatch({ effects: vimMode.reconfigure(vimExt(vimOn)) });
  }, [vimOn, progId]);

  // the font size is the `--code-size` of the host; the editor measures its lines again
  useEffect(() => {
    view.current!.requestMeasure();
  }, [fontSize]);

  useEffect(() => {
    const v = view.current!;
    const effects: StateEffect<unknown>[] = [setMark.of(mark)];
    if (mark && mark.start <= v.state.doc.lines) {
      effects.push(EditorView.scrollIntoView(v.state.doc.line(mark.start).from, { y: "nearest", yMargin: 60 }));
    }
    v.dispatch({ effects });
  }, [mark?.start, mark?.end, markFor, progId]);

  return <div id="srcwrap" ref={host} style={{ "--code-size": `${fontSize}px` } as React.CSSProperties} />;
}
