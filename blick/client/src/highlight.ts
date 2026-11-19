// Rust syntax highlighting, shared by the editor and the preview of the open dialog: syntax tags
// map to `hl-*` classes, colored in style.css.

import { rustLanguage } from "@codemirror/lang-rust";
import { highlightCode, tagHighlighter, tags as t } from "@lezer/highlight";

export const highlighter = tagHighlighter([
  { tag: [t.keyword, t.controlKeyword, t.modifier, t.self, t.bool, t.definitionKeyword, t.moduleKeyword], class: "hl-kw" },
  { tag: [t.typeName, t.className, t.namespace], class: "hl-ty" },
  { tag: [t.string, t.character, t.special(t.string)], class: "hl-str" },
  { tag: [t.number, t.integer, t.float], class: "hl-num" },
  { tag: [t.comment, t.lineComment, t.blockComment], class: "hl-com" },
  { tag: [t.meta, t.attributeName, t.processingInstruction], class: "hl-meta" },
  { tag: [t.function(t.variableName), t.function(t.propertyName)], class: "hl-fn" },
  { tag: t.macroName, class: "hl-mac" },
  { tag: [t.labelName, t.special(t.variableName)], class: "hl-life" },
]);

/** A line of highlighted code: its pieces of text, each with its classes ("" for none). */
export type HlLine = { text: string; cls: string }[];

/** Highlights the Rust program `code`, line by line. */
export function highlightRust(code: string): HlLine[] {
  const lines: HlLine[] = [[]];
  highlightCode(code, rustLanguage.parser.parse(code), highlighter,
    (text, cls) => lines[lines.length - 1].push({ text, cls }),
    () => lines.push([]));
  return lines;
}
