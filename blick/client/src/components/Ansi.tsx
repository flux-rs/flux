// Output with ANSI color escapes (cargo's and rustc's), rendered with ansi_up. Colors become
// classes (`ansi-red-fg`, ...), themed in style.css, so they read well in light and dark.

import { AnsiUp } from "ansi_up";
import { forwardRef, useMemo } from "react";

const ESCAPE = /\x1b\[[0-9;]*m/g;

/** The text without its color escapes. */
export const plain = (s: string) => s.replace(ESCAPE, "");

function toHtml(text: string): string {
  const au = new AnsiUp(); // stateful (colors carry over between calls): one per text
  au.use_classes = true;
  return au.ansi_to_html(text);
}

type Props = { text: string } & Omit<React.HTMLAttributes<HTMLPreElement>, "children" | "dangerouslySetInnerHTML">;

/** A `<pre>` showing `text` with its colors (ansi_up escapes the text itself). */
export const AnsiPre = forwardRef<HTMLPreElement, Props>(function AnsiPre({ text, ...rest }, ref) {
  const html = useMemo(() => toHtml(text), [text]);
  return <pre ref={ref} {...rest} dangerouslySetInnerHTML={{ __html: html }} />;
});
