// Splitting the checker's printed environments: `{_1: T, _2.0: U}` and contexts `{fact, fact}`.

export interface Binding {
  key: string;
  text: string;
}

function stripBraces(s: string | null | undefined): string {
  s = (s ?? "").trim();
  return s.startsWith("{") && s.endsWith("}") ? s.slice(1, -1) : s;
}

/** `{a: T, b: U}` -> [{key, text}], split at top-level commas. */
export function envBindings(s: string | null | undefined): Binding[] {
  return splitTop(stripBraces(s), ",")
    .map(p => p.trim())
    .filter(Boolean)
    .map(p => {
      const i = topIndexOf(p, ":");
      return i < 0 ? { key: p, text: "" } : { key: p.slice(0, i).trim(), text: p.slice(i + 1).trim() };
    });
}

export function rcxFacts(s: string | null | undefined): string[] {
  return splitTop(stripBraces(s), ",").map(x => x.trim()).filter(Boolean);
}

/**
 * Calls `cb(i, c, top)` for every character, `top` telling whether it is outside all brackets
 * (`()[]{}` and generic `<>`); stops when `cb` returns false. A `<` opens generics only after an
 * identifier character (not `<=`), and `>` closes them unless it is part of `->` or `=>`.
 */
function scanDepth(s: string, cb: (i: number, c: string, top: boolean) => boolean | void) {
  let d = 0, a = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i], p = s[i - 1], n = s[i + 1];
    if ("([{".includes(c)) d++;
    else if (")]}".includes(c)) d--;
    else if (c === "<" && /\w/.test(p ?? "") && n !== "=") a++;
    else if (c === ">" && a > 0 && p !== "-" && p !== "=") a--;
    if (cb(i, c, d === 0 && a === 0) === false) return;
  }
}

export function splitTop(s: string, sep: string): string[] {
  const out: string[] = [];
  let last = 0;
  scanDepth(s, (i, c, top) => {
    if (top && c === sep) {
      out.push(s.slice(last, i));
      last = i + 1;
    }
  });
  out.push(s.slice(last));
  return out;
}

export function topIndexOf(s: string, ch: string): number {
  let r = -1;
  scanDepth(s, (i, c, top) => {
    if (top && c === ch) {
      r = i;
      return false;
    }
  });
  return r;
}

/** Index of the first `ch` outside all brackets `()[]{}`, or -1. */
export function findTopOpen(s: string, ch: string): number {
  let d = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === ch && d === 0) return i;
    if ("([{".includes(c)) d++;
    else if (")]}".includes(c)) d--;
  }
  return -1;
}

/** Index of the bracket closing the one at `open`, or -1. */
export function matchClose(s: string, open: number): number {
  let d = 0;
  for (let i = open; i < s.length; i++) {
    if ("([{".includes(s[i])) d++;
    else if (")]}".includes(s[i]) && --d === 0) return i;
  }
  return -1;
}
