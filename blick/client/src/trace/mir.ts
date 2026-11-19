// The MIR of the checked bodies, as rustc dumps it (`-Zdump-mir=renumber -Zmir-include-spans=on`,
// the body borrow checking, and so Flux, works on): parsed into a mode named "mir", with the
// sections and items of the trace's modes, so that every view of a mode shows it too. Pure
// functions, no DOM.
//
// A dump looks like this (spans shortened):
//
//   // MIR for `f` 0 renumber
//
//   fn f(_1: &mut Option<i32>) -> i32 {
//       debug x => _1;                       // in scope 0 at /tmp/.../input.rs:1:10: 1:11
//       let mut _0: i32;                     // return place in scope 0 at ...
//       scope 1 {
//           debug y => _2;                   // in scope 1 at ...
//           let _4: &mut i32;                // in scope 1 at ...
//       }
//
//       bb0: {
//           _2 = const 3_i32;                // scope 0 at /tmp/.../input.rs:2:13: 2:14
//           // mir::ConstOperand             <- notes on constants: skipped
//           switchInt(move _3) -> [0: bb3, otherwise: bb1]; // scope 1 at ...
//       }
//
//       bb4 (cleanup): {
//       ...

import { type Fn, type Mode, type Section, type SrcLoc, shortSpan } from "./model";
import { matchClose, splitTop } from "./text";

/** A local's declaration. */
export interface MirLocal {
  local: string;
  ty: string;
  mutable: boolean;
  /** the source variable, from `debug x => _1` */
  name: string | null;
}

interface MirBody {
  /** the function, as rustc prints it (`f`, `<impl at ...>::get`) */
  name: string;
  locals: MirLocal[];
  mode: Mode;
}

// `debug x => _1;`, `let mut _2: bool;` and the span comment after them
const DEBUG_RE = /^\s*debug (.+?) => (_\d+);/;
const LET_RE = /^\s*let (mut )?(_\d+): (.*?);\s*(?:\/\/|$)/;
const ARG_RE = /^(mut )?(_\d+): (.*)$/;
const BLOCK_RE = /^\s*(bb\d+)( \(cleanup\))?: \{\s*$/;
// the span at the end of a statement's comment: `at /path/input.rs:3:30: 3:35`
const SPAN_RE = /at (.+?):(\d+):(\d+): (\d+):(\d+)\s*$/;

/** A statement or terminator line: its text (without the `;`) and its span, if it has one. */
function splitLine(line: string): { text: string; loc: SrcLoc | null; span: string } {
  // the comment rustc adds after the `;`: `// scope 0 at <span>`
  const c = line.lastIndexOf("// scope ");
  const code = (c >= 0 ? line.slice(0, c) : line).trim().replace(/;$/, "");
  const m = c >= 0 ? SPAN_RE.exec(line.slice(c)) : null;
  if (!m) return { text: code, loc: null, span: "" };
  const loc = { file: m[1], start_line: +m[2], start_col: +m[3], end_line: +m[4], end_col: +m[5] };
  return { text: code, loc, span: shortSpan(`${m[1]}:${m[2]}:${m[3]}`) };
}

function parseDump(text: string): MirBody | null {
  const lines = text.split("\n");
  const head = /^\/\/ MIR for `(.*)` \d+ /.exec(lines[0] ?? "");
  // promoted constants are dumped separately (`f::promoted[0]`); they are not shown
  if (!head || /::promoted\[\d+\]$/.test(head[1])) return null;
  const names = new Map<string, string>();
  const locals: MirLocal[] = [];
  const mode: Mode = { name: "mir", sections: [], errors: 0 };
  let cur: Section | null = null; // the open block
  for (const line of lines.slice(1)) {
    let m: RegExpExecArray | null;
    if (/^\s*\/\//.test(line) || !line.trim()) continue;
    if (cur) {
      if (/^\s*\}\s*$/.test(line)) {
        // a block's last line is its terminator
        const last = cur.items.pop();
        if (last && last.t === "stmt") {
          cur.term = { ...last, t: "term", kind: "term" };
          cur.items.push(cur.term);
        }
        cur = null;
      } else {
        const { text, loc, span } = splitLine(line);
        cur.items.push({ t: "stmt", kind: "mir", text, span, loc, before: null, after: null, i: 0 });
      }
    } else if (line.startsWith(`fn ${head[1]}(`)) {
      // the arguments: `fn f(_1: i32, mut _2: &mut S) -> i32 {`
      const open = head[1].length + 3;
      for (const a of splitTop(line.slice(open + 1, matchClose(line, open)), ",")) {
        if ((m = ARG_RE.exec(a.trim()))) locals.push({ local: m[2], ty: m[3], mutable: !!m[1], name: null });
      }
    } else if ((m = DEBUG_RE.exec(line))) names.set(m[2], m[1]);
    else if ((m = LET_RE.exec(line))) locals.push({ local: m[2], ty: m[3], mutable: !!m[1], name: null });
    else if ((m = BLOCK_RE.exec(line))) {
      cur = { kind: "block", bb: m[1], visit: 1, items: [], term: null, startRaw: null, idx: 0 };
      mode.sections.push(cur);
    }
  }
  for (const l of locals) l.name = names.get(l.local) ?? null;
  locals.sort((a, b) => +a.local.slice(1) - +b.local.slice(1));
  mode.sections.forEach((s, n) => {
    s.idx = n;
    s.items.forEach((it, i) => (it.i = i));
  });
  return { name: head[1], locals, mode };
}

/** A source location as a key: equal spans in the trace and in a dump name the same code. */
const locKey = (l: SrcLoc) => `${l.start_line}:${l.start_col}:${l.end_line}:${l.end_col}`;

function spanKeys(modes: Iterable<Mode>): Set<string> {
  const keys = new Set<string>();
  for (const m of modes) for (const s of m.sections) for (const it of s.items) if (it.t !== "sep" && it.t !== "goto" && it.loc) keys.add(locKey(it.loc));
  return keys;
}

/** The last segment of a function's path: `get` for `S::get` and `<impl at ...>::get`. */
const lastSegment = (name: string) => name.slice(name.lastIndexOf("::") + 2);

/**
 * Adds the MIR in `dumps` to the functions of the trace, as their mode "mir" (and their locals).
 * A dump belongs to the function it shares the most statement spans with (rustc and the trace name
 * functions differently: `<impl at ...>::get` is `S::get`), or else to the one with its name. A
 * dump of a function not in the trace gets a function of its own.
 */
export function addMir(fns: Fn[], dumps: string[]) {
  const keys = new Map(fns.map(fn => [fn, spanKeys(fn.modes.values())]));
  for (const body of dumps.map(parseDump)) {
    if (!body) continue;
    const mine = spanKeys([body.mode]);
    let best: Fn | null = null, shared = 0;
    for (const [fn, ks] of keys) {
      let n = 0;
      for (const k of mine) if (ks.has(k)) n++;
      if (n > shared) [best, shared] = [fn, n];
    }
    best ??= fns.find(fn => fn.id === body.name) ?? fns.find(fn => lastSegment(fn.id) === lastSegment(body.name)) ?? null;
    if (!best) {
      best = { id: body.name, modes: new Map(), solution: null, names: new Map(), locals: null };
      fns.push(best);
    }
    // first: the passes are listed in this order, and the MIR is what they check
    best.modes = new Map([["mir", body.mode], ...best.modes]);
    best.locals = body.locals;
    for (const l of body.locals) if (l.name && !best.names.has(l.local)) best.names.set(l.local, l.name);
  }
}
