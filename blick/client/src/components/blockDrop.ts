// Where a block dragged over the open blocks would go, and the bar that shows it.

import type { BlockDrop } from "../store";

/** A drop bar, in px relative to the columns' container: vertical (a new column) or horizontal (into a column). */
export interface DropBar {
  dir: "v" | "h";
  x: number;
  y: number;
  len: number;
}

/** half the gap between columns (`.cols`) and between blocks (`.sec`'s bottom margin) */
const COL_GAP = 6;
const BLOCK_GAP = 5;
/** the outer part of a column where a drop makes a new column: a fifth of it, at most 80px */
const edgeOf = (r: DOMRect) => Math.min(80, r.width / 5);

/**
 * The drop at the pointer (`x`, `y`, client coordinates) over the columns in `el`: its `.col`s, each with
 * its `.cblk` blocks. Only the pointer's x picks a column, so anywhere below a column drops at its end.
 * When the columns are stacked (a narrow window), the pointer's y picks the column and there are no
 * new-column drops.
 */
export function hitTest(el: HTMLElement, x: number, y: number): { drop: BlockDrop; bar: DropBar } | null {
  const box = el.getBoundingClientRect();
  const cols = [...el.querySelectorAll<HTMLElement>(":scope > .col")].map(c => ({
    r: c.getBoundingClientRect(),
    blocks: [...c.querySelectorAll<HTMLElement>(":scope > .cblk")].map(b => b.getBoundingClientRect()),
  }));
  if (!cols.length) return null;

  let ci = -1;
  if (cols.length > 1 && cols[1].r.top >= cols[0].r.bottom - 1) {
    for (let i = 0; i < cols.length; i++) if (cols[i].r.top <= y) ci = i;
    ci = Math.max(ci, 0);
  } else {
    ci = cols.findIndex(c => x >= c.r.left && x <= c.r.right);
    const inLeftEdge = ci >= 0 && x < cols[ci].r.left + edgeOf(cols[ci].r);
    const inRightEdge = ci >= 0 && x > cols[ci].r.right - edgeOf(cols[ci].r);
    if (ci < 0 || inLeftEdge || inRightEdge) {
      // between columns, or at their outer edges: a new column
      const at = ci < 0 ? cols.filter(c => c.r.left + c.r.width / 2 < x).length : inLeftEdge ? ci : ci + 1;
      const bx = at === 0 ? cols[0].r.left - COL_GAP
        : at === cols.length ? cols[at - 1].r.right + COL_GAP
        : (cols[at - 1].r.right + cols[at].r.left) / 2;
      return { drop: { kind: "newcol", at }, bar: { dir: "v", x: bx - box.left, y: 0, len: box.height } };
    }
  }

  const c = cols[ci];
  const at = c.blocks.filter(b => b.top + b.height / 2 < y).length;
  const by = at === 0 ? c.blocks[0].top - BLOCK_GAP : c.blocks[at - 1].bottom + BLOCK_GAP;
  return { drop: { kind: "into", col: ci, at }, bar: { dir: "h", x: c.r.left - box.left, y: by - box.top, len: c.r.width } };
}
