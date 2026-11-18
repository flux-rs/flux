/** A small ghost (16x16 user units): a rounded body with a zigzag hem and two eyes. */
export function GhostIcon() {
  return (
    <>
      <path className="gbody" d="M3.5 14V7.5a4.5 4.5 0 0 1 9 0V14l-1.5-1.4-1.5 1.4-1.5-1.4-1.5 1.4-1.5-1.4z" />
      <circle className="geye" cx="6.5" cy="7.5" r="1" />
      <circle className="geye" cx="9.5" cy="7.5" r="1" />
    </>
  );
}

/** A window with its left column shaded while the program pane is open. */
export function PaneIcon() {
  return (
    <svg viewBox="0 0 16 16" width="16" height="16" aria-hidden="true">
      <rect className="pnl" x="1.5" y="2.5" width="5" height="11" rx="1" />
      <rect x="1.5" y="2.5" width="13" height="11" rx="1.5" fill="none" stroke="currentColor" strokeWidth="1.2" />
      <line x1="6.5" y1="2.5" x2="6.5" y2="13.5" stroke="currentColor" strokeWidth="1.2" />
    </svg>
  );
}

export const IS_MAC = /Mac|iPhone|iPad/.test(navigator.platform);
export const MOD = IS_MAC ? "Cmd" : "Ctrl";
