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

/** A sun: light theme. */
export function SunIcon() {
  return (
    <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round">
      <circle cx="8" cy="8" r="2.8" />
      <path d="M8 1.2v1.6M8 13.2v1.6M1.2 8h1.6M13.2 8h1.6M3.2 3.2l1.1 1.1M11.7 11.7l1.1 1.1M3.2 12.8l1.1-1.1M11.7 4.3l1.1-1.1" />
    </svg>
  );
}

/** A crescent moon: dark theme. */
export function MoonIcon() {
  return (
    <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinejoin="round">
      <path d="M13.5 9.6A5.8 5.8 0 0 1 6.4 2.5a5.8 5.8 0 1 0 7.1 7.1z" />
    </svg>
  );
}

/** A monitor: follow the system's theme. */
export function MonitorIcon() {
  return (
    <svg viewBox="0 0 16 16" width="14" height="14" aria-hidden="true" fill="none" stroke="currentColor" strokeWidth="1.4" strokeLinecap="round" strokeLinejoin="round">
      <rect x="1.8" y="2.5" width="12.4" height="8.5" rx="1.3" />
      <path d="M5.5 14h5M8 11v3" />
    </svg>
  );
}
