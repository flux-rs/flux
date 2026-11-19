// The last run of each program, kept in IndexedDB: traces and build output can be several MB,
// more than localStorage holds. The rest of the state persists in localStorage (see store.ts).

import { del, get, set } from "idb-keyval";
import type { Run } from "./store";

/** A run as saved: without its parsed trace, which is parsed again from `trace` when loaded. */
export type SavedRun = Omit<Run, "data">;

const key = (id: number) => `blick:run:${id}`;

export const saveRun = (id: number, run: SavedRun) => set(key(id), run).catch(() => {});
export const loadRun = (id: number) => get<SavedRun>(key(id)).catch(() => undefined);
export const deleteRun = (id: number) => del(key(id)).catch(() => {});
