export type Kvar = string;

export type KvarApp = {
    kvar: Kvar;
    args: string[];
};

// The `body` should be an escaped-string ...
export type Assignment = { params: string[]; body: string };

export type KvarSol = Map<Kvar, Assignment>;

export type DefId = { file: string; index: number };

export type DefIdSol = Map<DefId, KvarSol>;

export type KvarDefs = {
    // mapping from line number to DefId at that line, if any
    lineId: Map<number, DefId>;

}
