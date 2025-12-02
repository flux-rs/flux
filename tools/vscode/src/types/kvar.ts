export type Kvar = string;

// The `body` should be an escaped-string ...
export type Assignment = { params: string[]; body: string };

export type KvarSol = Map<Kvar, Assignment>;

export type DefId = { file: string; index: number };

export type DefIdSol = Map<DefId, KvarSol>;

export type KvarApp = {
    kvar: string;
    args: string[];
};
