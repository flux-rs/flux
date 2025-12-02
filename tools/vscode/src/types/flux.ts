import * as vscode from 'vscode';

export enum Position {
    Start,
    End,
}

export type LineMap = Map<number, LineInfo>;

export type StmtSpan = {
    file: string | null;
    start_line: number;
    start_col: number;
    end_line: number;
    end_col: number;
};

export type LineInfo = {
    line: number;
    pos: Position;
    rcx: string;
    env: string;
};

// definitions per line
export type FluxDef = {
    fileName: string;
    line: number;
    column_start: number;
    column_end: number;
    target: vscode.Location;
};

// definitions per file, indexed by line number
export type FluxDefs = Map<number, FluxDef[]>;

export type LogInfo = {
    lineInfos: Map<string, LineInfo[]>;
    definitions: Map<string, FluxDefs>;
};

export type CheckMode = "All" | "Mod" | "Def" | "Off";

export enum DisplayState {
    None, // no info to display at current cursor position
    Loading, // running flux and waiting for results
    Info, // have info to display at current cursor position
}
