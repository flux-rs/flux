import * as path from "path";
import * as vscode from "vscode";
import { renderRustcDiagnostic, updateDiagnosticsFromRustc } from "../diagnostics";
import { parseLogInfo } from "../parsing";
import type {
    CheckMode,
    FluxDef,
    FluxDefs,
    KvarDefs,
    LineInfo,
    LineMap,
    Position
} from "../types";
import { getFileModificationTime, runCargoFlux, runTouch } from "../utils";

/**
 * Manages flux trace data, diagnostics, and line info
 */
export class InfoProvider {
    constructor(
        private readonly _workspacePath: string,
        private readonly _diagnosticCollection: vscode.DiagnosticCollection,
        private readonly _statusBarItem: vscode.StatusBarItem,
        private readonly _diagnosticDetailsMap: Map<string, any>
    ) { }

    private _StartMap: Map<string, LineMap> = new Map();
    private _EndMap: Map<string, LineMap> = new Map();
    private _ModifiedAt: Map<string, Date> = new Map();
    private _definitions: Map<string, FluxDefs> = new Map();
    private _kvarDefs: Map<string, KvarDefs> = new Map();

    currentFile?: string;
    currentLine: number = 0;
    currentColumn: number = 0;
    currentPosition: Position = 0; // Position.End

    relativeFile(file: string): string {
        return path.relative(this._workspacePath, file);
    }

    public setPosition(
        file: string,
        line: number,
        column: number,
        text: string
    ) {
        this.currentFile = file;
        this.currentLine = line;
        this.currentColumn = column;
        // Position.Start = 0, Position.End = 1
        this.currentPosition = text.slice(0, column - 1).trim() === "" ? 0 : 1;
    }

    // for the `Start` map we want the _first_ event for that line, while for the `End` map we want the _last_ event,
    // so we need to _reverse_ the array for the `Start` map
    private positionMap(info: LineInfo[], pos: Position): LineMap {
        if (pos === 0) {
            // Position.Start
            info = info.slice().reverse();
        }
        return new Map(
            info.filter((item) => item.pos === pos).map((item) => [item.line, item])
        );
    }

    private updateInfo(fileName: string, fileInfo: LineInfo[]) {
        const startMap = this.positionMap(fileInfo, 0); // Position.Start
        const endMap = this.positionMap(fileInfo, 1); // Position.End
        this._StartMap.set(fileName, startMap);
        this._EndMap.set(fileName, endMap);
    }

    public getDefinition(
        fileName: string,
        line: number,
        column: number
    ): FluxDef | undefined {
        const fileDefs = this._definitions.get(fileName);
        if (fileDefs) {
            const lineDefs = fileDefs.get(line);
            if (lineDefs) {
                return lineDefs.find(
                    (def) => def.column_start <= column && column <= def.column_end
                );
            }
        }
        return undefined;
    }

    public getLineInfo(): LineInfo | "loading" | undefined {
        const file = this.currentFile;
        const pos = this.currentPosition;
        const line = this.currentLine;
        const map = pos === 0 ? this._StartMap : this._EndMap; // Position.Start : Position.End
        if (file) {
            const fileInfo = map.get(file);
            if (fileInfo) {
                let lineInfo = fileInfo.get(line);
                return lineInfo;
            } else {
                return "loading";
            }
        }
    }

    /**
     * Helper function to render KvarApp
     */
    public renderKvarApp(app: { kvar: string; args: string[] }): string {
        const raw = `${app.kvar}(|${app.args.join(", ")}|)`;
        return `<span class="kvar-app" title="donald-mouse"><b>${raw}</b></span>`;
    }


    public getLine(): number {
        return this.currentLine;
    }

    private modeIncludeValue(mode: CheckMode): string {
        var file = this.currentFile;
        if (file) {
            file = this.relativeFile(file);
        }

        switch (mode) {
            case "All":
                return "*"; // full globset pattern;
            case "Mod":
                return file || "*";
            case "Def":
                if (file) {
                    return `span:${file}:${this.currentLine}:${this.currentColumn}`;
                } else {
                    return "*";
                }
            case "Off":
                return "[]"; // empty globset pattern;
        }
    }

    public async runFlux(
        uri: vscode.Uri,
        file: string,
        trace: boolean,
        checkMode: CheckMode,
        beforeLoad: () => void
    ) {
        if (!file.endsWith(".rs")) {
            return;
        }
        const workspacePath = this._workspacePath;
        const src = this.relativeFile(file);
        const lastFluxAt = this._ModifiedAt.get(src);
        const lastModifiedAt = getFileModificationTime(file);

        if (lastFluxAt === lastModifiedAt) {
            return;
        }

        // remove information for this file
        this._StartMap.delete(src);
        this._EndMap.delete(src);
        beforeLoad();
        // run touch, cargo flux and load the new info
        await runTouch(src);
        const curAt = getFileModificationTime(file);
        this._ModifiedAt.set(src, curAt);
        const includeValue = this.modeIncludeValue(checkMode);
        // note we use `file` for the ABSOLUTE path due to odd cargo workspace behavior
        await runCargoFlux(
            workspacePath,
            file,
            trace,
            includeValue,
            this._statusBarItem
        ).then((rustcOutput) => {
            updateDiagnosticsFromRustc(
                this._diagnosticCollection,
                rustcOutput,
                workspacePath,
                this._diagnosticDetailsMap,
                renderRustcDiagnostic
            );
        });
    }

    public async loadFluxInfo() {
        try {
            const logInfo = await parseLogInfo();
            logInfo.lineInfos.forEach((lineInfo, fileName) => {
                this.updateInfo(fileName, lineInfo);
            });
            logInfo.definitions.forEach((fluxDefs, fileName) => {
                this._definitions.set(fileName, fluxDefs);
            });
            logInfo.kvarDefs.forEach((kvarDefs, fileName) => {
                this._kvarDefs.set(fileName, kvarDefs);
            });
        } catch (error) {
            vscode.window.showErrorMessage(`Failed to load line info: ${error}`);
        }
    }
}
