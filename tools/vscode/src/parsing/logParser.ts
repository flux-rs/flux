import * as path from "path";
import * as vscode from "vscode";
import type {
    Assignment,
    FluxDef,
    FluxDefs,
    Kvar,
    KvarDefs,
    KvarSol,
    LineInfo,
    LogInfo,
    StmtSpan
} from "../types";
import { readEventsStreaming } from "./eventReader";

const checkerPath = "log/checker";

/**
 * Helper function to update flux definitions map
 */
function updateFluxDefs(defs: Map<string, FluxDefs>, fluxDef: FluxDef) {
    if (!defs.has(fluxDef.fileName)) {
        defs.set(fluxDef.fileName, new Map());
    }
    let fileDefs = defs.get(fluxDef.fileName)!;
    if (!fileDefs.has(fluxDef.line)) {
        fileDefs.set(fluxDef.line, []);
    }
    let lineDefs = fileDefs.get(fluxDef.line)!;
    lineDefs.push(fluxDef);
}

function updateKvarDefs(defs: Map<string, KvarDefs>, kvarSol: KvarSol) {
    const fileName = kvarSol.span.file!;
    if (!defs.has(fileName)) {
        defs.set(fileName, new Map());
    }
    let fileKvarDefs = defs.get(fileName)!;
    for (let line = kvarSol.span.start_line; line <= kvarSol.span.end_line; line++) {
        fileKvarDefs.set(line, kvarSol);
    }
}

/**
 * Parse events with a custom parser function
 */
export async function parseEventsWith<T>(
    def: T,
    parser: (events: any[]) => T
): Promise<T> {
    try {
        // Get the workspace folder
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (!workspaceFolders) {
            return def;
        }
        // Read the file using VS Code's file system API
        const workspacePath = workspaceFolders[0].uri.fsPath;
        const logPath = path.join(workspacePath, checkerPath);
        const events = await readEventsStreaming(logPath);
        // Parse the events using the provided parser function
        const result = parser(events);
        return result;
    } catch (error) {
        // vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
        return def;
    }
}

/**
 * Parse the log file to extract line info and definitions
 */
export async function parseLogInfo(): Promise<LogInfo> {
    let def: LogInfo = { lineInfos: new Map(), definitions: new Map(), kvarDefs: new Map() };
    try {
        // Get the workspace folder
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (!workspaceFolders) {
            return def;
        }
        // Read the file using VS Code's file system API
        const workspacePath = workspaceFolders[0].uri.fsPath;
        const logPath = path.join(workspacePath, checkerPath);
        const events = await readEventsStreaming(logPath);

        events.forEach((event) => {
            // handle line-info events
            const lineInfo = parseLineInfo(event);
            if (lineInfo) {
                const [fileName, info] = lineInfo;
                if (!def.lineInfos.has(fileName)) {
                    def.lineInfos.set(fileName, []);
                }
                def.lineInfos.get(fileName)?.push(info);
            }

            // handle definition events
            const fluxDef = parseFluxDef(event);
            if (fluxDef) {
                updateFluxDefs(def.definitions, fluxDef);
            }

            // handle kvar-solution events
            const kvarSol = parseKvarSol(event);
            if (kvarSol) {
                updateKvarDefs(def.kvarDefs, kvarSol);
            }
        });

        return def;
    } catch (error) {
        // vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
        return def;
    }
}

/**
 * Parse a statement span from JSON string
 */
function parseStatementSpanJSON(span: string): StmtSpan | undefined {
    if (span) {
        return JSON.parse(span);
    }
    return undefined;
}




/**
 * Parse a line info event
 */
function parseLineInfo(event: any): [string, LineInfo] | undefined {
    try {
        // Import Position enum at runtime to avoid circular dependency
        const Position = require("../types").Position;
        const position =
            event.fields.event === "statement_start"
                ? Position.Start
                : event.fields.event === "statement_end"
                    ? Position.End
                    : undefined;
        if (position !== undefined && event.span.name === "refine") {
            const stmt_span = parseStatementSpanJSON(event.fields.stmt_span_json);
            if (stmt_span && stmt_span.file) {
                const info = {
                    line: stmt_span.end_line,
                    pos: position,
                    rcx: event.fields.rcx_json,
                    env: event.fields.env_json,
                };
                return [stmt_span.file, info];
            }
        }
    } catch (error) {
        console.log(`Failed to parse event: ${error}`);
    }
    return undefined;
}

/**
 * Parse a flux definition (hyperlink) event
 */
function parseFluxDef(event: any): FluxDef | undefined {
    if (event.fields && event.fields.event === "hyperlink") {
        try {
            const srcSpan = JSON.parse(event.fields.src_span) as StmtSpan;
            const dstSpan = JSON.parse(event.fields.dst_span) as StmtSpan;
            if (!srcSpan.file || !dstSpan.file) {
                console.log(`Invalid detached link: ${event.fields}`);
                return undefined; // Skip invalid links
            }
            // console.log(`Parsing flux hyperlink definition`, srcSpan, dstSpan);
            // Create the target location
            const targetUri = vscode.Uri.file(dstSpan.file);
            const targetRange = new vscode.Range(
                dstSpan.start_line - 1,
                dstSpan.start_col - 1,
                dstSpan.end_line - 1,
                dstSpan.end_col - 1
            );
            const targetLocation = new vscode.Location(targetUri, targetRange);

            const fluxDef: FluxDef = {
                fileName: srcSpan.file,
                line: srcSpan.start_line,
                column_start: srcSpan.start_col,
                column_end: srcSpan.end_col,
                target: targetLocation,
            };
            // console.log(`Found flux definition`, fluxDef);
            return fluxDef;
        } catch (error) {
            console.log(`Failed to parse definition event: ${error}`);
            return undefined;
        }
    }
    return undefined;
}

/*
{"timestamp":"2025-12-02T15:30:47.543583Z","level":"INFO","fields":{"event":"solution","span":"{\"file\":\"/Users/rjhala/research/flux-demo/src/basics.rs\",\"start_line\":125,\"start_col\":1,\"end_line\":128,\"end_col\":2}","solution":"[{\"name\":\"$k0\",\"args\":[\"b0\",\"b1\",\"b2\"],\"body\":{\"text\":\"∀b3. b0 = b3 ∧ b1 = a0 ∧ b2 = a1 ∧ b3 = (a1 ≥ a0) ∧ a1 ≥ 0 ∨ ∀b4. ¬(a1 ≥ 0) ∧ b0 = b4 ∧ b1 = a0 ∧ b2 = a1 ∧ b4 = false\",\"key\":null,\"children\":null}}]"},"target":"flux_refineck","span":{"name":"check_crate"},"spans":[{"name":"check_crate"}]}
*/

/**
 * Parse a flux definition (hyperlink) event
 */
function parseKvarSol(event: any): KvarSol | undefined {
    try {
        if (event.fields.event === "solution") {
            const stmt_span = parseStatementSpanJSON(event.fields.span);
            const raw_asgn = JSON.parse(event.fields.solution);
            const asgn: [Kvar, Assignment][] = raw_asgn.map((b: any) => ([b.name, { args: b.args, body: b.body.text }]));
            return { span: stmt_span!, asgn: new Map(asgn) };
        }
    } catch (error) {
        console.log(`Failed to parse event: ${error}`);
    }
    return undefined;
}