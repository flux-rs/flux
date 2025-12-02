import * as path from "path";
import * as vscode from "vscode";
import type {
    FluxDef,
    FluxDefs,
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
            const lineInfo = parseEvent(event);
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
function parseEvent(event: any): [string, LineInfo] | undefined {
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
