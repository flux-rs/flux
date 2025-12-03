import * as vscode from "vscode";
import type { RustcDiagnostic, RustcMessage, RustcSpan } from "../types";

/**
 * Convert rustc severity level to VS Code DiagnosticSeverity
 */
function convertSeverity(level: string): vscode.DiagnosticSeverity {
    switch (level) {
        case "error":
        case "ice": // Internal Compiler Error
            return vscode.DiagnosticSeverity.Error;
        case "warning":
            return vscode.DiagnosticSeverity.Warning;
        case "note":
        case "help":
            return vscode.DiagnosticSeverity.Information;
        case "failure-note":
        default:
            return vscode.DiagnosticSeverity.Hint;
    }
}

/**
 * Convert rustc 1-based position to VS Code 0-based position
 */
function convertPosition(line: number, character: number): vscode.Position {
    // Convert from rustc's 1-based line/column to VS Code's 0-based
    return new vscode.Position(Math.max(0, line - 1), Math.max(0, character - 1));
}

/**
 * Convert rustc span to VS Code range
 */
function convertRange(span: RustcSpan): vscode.Range {
    const start = convertPosition(span.line_start, span.column_start);
    const end = convertPosition(span.line_end, span.column_end);
    return new vscode.Range(start, end);
}

/**
 * Convert child messages to VS Code related information
 */
function convertRelatedInformation(
    children: RustcMessage[],
    workspaceRoot?: string
): vscode.DiagnosticRelatedInformation[] {
    const related: vscode.DiagnosticRelatedInformation[] = [];

    for (const child of children) {
        for (const span of child.spans) {
            if (span.file_name && span.is_primary) {
                try {
                    const uri = vscode.Uri.file(
                        workspaceRoot ? workspaceRoot + "/" + span.file_name : span.file_name
                    );

                    const location = new vscode.Location(uri, convertRange(span));
                    const message = span.label || child.message;

                    related.push(
                        new vscode.DiagnosticRelatedInformation(location, message)
                    );
                } catch (error) {
                    // Skip invalid file paths
                    console.warn(
                        `Failed to create related information for ${span.file_name}:`,
                        error
                    );
                }
            }
        }
    }
    return related;
}

/**
 * Convert a single rustc diagnostic to VS Code diagnostic
 */
export function convertRustcDiagnostic(
    rustcDiag: RustcDiagnostic,
    workspaceRoot?: string,
    diagnosticDetailsMap?: Map<string, RustcDiagnostic>
): { uri: vscode.Uri; diagnostic: vscode.Diagnostic } | null {
    const message = rustcDiag.message;

    // Find the primary span (main location where the error occurs)
    const primarySpan = message.spans.find((span) => span.is_primary);
    if (!primarySpan) {
        // If no primary span, try to use the first span
        if (message.spans.length === 0) {
            return null;
        }
    }

    const span = primarySpan || message.spans[0];

    try {
        // Convert file path to URI
        const uri = vscode.Uri.file(workspaceRoot + "/" + span.file_name);
        const range = convertRange(span);

        // Create the diagnostic
        const diag = new vscode.Diagnostic(
            range,
            message.message,
            convertSeverity(message.level)
        );

        // Add error code if available
        if (message.code) {
            diag.code = message.code.explanation
                ? {
                    value: message.code.code,
                    target: vscode.Uri.parse(
                        `https://doc.rust-lang.org/error-index.html#${message.code.code}`
                    ),
                }
                : message.code.code;
        }

        // Set source
        diag.source = "flux";

        // Add related information from child messages
        const relatedInfo = convertRelatedInformation(
            message.children,
            workspaceRoot
        );
        if (relatedInfo.length > 0) {
            diag.relatedInformation = relatedInfo;
        }

        // Add tags for specific types of diagnostics
        const tags: vscode.DiagnosticTag[] = [];
        if (
            message.code?.code === "dead_code" ||
            message.message.includes("never read")
        ) {
            tags.push(vscode.DiagnosticTag.Unnecessary);
        }
        if (
            message.code?.code.startsWith("deprecated") ||
            message.message.includes("deprecated")
        ) {
            tags.push(vscode.DiagnosticTag.Deprecated);
        }
        if (tags.length > 0) {
            diag.tags = tags;
        }

        // Add link to full diagnostic if rendered content is available
        if (message.rendered && diagnosticDetailsMap) {
            // Generate a unique ID for this diagnostic
            const diagnosticId = `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

            // Store the diagnostic details for the content provider
            diagnosticDetailsMap.set(diagnosticId, rustcDiag);

            // Create command URI for the full diagnostic view
            const diagnosticUri = vscode.Uri.from({
                scheme: "command",
                path: "Flux.showDiagnostic",
                query: JSON.stringify([
                    vscode.Uri.from({
                        scheme: "flux-diagnostic",
                        path: `/${diagnosticId}`,
                        query: `file=${encodeURIComponent(span.file_name)}&line=${span.line_start}`,
                    }),
                ]),
            });

            // If there's already a code, preserve it, otherwise create a new code object
            const existingCode = message.code?.code;
            diag.code = {
                value /* existingCode || */: "Click for full flux diagnostic",
                target: diagnosticUri,
            };
        }

        return { uri, diagnostic: diag };
    } catch (error) {
        console.error("Failed to convert rustc diagnostic:", error, rustcDiag);
        return null;
    }
}

/**
 * Batch conversion function for multiple diagnostics
 */
export function convertRustcDiagnostics(
    rustcDiags: RustcDiagnostic[],
    workspaceRoot?: string,
    diagnosticDetailsMap?: Map<string, RustcDiagnostic>
): Map<string, vscode.Diagnostic[]> {
    const diagnosticsByFile = new Map<string, vscode.Diagnostic[]>();

    for (const rustcDiag of rustcDiags) {
        const converted = convertRustcDiagnostic(
            rustcDiag,
            workspaceRoot,
            diagnosticDetailsMap
        );
        if (converted) {
            const fileKey = converted.uri.toString();
            const existing = diagnosticsByFile.get(fileKey) || [];
            existing.push(converted.diagnostic);
            diagnosticsByFile.set(fileKey, existing);
        }
    }

    return diagnosticsByFile;
}

/**
 * Update VS Code diagnostics from rustc JSON output
 */
export function updateDiagnosticsFromRustc(
    diagnosticCollection: vscode.DiagnosticCollection,
    rustcOutput: string,
    workspaceRoot?: string,
    diagnosticDetailsMap?: Map<string, RustcDiagnostic>,
    renderDiagnostic?: (diag: RustcDiagnostic, workspaceRoot?: string) => string
): void {
    try {
        // Parse rustc JSON output (each line is a separate JSON object)
        const rustcDiagnostics: RustcDiagnostic[] = [];

        for (const line of rustcOutput.split("\n")) {
            if (line.trim()) {
                try {
                    const parsed = JSON.parse(line);
                    // Only process compiler messages (not build artifacts)
                    if (parsed.reason === "compiler-message" && parsed.message) {
                        // console.log(`TRACE: updateDiagnostics parsed:`, parsed);
                        const diag = {
                            message: parsed.message,
                            package_id: parsed.package_id,
                            manifest_path: parsed.manifest_path,
                            target: parsed.target,
                        };
                        if (renderDiagnostic) {
                            let str = renderDiagnostic(diag, workspaceRoot);
                            // console.log(`Parsed rustc diagnostic:\n ${str}`);
                        }
                        rustcDiagnostics.push(diag);
                    }
                } catch (parseError) {
                    console.warn("Failed to parse rustc output line:", line, parseError);
                }
            }
        }

        // Convert to VS Code diagnostics
        const diagnosticsByFile = convertRustcDiagnostics(
            rustcDiagnostics,
            workspaceRoot,
            diagnosticDetailsMap
        );

        // Clear existing diagnostics
        diagnosticCollection.clear();

        // Set new diagnostics
        for (const [uriString, diagnostics] of diagnosticsByFile) {
            const uri = vscode.Uri.parse(uriString);
            diagnosticCollection.set(uri, diagnostics);
        }
    } catch (error) {
        console.error("Failed to update diagnostics from rustc output:", error);
    }
}
