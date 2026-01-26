import type { RustcDiagnostic, RustcSpan } from "../types";

/**
 * Render a rustc diagnostic as plain text
 */
export function renderRustcDiagnostic(
    diagnostic: RustcDiagnostic,
    workspaceRoot?: string
): string {
    const message = diagnostic.message;
    let output = "";

    // Main diagnostic header
    const level = message.level.toUpperCase();
    const code = message.code?.code ? `[${message.code.code}]` : "";
    output += `${level}${code}: ${message.message}\n`;

    // Helper function to format file path
    const formatFilePath = (fileName: string): string => {
        if (workspaceRoot && fileName.startsWith(workspaceRoot)) {
            return fileName.substring(workspaceRoot.length + 1);
        }
        return fileName;
    };

    // Helper function to render a span with its context
    const renderSpan = (span: RustcSpan, indent: string = ""): string => {
        let spanOutput = "";

        if (span.file_name) {
            const filePath = formatFilePath(span.file_name);
            spanOutput += `${indent}--> ${filePath}:${span.line_start}:${span.column_start}\n`;

            // Add the source code lines if available
            if (span.text && span.text.length > 0) {
                const lineNumWidth = span.line_end.toString().length;

                span.text.forEach((textLine, index) => {
                    const lineNum = span.line_start + index;
                    const lineNumStr = lineNum.toString().padStart(lineNumWidth, " ");

                    spanOutput += `${indent}${lineNumStr} | ${textLine.text}\n`;

                    // Add highlighting if this line has highlights
                    if (textLine.highlight_start !== textLine.highlight_end) {
                        const highlightLine = " ".repeat(lineNumWidth + 3); // padding for line number and " | "
                        const beforeHighlight = " ".repeat(textLine.highlight_start);
                        const highlightLength =
                            textLine.highlight_end - textLine.highlight_start;
                        const highlight = "^".repeat(Math.max(1, highlightLength));

                        spanOutput += `${indent}${highlightLine}${beforeHighlight}${highlight}`;

                        // Add label if available
                        if (span.label) {
                            spanOutput += ` ${span.label}`;
                        }
                        spanOutput += "\n";
                    }
                });
            }
        }

        return spanOutput;
    };

    // Process primary spans first
    const primarySpans = message.spans.filter((span) => span.is_primary);
    const secondarySpans = message.spans.filter((span) => !span.is_primary);

    // Render primary spans
    primarySpans.forEach((span) => {
        output += renderSpan(span);
    });

    // Render secondary spans if any
    secondarySpans.forEach((span) => {
        output += renderSpan(span, "   ");
    });

    // Process child messages (notes, helps, etc.)
    message.children.forEach((child) => {
        output += "\n";
        const childLevel =
            child.level === "note"
                ? "note"
                : child.level === "help"
                    ? "help"
                    : child.level;
        output += `${childLevel}: ${child.message}\n`;

        // Render child spans
        child.spans.forEach((span) => {
            if (span.is_primary && span.file_name) {
                output += renderSpan(span, "   ");
            }
        });
    });

    // Add suggestion if available
    const suggestionSpans = message.spans.filter(
        (span) => span.suggested_replacement
    );
    if (suggestionSpans.length > 0) {
        output += "\nhelp: try this\n";
        suggestionSpans.forEach((span) => {
            if (span.suggested_replacement) {
                output += `   ${span.suggested_replacement}\n`;
            }
        });
    }

    // If we have a pre-rendered version, prefer that for ANSI formatting
    if (message.rendered) {
        // Strip ANSI codes for pure text output
        const cleanRendered = message.rendered
            .replace(/\x1b\[[0-9;]*m/g, "") // Remove ANSI escape codes
            .replace(/\r\n/g, "\n") // Normalize line endings
            .trim();

        if (cleanRendered.length > output.length) {
            return cleanRendered;
        }
    }

    return output.trim();
}
