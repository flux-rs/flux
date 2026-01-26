import * as vscode from "vscode";
import type { FluxViewProvider } from "../providers";

/**
 * Registers event listeners for document and editor changes
 */
export function registerEventListeners(
    context: vscode.ExtensionContext,
    fluxViewProvider: FluxViewProvider
): void {
    // Listener to track cursor position
    context.subscriptions.push(
        vscode.window.onDidChangeTextEditorSelection((event) => {
            if (event.textEditor) {
                fluxViewProvider.setPosition(event.textEditor);
            }
            fluxViewProvider.updateView();
        })
    );

    // Track the set of saved (updated) source files
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument((document) => {
            fluxViewProvider.runFlux(document.fileName);
        })
    );

    // Track the set of opened files
    context.subscriptions.push(
        vscode.workspace.onDidOpenTextDocument((document) => {
            fluxViewProvider.runFlux(document.fileName);
        })
    );
}
