import * as vscode from "vscode";
import type { FluxViewProvider, InfoProvider } from "../providers";

/**
 * Command to toggle the Flux view panel
 */
export function registerToggleCommand(
    context: vscode.ExtensionContext,
    fluxViewProvider: FluxViewProvider,
    infoProvider: InfoProvider
): vscode.Disposable {
    return vscode.commands.registerCommand("Flux.toggle", () => {
        fluxViewProvider.toggle();
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            infoProvider.runFlux(context.extensionUri, editor.document.fileName, false, "All", () => {
                fluxViewProvider.updateView();
            });
        }
    });
}
