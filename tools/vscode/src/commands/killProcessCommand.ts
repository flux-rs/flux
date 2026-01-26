import * as vscode from "vscode";
import { killFluxProcess } from "../utils";

/**
 * Command to kill the running flux process
 */
export function registerKillProcessCommand(
    statusBarItem: vscode.StatusBarItem
): vscode.Disposable {
    return vscode.commands.registerCommand("Flux.killProcess", () => {
        if (killFluxProcess()) {
            statusBarItem.hide();
            vscode.window.showInformationMessage("Flux process terminated");
        }
    });
}
