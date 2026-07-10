import * as vscode from "vscode";

const outputChannel = vscode.window.createOutputChannel("Flux");

export function log(...args: any[]): void {
    outputChannel.appendLine(args.map(String).join(" "));
}

export function warn(...args: any[]): void {
    outputChannel.appendLine(`[WARN] ${args.map(String).join(" ")}`);
}

export function error(...args: any[]): void {
    outputChannel.appendLine(`[ERROR] ${args.map(String).join(" ")}`);
}
