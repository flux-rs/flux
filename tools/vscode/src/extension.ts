import * as vscode from "vscode";
import {
  registerKillProcessCommand,
  registerShowDiagnosticCommand,
  registerToggleCommand,
} from "./commands";
import {
  FluxDefinitionProvider,
  FluxViewProvider,
  InfoProvider,
} from "./providers";
import { registerEventListeners, setupFileWatcher } from "./setup";
import type { RustcDiagnostic } from "./types";

const checkerPath = "log/checker";

// Global map to store diagnostic details for the TextDocumentContentProvider
const diagnosticDetailsMap = new Map<string, RustcDiagnostic>();

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

  const workspaceFolders = vscode.workspace.workspaceFolders;
  if (!workspaceFolders) {
    return [];
  }

  // This line of code wll only be executed once when your extension is activated
  const workspacePath = workspaceFolders[0].uri.fsPath;
  console.log('Extension "flux" is now active in workspace:', workspacePath);

  const diagnosticCollection = vscode.languages.createDiagnosticCollection('flux');

  // Create status bar item for flux operations
  const statusBarItem = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 100);
  statusBarItem.hide(); // Initially hidden
  context.subscriptions.push(statusBarItem);

  const infoProvider = new InfoProvider(workspacePath, diagnosticCollection, statusBarItem, diagnosticDetailsMap);
  const fluxViewProvider = new FluxViewProvider(
    context.extensionUri,
    infoProvider,
  );

  // Register commands
  context.subscriptions.push(
    registerToggleCommand(context, fluxViewProvider, infoProvider),
    registerKillProcessCommand(statusBarItem),
    registerShowDiagnosticCommand(diagnosticDetailsMap)
  );

  // Register webview provider
  context.subscriptions.push(
    vscode.window.registerWebviewViewProvider("fluxView", fluxViewProvider)
  );

  // Register definition provider
  const fluxDefinitionProvider = new FluxDefinitionProvider(infoProvider, context);
  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(
      { scheme: 'file', language: 'rust' },
      fluxDefinitionProvider
    )
  );

  // Register event listeners for document and editor changes
  registerEventListeners(context, fluxViewProvider);

  // Setup file watcher for flux checker log
  setupFileWatcher(workspacePath, checkerPath, () => {
    infoProvider.loadFluxInfo()
      .then(() => fluxViewProvider.updateView());
  });
}

// This method is called when your extension is deactivated
export function deactivate() { }