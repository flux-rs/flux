import * as fs from "fs";
import * as path from "path";
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

  /************************************************************/
  // Register a custom webview panel

  context.subscriptions.push(
    vscode.window.registerWebviewViewProvider("fluxView", fluxViewProvider),
  );

  // Listener to track cursor position
  context.subscriptions.push(
    vscode.window.onDidChangeTextEditorSelection((event) => {
      if (event.textEditor) {
        fluxViewProvider.setPosition(event.textEditor);
      }
      fluxViewProvider.updateView();
    }),
  );

  // Track the set of saved (updated) source files
  context.subscriptions.push(
    vscode.workspace.onDidSaveTextDocument((document) => {
      fluxViewProvider.runFlux(document.fileName);
    }),
  );

  // Track the set of opened files
  context.subscriptions.push(
    vscode.workspace.onDidOpenTextDocument((document) => {
      fluxViewProvider.runFlux(document.fileName);
    }),
  );

  const fluxDefinitionProvider = new FluxDefinitionProvider(infoProvider, context);
  context.subscriptions.push(
    vscode.languages.registerDefinitionProvider(
      { scheme: 'file', language: 'rust' },
      fluxDefinitionProvider
    )
  );

  // Reload the flux trace information for changedFiles
  const logFilePattern = new vscode.RelativePattern(workspacePath, checkerPath);

  // Delete the existing log file to avoid using stale data
  const logFilePath = path.join(workspacePath, checkerPath);
  try {
    if (fs.existsSync(logFilePath)) {
      fs.unlinkSync(logFilePath);
      console.log(`Deleted existing log file: ${logFilePath}`);
    }
  } catch (error) {
    console.warn(`Failed to delete log file ${logFilePath}:`, error);
  }

  const fileWatcher = vscode.workspace.createFileSystemWatcher(logFilePattern);
  console.log(`fileWatcher at:`, logFilePattern);

  fileWatcher.onDidChange((uri) => {
    console.log(`checker trace changed: ${uri.fsPath}`);
    infoProvider.loadFluxInfo()
      .then(() => fluxViewProvider.updateView());
  });
}

// Note: FluxDiagnosticContentProvider removed - now using WebView panel directly via command

// This method is called when your extension is deactivated
export function deactivate() { }

/**********************************************************************************************/
// Using KVar Solutions to translate Exprs
/**********************************************************************************************/