import anser from "anser";
import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";
import {
  FluxDefinitionProvider,
  FluxViewProvider,
  InfoProvider,
} from "./providers";
import type { RustcDiagnostic } from "./types";
import { killFluxProcess } from "./utils";

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

  let disposable = vscode.commands.registerCommand("Flux.toggle", () => {
    fluxViewProvider.toggle();
    const editor = vscode.window.activeTextEditor;
    if (editor) {
      infoProvider.runFlux(context.extensionUri, editor.document.fileName, false, "All", () => {
        fluxViewProvider.updateView();
      });
    }
  });
  context.subscriptions.push(disposable);

  // Register command to kill running flux process
  let killFluxCommand = vscode.commands.registerCommand("Flux.killProcess", () => {
    if (killFluxProcess()) {
      statusBarItem.hide();
      vscode.window.showInformationMessage("Flux process terminated");
    }
  });
  context.subscriptions.push(killFluxCommand);

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

  // Register command to show full diagnostic in webview
  let showDiagnosticCommand = vscode.commands.registerCommand("Flux.showDiagnostic", async (diagnosticUri: vscode.Uri) => {
    try {
      // Extract diagnostic ID from URI
      const diagnosticId = diagnosticUri.path.substring(1);
      const diagnostic = diagnosticDetailsMap.get(diagnosticId);

      if (!diagnostic) {
        vscode.window.showErrorMessage('Diagnostic not found');
        return;
      }

      // Create webview panel for better HTML rendering
      const panel = vscode.window.createWebviewPanel(
        'fluxDiagnostic',
        'Flux Compiler Diagnostic',
        vscode.ViewColumn.Beside,
        {
          enableScripts: false,
          retainContextWhenHidden: true
        }
      );

      const message = diagnostic.message;
      if (message.rendered) {
        // First escape HTML entities in the content, then convert ANSI to HTML
        // This prevents anser from treating < > as HTML tags
        const escapedContent = message.rendered
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;');

        // Convert ANSI escape codes to HTML to preserve formatting
        const htmlContent = anser.ansiToHtml(escapedContent);

        panel.webview.html = `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <style>
        body {
            font-family: var(--vscode-editor-font-family, 'SF Mono', Monaco, 'Cascadia Code', 'Roboto Mono', Consolas, 'Courier New', monospace);
            font-size: var(--vscode-editor-font-size, 13px);
            line-height: 1.4;
            color: var(--vscode-editor-foreground);
            background-color: var(--vscode-editor-background);
            margin: 0;
            padding: 16px;
            white-space: pre-wrap;
            word-wrap: break-word;
        }
        .diagnostic-header {
            border-bottom: 2px solid var(--vscode-panel-border);
            padding-bottom: 8px;
            margin-bottom: 16px;
            font-weight: bold;
            color: var(--vscode-textLink-foreground);
        }
        .diagnostic-content {
            font-family: inherit;
        }
        /* ANSI color classes that anser.ansiToHtml() generates - using VS Code theme colors */
        .ansi-black-fg { color: var(--vscode-terminal-ansiBlack, #000000); }
        .ansi-red-fg { color: var(--vscode-terminal-ansiRed, #cd3131); }
        .ansi-green-fg { color: var(--vscode-terminal-ansiGreen, #0dbc79); }
        .ansi-yellow-fg { color: var(--vscode-terminal-ansiYellow, #e5e510); }
        .ansi-blue-fg { color: var(--vscode-terminal-ansiBlue, #2472c8); }
        .ansi-magenta-fg { color: var(--vscode-terminal-ansiMagenta, #bc3fbc); }
        .ansi-cyan-fg { color: var(--vscode-terminal-ansiCyan, #11a8cd); }
        .ansi-white-fg { color: var(--vscode-terminal-ansiWhite, #e5e5e5); }
        .ansi-bright-black-fg { color: var(--vscode-terminal-ansiBrightBlack, #666666); }
        .ansi-bright-red-fg { color: var(--vscode-terminal-ansiBrightRed, #f14c4c); }
        .ansi-bright-green-fg { color: var(--vscode-terminal-ansiBrightGreen, #23d18b); }
        .ansi-bright-yellow-fg { color: var(--vscode-terminal-ansiBrightYellow, #f5f543); }
        .ansi-bright-blue-fg { color: var(--vscode-terminal-ansiBrightBlue, #3b8eea); }
        .ansi-bright-magenta-fg { color: var(--vscode-terminal-ansiBrightMagenta, #d670d6); }
        .ansi-bright-cyan-fg { color: var(--vscode-terminal-ansiBrightCyan, #29b8db); }
        .ansi-bright-white-fg { color: var(--vscode-terminal-ansiBrightWhite, #ffffff); }
        .ansi-bold { font-weight: bold; }
        .ansi-underline { text-decoration: underline; }
        .ansi-italic { font-style: italic; }
    </style>
</head>
<body>
${htmlContent}
</body>
</html>`;
      } else {
        // Fallback to plain text
        const plainText = `Full Flux Compiler Diagnostic

${message.level.toUpperCase()}: ${message.message}

${message.spans.map(span =>
          `  --> ${span.file_name}:${span.line_start}:${span.column_start}
${span.text?.map(text => `   | ${text.text}`).join('\n') || ''}
${span.label ? `   = ${span.label}` : ''}`
        ).join('\n\n')}

${message.children.map(child =>
          `${child.level}: ${child.message}`
        ).join('\n')}`;

        panel.webview.html = `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <style>
        body {
            font-family: 'SF Mono', Monaco, 'Cascadia Code', 'Roboto Mono', Consolas, 'Courier New', monospace;
            font-size: 13px;
            line-height: 1.4;
            color: #d4d4d4;
            background-color: #1e1e1e;
            margin: 0;
            padding: 16px;
            white-space: pre-wrap;
        }
    </style>
</head>
<body>${plainText.replace(/\n/g, '<br>')}</body>
</html>`;
      }
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to show diagnostic: ${error}`);
    }
  });
  context.subscriptions.push(showDiagnosticCommand);


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