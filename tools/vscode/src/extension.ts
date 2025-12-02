import anser from "anser";
import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";
import {
  renderRustcDiagnostic,
  updateDiagnosticsFromRustc,
} from "./diagnostics";
import { parseEnv, parseLogInfo, parseRcx } from "./parsing";
import {
  CheckMode,
  DisplayState,
  FluxDef,
  FluxDefs,
  KvarApp,
  LineInfo,
  LineMap,
  NestedString,
  Position,
  Rcx,
  RustcDiagnostic,
  TypeEnv
} from "./types";
import {
  escapeHtml,
  getFileModificationTime,
  killFluxProcess,
  runCargoFlux,
  runTouch,
} from "./utils";

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

  const infoProvider = new InfoProvider(workspacePath, diagnosticCollection, statusBarItem);
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

class FluxDefinitionProvider implements vscode.DefinitionProvider {

  constructor(
    private readonly _infoProvider: InfoProvider,
    private readonly _context: vscode.ExtensionContext
  ) { }

  provideDefinition(document: vscode.TextDocument, position: vscode.Position, token: vscode.CancellationToken): vscode.ProviderResult<vscode.Definition | vscode.DefinitionLink[]> {
    const fileName = document.fileName;

    // Convert VS Code 0-based position to 1-based line/column for flux
    const line = position.line + 1;
    const column = position.character + 1;

    // Look up the definition using the info provider
    const fluxDef = this._infoProvider.getDefinition(fileName, line, column);

    if (fluxDef) {
      // Create the source range for the definition link
      const originSelectionRange = new vscode.Range(
        fluxDef.line - 1,  // Convert back to 0-based
        fluxDef.column_start - 1,  // Convert back to 0-based
        fluxDef.line - 1,
        fluxDef.column_end - 1
      );

      // Create a DefinitionLink with both source and target information
      const definitionLink: vscode.DefinitionLink = {
        originSelectionRange: originSelectionRange,
        targetUri: fluxDef.target.uri,
        targetRange: fluxDef.target.range,
        targetSelectionRange: fluxDef.target.range  // Use the same range for selection
      };

      return [definitionLink];
    }

    // Return undefined if no definition found
    return undefined;
  }

}

class InfoProvider {
  constructor(
    private readonly _workspacePath: string,
    private readonly _diagnosticCollection: vscode.DiagnosticCollection,
    private readonly _statusBarItem: vscode.StatusBarItem
  ) { }

  private _StartMap: Map<string, LineMap> = new Map();
  private _EndMap: Map<string, LineMap> = new Map();
  private _ModifiedAt: Map<string, Date> = new Map();
  private _definitions: Map<string, FluxDefs> = new Map();

  currentFile?: string;
  currentLine: number = 0;
  currentColumn: number = 0;
  currentPosition: Position = Position.End;

  relativeFile(file: string): string {
    return path.relative(this._workspacePath, file);
  }

  public setPosition(file: string, line: number, column: number, text: string) {
    this.currentFile = file;
    this.currentLine = line;
    this.currentColumn = column;
    this.currentPosition =
      text.slice(0, column - 1).trim() === "" ? Position.Start : Position.End;
  }

  // for the `Start` map we want the _first_ event for that line, while for the `End` map we want the _last_ event,
  // so we need to _reverse_ the array for the `Start` map
  private positionMap(info: LineInfo[], pos: Position): LineMap {
    if (pos === Position.Start) {
      info = info.slice().reverse();
    }
    return new Map(
      info.filter((item) => item.pos === pos).map((item) => [item.line, item]),
    );
  }

  private updateInfo(fileName: string, fileInfo: LineInfo[]) {
    const startMap = this.positionMap(fileInfo, Position.Start);
    const endMap = this.positionMap(fileInfo, Position.End);
    this._StartMap.set(fileName, startMap);
    this._EndMap.set(fileName, endMap);
  }

  public getDefinition(fileName: string, line: number, column: number): FluxDef | undefined {
    const fileDefs = this._definitions.get(fileName);
    if (fileDefs) {
      const lineDefs = fileDefs.get(line);
      if (lineDefs) {
        return lineDefs.find(def => def.column_start <= column && column <= def.column_end);
      }
    }
    return undefined;
  }

  public getLineInfo(): LineInfo | "loading" | undefined {
    const file = this.currentFile;
    const pos = this.currentPosition;
    const line = this.currentLine;
    const map = pos === Position.Start ? this._StartMap : this._EndMap;
    if (file) {
      const fileInfo = map.get(file);
      if (fileInfo) {
        let lineInfo = fileInfo.get(line);
        return lineInfo;
      } else {
        return "loading";
      }
    }
  }

  public getLine(): number {
    return this.currentLine;
  }

  private modeIncludeValue(mode: CheckMode): string {
    var file = this.currentFile;
    if (file) {
      file = this.relativeFile(file);
    }

    switch (mode) {
      case "All":
        return "*"; // full globset pattern;
      case "Mod":
        return file || "*";
      case "Def":
        if (file) {
          return `span:${file}:${this.currentLine}:${this.currentColumn}`;
        } else {
          return "*";
        }
      case "Off":
        return "[]"; // empty globset pattern;
    }
  }
  public async runFlux(uri: vscode.Uri, file: string, trace: boolean, checkMode: CheckMode, beforeLoad: () => void) {
    if (!file.endsWith(".rs")) {
      return;
    }
    const workspacePath = this._workspacePath;
    const src = this.relativeFile(file);
    const lastFluxAt = this._ModifiedAt.get(src);
    const lastModifiedAt = getFileModificationTime(file);

    if (lastFluxAt === lastModifiedAt) {
      return;
    }

    // remove information for this file
    this._StartMap.delete(src);
    this._EndMap.delete(src);
    beforeLoad();
    // run touch, cargo flux and load the new info
    await runTouch(src);
    const curAt = getFileModificationTime(file);
    this._ModifiedAt.set(src, curAt);
    const includeValue = this.modeIncludeValue(checkMode);
    // note we use `file` for the ABSOLUTE path due to odd cargo workspace behavior
    await runCargoFlux(workspacePath, file, trace, includeValue, this._statusBarItem).then(rustcOutput => {
      updateDiagnosticsFromRustc(this._diagnosticCollection, rustcOutput, workspacePath, diagnosticDetailsMap, renderRustcDiagnostic);
    });
  }

  public async loadFluxInfo() {
    try {
      const logInfo = await parseLogInfo();
      logInfo.lineInfos.forEach((lineInfo, fileName) => {
        this.updateInfo(fileName, lineInfo);
      });
      logInfo.definitions.forEach((fluxDefs, fileName) => {
        this._definitions.set(fileName, fluxDefs);
      });
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to load line info: ${error}`);
    }
  }
}

class FluxViewProvider implements vscode.WebviewViewProvider {
  private _view?: vscode.WebviewView;
  private _panel?: vscode.WebviewPanel;
  private _currentLine: number = 0;
  private _interactive: boolean = false;
  private _currentState: DisplayState = DisplayState.None;
  private _currentRcx: Rcx | undefined;
  private _currentEnv: TypeEnv | undefined;
  private _valuesExpanded: boolean = true;
  private _typesExpanded: boolean = true;
  private _constraintsExpanded: boolean = true;
  private _fontFamily: string | undefined = "Arial";
  private _fontSize: number | undefined = 14;
  private _checkMode: CheckMode = "All";
  private _checkTrace: boolean = false;

  constructor(
    private readonly _extensionUri: vscode.Uri,
    private readonly _infoProvider: InfoProvider,
  ) { }


  private show() {
    const panel = vscode.window.createWebviewPanel(
      "FluxInfoView",
      "Flux",
      vscode.ViewColumn.Beside,
      {
        enableScripts: true,
        retainContextWhenHidden: true,
      },
    );
    this._panel = panel;

    // Handle messages from the webview
    panel.webview.onDidReceiveMessage(
      (message) => {
        switch (message.command) {
          case "valuesClicked":
            this._valuesExpanded = !this._valuesExpanded;
            this.updateView();
            return;
          case "typesClicked":
            this._typesExpanded = !this._typesExpanded;
            this.updateView();
            return;
          case "constraintsClicked":
            this._constraintsExpanded = !this._constraintsExpanded;
            this.updateView();
            return;
          case "checkModeChanged":
            this._checkMode = message.mode;
            console.log(`Check mode changed to: ${this._checkMode}`);
            return;
          case "checkerTraceChanged":
            this._checkTrace = message.checked;
            console.log(`Checker trace changed to: ${this._checkTrace}`);
            return;
        }
      },
      undefined,
      undefined,
    );

    this._panel.onDidDispose(() => {
      this._panel = undefined;
    });
    this.updateView();
  }

  private hide() {
    if (this._panel) {
      this._panel.dispose();
      this._panel = undefined;
    }
  }

  public toggle() {
    if (this._panel) {
      this.hide();
    } else {
      this.show();
    }
  }

  public runFluxCheck(file: string) {
    this._infoProvider
      .runFlux(this._extensionUri, file, this._checkTrace, this._checkMode, () => {
        this.updateView();
      })
      .then(() => this._infoProvider.loadFluxInfo())
      .then(() => this.updateView());
  }

  public runFlux(file: string) {
    this.runFluxCheck(file);
  }

  public setPosition(editor: vscode.TextEditor) {
    const position = editor.selection.active;
    const fileName = editor.document.fileName;
    const line = editor.document.lineAt(position.line);
    this._infoProvider.setPosition(
      fileName,
      position.line + 1,
      position.character + 1,
      line.text,
    );
  }

  public updateView() {
    this._currentLine = this._infoProvider.getLine();
    const info = this._infoProvider.getLineInfo();
    if (info === "loading") {
      this._currentState = DisplayState.Loading;
    } else if (info) {
      this._currentState = DisplayState.Info;
      this._currentRcx = parseRcx(info.rcx);
      this._currentEnv = parseEnv(info.env);
    } else {
      this._currentState = DisplayState.None;
    }
    const config = vscode.workspace.getConfiguration("editor");
    this._fontFamily = config.get<string>("fontFamily");
    this._fontSize = config.get<number>("fontSize");
    const html = this._getHtmlForWebview();
    if (this._panel) {
      this._panel.webview.html = html;
    }
  }

  public resolveWebviewView(
    webviewView: vscode.WebviewView,
    context: vscode.WebviewViewResolveContext,
    _token: vscode.CancellationToken,
  ) {
    this._view = webviewView;
    webviewView.webview.options = {
      enableScripts: true,
      localResourceRoots: [this._extensionUri],
    };

    const config = vscode.workspace.getConfiguration("editor");
    this._fontFamily = config.get<string>("fontFamily");
    this._fontSize = config.get<number>("fontSize");
    webviewView.webview.html = this._getHtmlForWebview();
  }

  private _getHtmlForInfo() {
    let rcxBindings;
    if (this._valuesExpanded) {
      rcxBindings = this._currentRcx?.bindings
        .map((bind) => {
          const name =
            typeof bind.name === "string" ? bind.name : bind.name.join(" ");
          return `
            <tr>
                <td><b style="color: #F26123">${name}</b> : ${bind.sort} </td>
            </tr>
          `;
        })
        .join("");
    } else {
      rcxBindings = "";
    }

    let rcxExprs;
    if (this._constraintsExpanded) {
      rcxExprs = this._currentRcx?.exprs
        .map(
          (expr) => `
            <tr>
                <td>${nestedStringHtml(expr)}</td>
            </tr>
          `,
        )
        .join("");
    } else {
      rcxExprs = "";
    }

    let envBindings;
    if (this._typesExpanded) {
      envBindings = this._currentEnv
        ?.map(
          (bind) => `
            <tr>
                <td style="vertical-align: top;"><b style="color: #F26123">${bind.name}</b></td>
                <td>${nestedStringHtml(bind.ty)}</td>
            </tr>
          `,
        )
        .join("");
    } else {
      envBindings = "";
    }

    const valuesExpanded = this._valuesExpanded ? "expanded" : "";
    const constraintsExpanded = this._constraintsExpanded ? "expanded" : "";
    const typesExpanded = this._typesExpanded ? "expanded" : "";

    return `
                    <table style="border-collapse: collapse">
                    <tr>
                      <th style="color: green">
                        <div class="node toggleable ${valuesExpanded}" id="values-toggle">Values</div>
                      </th>
                    </tr>
                    ${rcxBindings}
                    </table>

                    <br>

                    <table>

                    <tr>
                      <th style="color: purple">
                        <div class="node toggleable ${constraintsExpanded}" id="constraints-toggle">Constraints</div>
                      </th>
                    </tr>
                    ${rcxExprs}
                    </table>

                    <br>

                    <table style="border-collapse: collapse">
                    <tr>
                      <th style="color: blue">
                        <div class="node toggleable ${typesExpanded}" id="types-toggle">Types</div>
                      </th>
                    </tr>
                    ${envBindings}
                    </table>
                `;
  }

  private _getHtmlForMessage(message: string) {
    return `
                    <table style="border-collapse: collapse">
                    <tr>
                      <th>${message}</th>
                    </tr>
                    </table>
                `;
  }

  private _getHtmlForWebview() {
    let body: string;
    if (this._currentState === DisplayState.Info) {
      body = this._getHtmlForInfo();
    } else if (this._currentState === DisplayState.Loading) {
      if (this._checkTrace) {
        body = this._getHtmlForMessage("Loading...");
      } else {
        body = this._getHtmlForMessage("<trace disabled>");
      }
    } else {
      body = this._getHtmlForMessage("No info available");
    }

    return `
            <!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>Flux</title>
                <style>
                    body {
                        display: flex;
                        align-items: left;
                        height: 100%;
                        margin: 0;
                        font-family: ${this._fontFamily};
                        font-size: ${this._fontSize};
                        background-color: var(--vscode-editor-background);
                    }
                    #cursor-position {
                        font-size: ${this._fontSize};
                    }
                    table, th, td {
                        border: 0px solid black;
                        border-collapse: collapse;
                    }
                    th, td {
                      padding: 5px;
                    }
                    th {
                      text-align: left;
                    }
                .node {
                    position: relative;
                    cursor: pointer;
                    user-select: none;
                }
                .node.toggleable {
                    padding-left: 10px;
                }
                .node.toggleable::before {
                    content: '▶';
                    position: absolute;
                    left: 0;
                    top: 0;
                    color: #888;
                    transition: transform 0.2s;
                    display: inline-block;
                    margin-right: 5px;
                }

                .node:not(.toggleable)::before {
                    content: none;
                }

                .node.toggleable.expanded::before {
                    transform: rotate(90deg);
                }

                .object-key {
                    margin-left: 5px;
                    /* Add a small margin to separate key from arrow */
                }

                .node-label {
                    color: #000;
                }

                .node-label.has-children {
                    color: #0000FF;
                    /* Classic console object color */
                }

                .children {
                    display: none;
                    margin-left: 2px;
                    border-left: 1px solid #ddd;
                    padding-left: 2px;
                }

                .node.expanded>.children {
                    display: block;
                }
                .children>.node {
                    margin-top: 5px;
                    padding-left: 10px;
                }
                .primitive {
                    color: #006400;
                    /* Dark green for primitive values */
                }

                .object-key {
                    color: #0000FF;
                    /* Blue for object keys */
                }

                .control-row {
                    display: flex;
                    align-items: center;
                    justify-content: flex-start;
                    width: 100%;
                    padding: 10px 0;
                    background-color: var(--vscode-editor-background);
                    border-bottom: 1px solid var(--vscode-panel-border);
                    gap: 15px;
                }

                .four-state-switch {
                  display: flex;
                  background-color: var(--vscode-input-background);
                  border: 1px solid var(--vscode-input-border);
                  border-radius: 8px;
                  height: 32px;
                  position: relative;
                  gap: 2px;
                  padding: 2px;
                  flex: 1;
                  max-width: 200px;
                  min-width: 160px;
                }
                .four-state-option {
                  flex: 1;
                  background: none;
                  border: none;
                  padding: 8px 12px;
                  font-size: 12px;
                  font-weight: 500;
                  color: var(--vscode-foreground);
                  cursor: pointer;
                  transition: all 0.2s ease;
                  z-index: 2;
                  position: relative;
                  border-radius: 6px;
                  min-width: 0;
                  display: flex;
                  align-items: center;
                  justify-content: center;
                  text-align: center;
                  white-space: nowrap;
                }
                .four-state-option.active {
                  color: var(--vscode-button-foreground);
                  background-color: var(--vscode-button-background);
                  font-weight: 600;
                }
                .four-state-option:hover:not(.active) {
                  background-color: var(--vscode-button-hoverBackground);
                  opacity: 0.7;
                }

                .checker-trace-container {
                  display: flex;
                  align-items: center;
                  gap: 8px;
                  margin-left: 15px;
                }

                .checker-trace-checkbox {
                  margin: 0;
                  cursor: pointer;
                }

                .checker-trace-label {
                  font-size: 12px;
                  font-weight: 500;
                  color: var(--vscode-foreground);
                  cursor: pointer;
                  user-select: none;
                  white-space: nowrap;
                }
                </style>
            </head>
            <body>

              <div id="cursor-position">
                <table style="border-collapse: collapse">
                  <tr>
                    <td colspan="2">
                      <div class="control-row">
                        <div class="four-state-switch" id="check-mode-switch">
                          <button class="four-state-option active" data-mode="All" title="Check entire crate">All</button>
                          <button class="four-state-option" data-mode="Mod" title="Only check current file">Mod</button>
                          <button class="four-state-option" data-mode="Def" title="Only check current function definition">Def</button>
                          <button class="four-state-option" data-mode="Off" title="Disable checking">Off</button>
                        </div>
                        <div class="checker-trace-container">
                          <input type="checkbox" id="checker-trace-checkbox" class="checker-trace-checkbox" ${this._checkTrace ? 'checked' : ''}>
                          <label for="checker-trace-checkbox" class="checker-trace-label">trace</label>
                        </div>
                      </div>
                    </td>
                  </tr>

                  <tr>
                    <th>Line</th><td>${this._currentLine}</td>
                  </tr>
                </table>

                    <br>

                    <div>${body}</div>

                </div>
	        <script>

            const vscode = acquireVsCodeApi();

            document.addEventListener('DOMContentLoaded', () => {
                const toggleables = document.querySelectorAll('.toggleable');
                toggleables.forEach((element, index) => {
                    element.addEventListener('click', (e) => {
                        e.stopPropagation();
                        element.classList.toggle('expanded');
                    });
                    if (element.id == "values-toggle") {
                       element.addEventListener('click', () => {
                          console.log("values toggled!");
                          vscode.postMessage({
                            command: 'valuesClicked',
                          });
                       });
                    };
                    if (element.id == "constraints-toggle") {
                       element.addEventListener('click', () => {
                          console.log("constraints toggled!");
                          vscode.postMessage({
                            command: 'constraintsClicked',
                          });
                       });
                    };
                    if (element.id == "types-toggle") {
                       element.addEventListener('click', () => {
                          console.log("types toggled!");
                          vscode.postMessage({
                            command: 'typesClicked',
                          });
                       });
                    };
                });
            });


            // Four-state switch functionality
            const checkModeSwitch = document.getElementById('check-mode-switch');
            const checkModeOptions = checkModeSwitch.querySelectorAll('.four-state-option');

            const currentCheckMode = "${this._checkMode}";

            // Set initial state
            checkModeOptions.forEach((option) => {
                if (option.dataset.mode === currentCheckMode) {
                    option.classList.add('active');
                } else {
                    option.classList.remove('active');
                }
            });

            // Add click handlers
            checkModeOptions.forEach((option) => {
                option.addEventListener('click', () => {
                    checkModeOptions.forEach(opt => opt.classList.remove('active'));
                    option.classList.add('active');

                    vscode.postMessage({
                        command: 'checkModeChanged',
                        mode: option.dataset.mode
                    });
                });
            });

            // Checker trace checkbox functionality
            const checkerTraceCheckbox = document.getElementById('checker-trace-checkbox');
            checkerTraceCheckbox.addEventListener('change', (event) => {
                vscode.postMessage({
                    command: 'checkerTraceChanged',
                    checked: event.target.checked
                });
            });
            </script>
            </body>
            </html>
        `;
  }
}

/**********************************************************************************************/

// Sample data (you'd typically get this from somewhere else)
const sampleData: NestedString = {
  key: "",
  text: "{..}",
  children: [
    {
      key: "f1",
      text: "10",
    },
    {
      key: "f2",
      text: "20",
    },
    {
      key: "f3",
      text: "{..}",
      children: [
        { key: "f4", text: "30" },
        { key: "f5", text: "40" },
      ],
    },
  ],
};

function renderKvarApp(app: KvarApp): string {
  const raw = `${app.kvar}(|${app.args.join(', ')}|)`;
  return `<span class="kvar-app" title="mickey-mouse"><b>${raw}</b></span>`;
}

function renderText(text: string): string {
  // Replace patterns like ##[<s_0>##<s_1>##...##<s_n>]## with <s_0>(<s_1>, ..., <s_n>)
  return text.replace(/##\[([^\]]+)\]##/g, (match, content) => {
    const parts = content.split('##');
    if (parts.length === 0) {
      return match; // Return original if empty
    }
    const kvarApp: KvarApp = { kvar: parts[0], args: parts.slice(1) };
    return renderKvarApp(kvarApp);
  });
}

function nestedStringHtml(node: NestedString): string {
  const hasChildren = node.children && node.children.length > 0;
  const toggleable = hasChildren ? "toggleable" : "";
  const labelclass = hasChildren ? " has-children" : " primitive";
  const keyText = node.key ? node.key + ": " : "";
  // const labelText = escapeHtml(keyText + renderText(node.text));
  const labelText = keyText + renderText(escapeHtml(node.text));

  let childrenHtml = "";
  if (node.children) {
    const childrenElements = node.children
      .map((child) => nestedStringHtml(child))
      .join("");
    childrenHtml = `<div class="children">${childrenElements}</div>`;
  }

  hasChildren
    ? node.children?.map((child) => nestedStringHtml(child)).join("")
    : "";
  const html = `
        <div class="node ${toggleable}">
            <span class="node-label ${labelclass}">${labelText}</span>
            ${childrenHtml}
        </div>
        `;
  return html;
}

/**********************************************************************************************/
// Using KVar Solutions to translate Exprs
/**********************************************************************************************/