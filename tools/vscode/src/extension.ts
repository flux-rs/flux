import anser from "anser";
import * as child_process from "child_process";
import * as fs from "fs";
import * as process from "node:process";
import * as path from "path";
import * as readline from "readline";
import { promisify } from "util";
import * as vscode from "vscode";

const checkerPath = "log/checker";

// Global variable to track the running flux process
let runningFluxProcess: child_process.ChildProcess | null = null;

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
    if (runningFluxProcess) {
      console.log("Killing running Flux process...");
      runningFluxProcess.kill('SIGTERM');
      runningFluxProcess = null;
      statusBarItem.hide();
      vscode.window.showInformationMessage("Flux process terminated");
    }
  });
  context.subscriptions.push(killFluxCommand);

  // Register command to show full diagnostic
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
      // Clean up the message to remove some redundant information
      if (message.rendered) {
        // Strip all ANSI escape codes and show plain text
        const plainText = anser.ansiToText(message.rendered)
          // Escape HTML entities for safety
          .replace(/&/g, '&amp;')
          .replace(/</g, '&lt;')
          .replace(/>/g, '&gt;')
          .replace(/"/g, '&quot;')
          .replace(/'/g, '&#39;');
        // const decolorized = anser.ansiToText(message.rendered);
        // const index = decolorized.match(/^(note|help):/m)?.index || decolorized.length;
        // const plainText = decolorized
        //   .substring(0, index)
        //   .replace(/^ -->[^\n]+\n/m, "")
        //   .trim();

        panel.webview.html = `<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
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
            word-wrap: break-word;
        }
        .diagnostic-header {
            border-bottom: 2px solid #3c3c3c;
            padding-bottom: 8px;
            margin-bottom: 16px;
            font-weight: bold;
            color: #569cd6;
        }
        .diagnostic-content {
            font-family: inherit;
        }
    </style>
</head>
<body>
    <div class="diagnostic-header">Full Blux Compiler Diagnostic</div>
    <div class="diagnostic-content">${plainText}</div>
</body>
</html>`;
      } else {
        // Fallback to plain text
        const plainText = `Full Klux Compiler Diagnostic

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

  // Register the diagnostic content provider
  const diagnosticContentProvider = new FluxDiagnosticContentProvider();
  context.subscriptions.push(
    vscode.workspace.registerTextDocumentContentProvider(
      FluxDiagnosticContentProvider.scheme,
      diagnosticContentProvider
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

// Promisify the exec function to use with await
const execPromise = promisify(child_process.exec);

async function runShellCommand(env: NodeJS.ProcessEnv, command: string): Promise<any> {
  const start = performance.now();
  try {
    console.log(`TRACE: Running command: ${command} flags=`, env.FLUXFLAGS);
    const { stdout, stderr } = await execPromise(command, {
      env: env,
      cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
    });

    const end = performance.now();
    console.log(`TRACE: Finish command: execution time: ${end - start} ms`);
    // Handle any output
    // if (stdout) { console.log(`Command stdout: ${stdout}`); }
    // if (stderr) { console.warn(`Command stderr: ${stderr}`); }

    return stdout.trim();
  } catch (error: any) {

    const end = performance.now();
    console.log(`TRACE: Finish command: execution time: ${end - start} ms`);
    // Even when the command fails, we can still get stdout and stderr
    const stdout = error.stdout || '';
    const stderr = error.stderr || '';
    const exitCode = error.code;

    console.log(`Command failed with exit code ${exitCode}`);
    // if (stdout) { console.log(`Command stdout: ${stdout}`); }
    // if (stderr) { console.warn(`Command stderr: ${stderr}`); }
    // Return stdout even on failure - useful for commands that output data but exit with non-zero
    return stdout.trim();
  }
}

function getFileModificationTime(filePath: string): Date {
  const stats = fs.statSync(filePath);
  return stats.mtime;
}

// Run `touch` on the file to force cargo/flux to re-run
async function runTouch(file: string) {
  const command = `touch ${file}`;
  await runShellCommand(process.env, command);
}

// run `cargo flux` on the file (absolute path)
async function runCargoFlux(workspacePath: string, file: string, trace: boolean, includeValue: string, statusBarItem: vscode.StatusBarItem): Promise<any> {
  // Show spinning indicator with clickable command
  statusBarItem.text = "$(sync~spin) Running Flux... (click to cancel)";
  statusBarItem.tooltip = "Flux type checker is running - Click to cancel";
  statusBarItem.command = "Flux.killProcess";
  statusBarItem.show();

  let fluxFlags = `-Finclude=${includeValue}`;
  if (trace) {
    fluxFlags += ` -Fdump-checker-trace=info`;
  } else {
    fluxFlags += ` -Fdump-checker-trace=warn`;
  }
  // console.log(`TRACE: Running command: cargo flux with flags=`, fluxFlags);

  return new Promise((resolve, reject) => {
    const fluxEnv = {
      ...process.env,
      FLUXFLAGS: fluxFlags,
    };

    // Get the flux command from workspace configuration
    const config = vscode.workspace.getConfiguration('flux');
    const baseCommand = config.get<string>('command', 'cargo flux');
    const commandArgs = `${baseCommand} --message-format=json-diagnostic-rendered-ansi`.split(' ');
    const command = commandArgs[0];
    const args = commandArgs.slice(1);

    const start = performance.now();
    console.log(`TRACE: Running command: ${command} ${args.join(' ')} flags=`, fluxEnv.FLUXFLAGS);

    // Use spawn to get a killable process reference
    runningFluxProcess = child_process.spawn(command, args, {
      env: fluxEnv,
      cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
      stdio: ['pipe', 'pipe', 'pipe']
    });

    let stdout = '';
    let stderr = '';

    runningFluxProcess.stdout?.on('data', (data) => {
      stdout += data.toString();
    });

    runningFluxProcess.stderr?.on('data', (data) => {
      stderr += data.toString();
    });

    runningFluxProcess.on('close', (code, signal) => {
      const end = performance.now();
      console.log(`TRACE: Finish command: execution time: ${end - start} ms`);

      runningFluxProcess = null;
      statusBarItem.hide();
      statusBarItem.command = undefined; // Remove click command

      if (signal === 'SIGTERM') {
        console.log('Flux process was terminated by user');
        resolve(''); // Return empty result when cancelled
        return;
      }

      if (code !== 0) {
        console.log(`Command failed with exit code ${code}`);
      }

      // if (stdout) { console.log(`Command stdout: ${stdout}`); }
      // if (stderr) { console.warn(`Command stderr: ${stderr}`); }

      // Return stdout even on failure - useful for commands that output data but exit with non-zero
      resolve(stdout.trim());
    });

    runningFluxProcess.on('error', (error) => {
      const end = performance.now();
      console.log(`TRACE: Finish command: execution time: ${end - start} ms`);

      runningFluxProcess = null;
      statusBarItem.hide();
      statusBarItem.command = undefined; // Remove click command

      console.error('Failed to start flux process:', error);
      reject(error);
    });
  });
}

// TextDocumentContentProvider for showing full diagnostic details
class FluxDiagnosticContentProvider implements vscode.TextDocumentContentProvider {
  private _onDidChange = new vscode.EventEmitter<vscode.Uri>();
  readonly onDidChange = this._onDidChange.event;

  static readonly scheme = 'flux-diagnostic';

  provideTextDocumentContent(uri: vscode.Uri): string {
    const diagnosticId = uri.path.substring(1); // Remove leading slash
    const diagnostic = diagnosticDetailsMap.get(diagnosticId);

    if (!diagnostic) {
      return 'Diagnostic not found';
    }

    const message = diagnostic.message;
    if (message.rendered) {
      const decolorized = anser.ansiToText(message.rendered);
      // const index = decolorized.match(/^(note|help):/m)?.index || decolorized.length;
      const plainText = decolorized
        //   .substring(0, index)
        .replace(/^ -->[^\n]+\n/m, "")
        .trim();

      const header = '=== Full Qlux Compiler Diagnostic ===\n\n';
      return header + plainText; // message.rendered;
    } else {
      // Fallback to plain text if no rendered content
      return `Full Flux Compiler Diagnostic

${message.level.toUpperCase()}: ${message.message}

${message.spans.map(span =>
        `  --> ${span.file_name}:${span.line_start}:${span.column_start}
${span.text?.map(text => `   | ${text.text}`).join('\n') || ''}
${span.label ? `   = ${span.label}` : ''}`
      ).join('\n\n')}

${message.children.map(child =>
        `${child.level}: ${child.message}`
      ).join('\n')}`;
    }
  }

  update(uri: vscode.Uri): void {
    this._onDidChange.fire(uri);
  }
}

// This method is called when your extension is deactivated
export function deactivate() { }

type LineMap = Map<number, LineInfo>;

enum Position {
  Start,
  End,
}

// definitions per line
type FluxDef = { fileName: string, line: number, column_start: number; column_end: number; target: vscode.Location };
// definitions per file, indexed by line number
type FluxDefs = Map<number, FluxDef[]>

function updateFluxDefs(defs: Map<string, FluxDefs>, fluxDef: FluxDef) {
  if (!defs.has(fluxDef.fileName)) {
    defs.set(fluxDef.fileName, new Map());
  }
  let fileDefs = defs.get(fluxDef.fileName)!;
  if (!fileDefs.has(fluxDef.line)) {
    fileDefs.set(fluxDef.line, []);
  }
  let lineDefs = fileDefs.get(fluxDef.line)!;
  lineDefs.push(fluxDef);
}

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
      updateDiagnosticsFromRustc(this._diagnosticCollection, rustcOutput, workspacePath);
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

enum DisplayState {
  None, // no info to display at current cursor position
  Loading, // running flux and waiting for results
  Info, // have info to display at current cursor position
}

function collapseBindings(bindings: RcxBind[]): RcxBind[] {
  let sort: string = "";
  let names: string[] = [];
  let binds: RcxBind[] = [];
  for (const bind of bindings) {
    if (typeof bind.name === "string") {
      if (bind.sort === sort) {
        // same sort as before
        names.push(bind.name);
      } else {
        // new sort
        if (names.length > 0) {
          binds.push({ name: names, sort: sort });
        }
        names = [bind.name];
        sort = bind.sort;
      }
    }
  }
  if (names.length > 0) {
    binds.push({ name: names, sort: sort });
  }
  return binds;
}

function parseRcx(rcx: string): Rcx {
  const rcxObj = JSON.parse(rcx);
  rcxObj.bindings = collapseBindings(rcxObj.bindings);
  rcxObj.exprs = rcxObj.exprs.map((s: any) => parseNestedString(s));
  return rcxObj;
}

function parseNestedString(s: string): NestedString {
  return JSON.parse(s);
}

function parseEnv(env: string): TypeEnv {
  return JSON.parse(env)
    .filter((bind: TypeEnvBind) => bind.name)
    .map((b: any) => {
      return {
        name: b.name,
        kind: b.kind,
        ty: parseNestedString(b.ty),
        span: b.span,
      };
    });
}

type CheckMode = "All" | "Mod" | "Def" | "Off";


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

async function readEventsStreaming(logPath: string): Promise<any[]> {
  const events: any[] = [];
  const fileStream = fs.createReadStream(logPath);

  // Create interface for reading line by line
  const rl = readline.createInterface({
    input: fileStream,
    crlfDelay: Infinity, // Recognize all instances of CR LF as a single line break
  });

  for await (const line of rl) {
    if (line.trim() === "") continue;

    try {
      events.push(JSON.parse(line));
    } catch (error) {
      // console.error(`Error parsing line: ${line.substring(0, 100)}...`, error, line);
      // throw error; // Uncomment to stop processing on first error
    }
  }

  return events;
}

async function parseEventsWith<T>(def: T, parser: (events: any[]) => T): Promise<T> {
  try {
    // Get the workspace folder
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
      return def;
    }
    // Read the file using VS Code's file system API
    const workspacePath = workspaceFolders[0].uri.fsPath;
    const logPath = path.join(workspacePath, checkerPath);
    const events = await readEventsStreaming(logPath);
    // Parse the events using the provided parser function
    const result = parser(events);
    return result;
  } catch (error) {
    // vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
    return def;
  }
}

async function parseLogInfo(): Promise<LogInfo> {
  let def: LogInfo = { lineInfos: new Map(), definitions: new Map() };
  try {
    // Get the workspace folder
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
      return def;
    }
    // Read the file using VS Code's file system API
    const workspacePath = workspaceFolders[0].uri.fsPath;
    const logPath = path.join(workspacePath, checkerPath);
    const events = await readEventsStreaming(logPath);

    events.forEach((event) => {

      // handle line-info events
      const lineInfo = parseEvent(event);
      if (lineInfo) {
        const [fileName, info] = lineInfo;
        if (!def.lineInfos.has(fileName)) {
          def.lineInfos.set(fileName, []);
        }
        def.lineInfos.get(fileName)?.push(info);
      }

      // handle definition events
      const fluxDef = parseFluxDef(event);
      if (fluxDef) {
        updateFluxDefs(def.definitions, fluxDef);
      }
    });

    return def;
  } catch (error) {
    // vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
    return def;
  }
}


type LogInfo = {
  lineInfos: Map<string, LineInfo[]>;
  definitions: Map<string, FluxDefs>;
}


// TODO: add local-info to TypeEnvBind
type TypeEnvBind = {
  name: string | null;
  kind: string;
  ty: NestedString;
  span: StmtSpan;
};
type TypeEnv = TypeEnvBind[];

type RcxBind = {
  name: string | string[];
  sort: string;
};
type Rcx = {
  bindings: RcxBind[];
  exprs: NestedString[];
};

type StmtSpan = {
  file: string | null;
  start_line: number;
  start_col: number;
  end_line: number;
  end_col: number;
};

type LineInfo = {
  line: number;
  pos: Position;
  rcx: string;
  env: string;
};

function parseStatementSpanJSON(span: string): StmtSpan | undefined {
  if (span) {
    return JSON.parse(span);
  }
  return undefined;
}

function parseEvent(event: any): [string, LineInfo] | undefined {
  try {
    const position =
      event.fields.event === "statement_start"
        ? Position.Start
        : event.fields.event === "statement_end"
          ? Position.End
          : undefined;
    if (position !== undefined && event.span.name === "refine") {
      const stmt_span = parseStatementSpanJSON(event.fields.stmt_span_json);
      if (stmt_span && stmt_span.file) {
        const info = {
          line: stmt_span.end_line,
          pos: position,
          rcx: event.fields.rcx_json,
          env: event.fields.env_json,
        };
        return [stmt_span.file, info];
      }
    }
  } catch (error) {
    console.log(`Failed to parse event: ${error}`);
  }
  return undefined;
}

function parseFluxDef(event: any): FluxDef | undefined {
  if (event.fields && event.fields.event === "hyperlink") {
    try {
      const srcSpan = JSON.parse(event.fields.src_span) as StmtSpan;
      const dstSpan = JSON.parse(event.fields.dst_span) as StmtSpan;
      if (!srcSpan.file || !dstSpan.file) {
        console.log(`Invalid detached link: ${event.fields}`);
        return undefined; // Skip invalid links
      }
      // console.log(`Parsing flux hyperlink definition`, srcSpan, dstSpan);
      // Create the target location
      const targetUri = vscode.Uri.file(dstSpan.file);
      const targetRange = new vscode.Range(
        dstSpan.start_line - 1,
        dstSpan.start_col - 1,
        dstSpan.end_line - 1,
        dstSpan.end_col - 1
      );
      const targetLocation = new vscode.Location(targetUri, targetRange);

      const fluxDef: FluxDef = {
        fileName: srcSpan.file,
        line: srcSpan.start_line,
        column_start: srcSpan.start_col,
        column_end: srcSpan.end_col,
        target: targetLocation,
      };
      // console.log(`Found flux definition`, fluxDef);
      return fluxDef;
    } catch (error) {
      console.log(`Failed to parse definition event: ${error}`);
      return undefined;
    }
  }
  return undefined;
}


/**********************************************************************************************/

type NestedString = {
  text: string;
  key?: string;
  children?: NestedString[];
};

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

function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}


function nestedStringHtml(node: NestedString): string {
  const hasChildren = node.children && node.children.length > 0;
  const toggleable = hasChildren ? "toggleable" : "";
  const labelclass = hasChildren ? " has-children" : " primitive";
  const keyText = node.key ? node.key + ": " : "";
  const labelText = escapeHtml(keyText + node.text);

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
// Rustc JSON Diagnostic Format Conversion (via Claude)
/**********************************************************************************************/

// TypeScript types representing rustc JSON diagnostic format
interface RustcSpan {
  file_name: string;
  byte_start: number;
  byte_end: number;
  line_start: number;
  line_end: number;
  column_start: number;
  column_end: number;
  is_primary: boolean;
  text: Array<{
    text: string;
    highlight_start: number;
    highlight_end: number;
  }>;
  label?: string;
  suggested_replacement?: string;
  suggestion_applicability?: string;
}

interface RustcCode {
  code: string;
  explanation?: string;
}

interface RustcMessage {
  message: string;
  code?: RustcCode;
  level: 'error' | 'warning' | 'note' | 'help' | 'failure-note' | 'ice';
  spans: RustcSpan[];
  children: RustcMessage[];
  rendered?: string;
}

interface RustcTarget {
  kind: string[];
  crate_types: string[];
  name: string;
  src_path: string;
  edition?: string;
  doctest?: boolean;
}

interface RustcDiagnostic {
  message: RustcMessage;
  package_id: string;
  manifest_path?: string;
  target: RustcTarget;
}

// Utility functions for conversion
function convertSeverity(level: string): vscode.DiagnosticSeverity {
  switch (level) {
    case 'error':
    case 'ice': // Internal Compiler Error
      return vscode.DiagnosticSeverity.Error;
    case 'warning':
      return vscode.DiagnosticSeverity.Warning;
    case 'note':
    case 'help':
      return vscode.DiagnosticSeverity.Information;
    case 'failure-note':
    default:
      return vscode.DiagnosticSeverity.Hint;
  }
}

function convertPosition(line: number, character: number): vscode.Position {
  // Convert from rustc's 1-based line/column to VS Code's 0-based
  return new vscode.Position(
    Math.max(0, line - 1),
    Math.max(0, character - 1)
  );
}

function convertRange(span: RustcSpan): vscode.Range {
  const start = convertPosition(span.line_start, span.column_start);
  const end = convertPosition(span.line_end, span.column_end);
  return new vscode.Range(start, end);
}

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
            workspaceRoot
              ? workspaceRoot + "/" + span.file_name
              : span.file_name
          );

          const location = new vscode.Location(uri, convertRange(span));
          const message = span.label || child.message;

          related.push(new vscode.DiagnosticRelatedInformation(location, message));
        } catch (error) {
          // Skip invalid file paths
          console.warn(`Failed to create related information for ${span.file_name}:`, error);
        }
      }
    }
  }
  return related;
}

// Main conversion function
export function convertRustcDiagnostic(
  rustcDiag: RustcDiagnostic,
  workspaceRoot?: string
): { uri: vscode.Uri; diagnostic: vscode.Diagnostic } | null {
  const message = rustcDiag.message;

  // Find the primary span (main location where the error occurs)
  const primarySpan = message.spans.find(span => span.is_primary);
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
          target: vscode.Uri.parse(`https://doc.rust-lang.org/error-index.html#${message.code.code}`)
        }
        : message.code.code;
    }

    // Set source
    diag.source = 'flux';

    // Add related information from child messages
    const relatedInfo = convertRelatedInformation(message.children, workspaceRoot);
    if (relatedInfo.length > 0) {
      diag.relatedInformation = relatedInfo;
    }

    // Add tags for specific types of diagnostics
    const tags: vscode.DiagnosticTag[] = [];
    if (message.code?.code === 'dead_code' || message.message.includes('never read')) {
      tags.push(vscode.DiagnosticTag.Unnecessary);
    }
    if (message.code?.code.startsWith('deprecated') || message.message.includes('deprecated')) {
      tags.push(vscode.DiagnosticTag.Deprecated);
    }
    if (tags.length > 0) {
      diag.tags = tags;
    }

    // Add link to full diagnostic if rendered content is available
    if (message.rendered) {
      // Generate a unique ID for this diagnostic
      const diagnosticId = `${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;

      // Store the diagnostic details for the content provider
      diagnosticDetailsMap.set(diagnosticId, rustcDiag);

      // Create command URI for the full diagnostic view
      const diagnosticUri = vscode.Uri.from({
        scheme: FluxDiagnosticContentProvider.scheme,
        path: `/${diagnosticId}`,
        query: `file=${encodeURIComponent(span.file_name)}&line=${span.line_start}`
      });

      // If there's already a code, preserve it, otherwise create a new code object
      const existingCode = message.code?.code;
      diag.code = {
        value: existingCode || "Click for full compiler diagnostic",
        target: diagnosticUri
      };

      // Clean up the message to remove some redundant information
      if (message.rendered) {
        const decolorized = anser.ansiToText(message.rendered);
        const index = decolorized.match(/^(note|help):/m)?.index || decolorized.length;
        const cleanMessage = decolorized
          .substring(0, index)
          .replace(/^ -->[^\n]+\n/m, "")
          .trim();

        if (cleanMessage && cleanMessage !== message.message) {
          diag.message = cleanMessage;
        }
      }
    }

    return { uri, diagnostic: diag };
  } catch (error) {
    console.error('Failed to convert rustc diagnostic:', error, rustcDiag);
    return null;
  }
}

// Batch conversion function for multiple diagnostics
export function convertRustcDiagnostics(
  rustcDiags: RustcDiagnostic[],
  workspaceRoot?: string
): Map<string, vscode.Diagnostic[]> {
  const diagnosticsByFile = new Map<string, vscode.Diagnostic[]>();

  for (const rustcDiag of rustcDiags) {
    const converted = convertRustcDiagnostic(rustcDiag, workspaceRoot);
    if (converted) {
      const fileKey = converted.uri.toString();
      const existing = diagnosticsByFile.get(fileKey) || [];
      existing.push(converted.diagnostic);
      diagnosticsByFile.set(fileKey, existing);
    }
  }

  return diagnosticsByFile;
}


// Usage example:
export function updateDiagnosticsFromRustc(
  diagnosticCollection: vscode.DiagnosticCollection,
  rustcOutput: string,
  workspaceRoot?: string
): void {
  try {
    // Parse rustc JSON output (each line is a separate JSON object)
    const rustcDiagnostics: RustcDiagnostic[] = [];

    for (const line of rustcOutput.split('\n')) {
      if (line.trim()) {
        try {
          const parsed = JSON.parse(line);
          // Only process compiler messages (not build artifacts)
          if (parsed.reason === 'compiler-message' && parsed.message) {
            console.log(`TRACE: updateDiagnostics parsed:`, parsed);
            const diag = {
              message: parsed.message,
              package_id: parsed.package_id,
              manifest_path: parsed.manifest_path,
              target: parsed.target
            };
            let str = renderRustcDiagnostic(diag, workspaceRoot);
            // console.log(`Parsed rustc diagnostic:\n ${str}`);
            rustcDiagnostics.push(diag);
          }
        } catch (parseError) {
          console.warn('Failed to parse rustc output line:', line, parseError);
        }
      }
    }

    // Convert to VS Code diagnostics
    const diagnosticsByFile = convertRustcDiagnostics(rustcDiagnostics, workspaceRoot);

    // Clear existing diagnostics
    diagnosticCollection.clear();

    // Set new diagnostics
    for (const [uriString, diagnostics] of diagnosticsByFile) {
      const uri = vscode.Uri.parse(uriString);
      diagnosticCollection.set(uri, diagnostics);
    }

  } catch (error) {
    console.error('Failed to update diagnostics from rustc output:', error);
  }
}

export function renderRustcDiagnostic(
  diagnostic: RustcDiagnostic,
  workspaceRoot?: string
): string {
  const message = diagnostic.message;
  let output = '';

  // Main diagnostic header
  const level = message.level.toUpperCase();
  const code = message.code?.code ? `[${message.code.code}]` : '';
  output += `${level}${code}: ${message.message}\n`;

  // Helper function to format file path
  const formatFilePath = (fileName: string): string => {
    if (workspaceRoot && fileName.startsWith(workspaceRoot)) {
      return fileName.substring(workspaceRoot.length + 1);
    }
    return fileName;
  };

  // Helper function to render a span with its context
  const renderSpan = (span: RustcSpan, indent: string = ''): string => {
    let spanOutput = '';

    if (span.file_name) {
      const filePath = formatFilePath(span.file_name);
      spanOutput += `${indent}--> ${filePath}:${span.line_start}:${span.column_start}\n`;

      // Add the source code lines if available
      if (span.text && span.text.length > 0) {
        const lineNumWidth = span.line_end.toString().length;

        span.text.forEach((textLine, index) => {
          const lineNum = span.line_start + index;
          const lineNumStr = lineNum.toString().padStart(lineNumWidth, ' ');

          spanOutput += `${indent}${lineNumStr} | ${textLine.text}\n`;

          // Add highlighting if this line has highlights
          if (textLine.highlight_start !== textLine.highlight_end) {
            const highlightLine = ' '.repeat(lineNumWidth + 3); // padding for line number and " | "
            const beforeHighlight = ' '.repeat(textLine.highlight_start);
            const highlightLength = textLine.highlight_end - textLine.highlight_start;
            const highlight = '^'.repeat(Math.max(1, highlightLength));

            spanOutput += `${indent}${highlightLine}${beforeHighlight}${highlight}`;

            // Add label if available
            if (span.label) {
              spanOutput += ` ${span.label}`;
            }
            spanOutput += '\n';
          }
        });
      }
    }

    return spanOutput;
  };

  // Process primary spans first
  const primarySpans = message.spans.filter(span => span.is_primary);
  const secondarySpans = message.spans.filter(span => !span.is_primary);

  // Render primary spans
  primarySpans.forEach(span => {
    output += renderSpan(span);
  });

  // Render secondary spans if any
  secondarySpans.forEach(span => {
    output += renderSpan(span, '   ');
  });

  // Process child messages (notes, helps, etc.)
  message.children.forEach(child => {
    output += '\n';
    const childLevel = child.level === 'note' ? 'note' :
      child.level === 'help' ? 'help' : child.level;
    output += `${childLevel}: ${child.message}\n`;

    // Render child spans
    child.spans.forEach(span => {
      if (span.is_primary && span.file_name) {
        output += renderSpan(span, '   ');
      }
    });
  });

  // Add suggestion if available
  const suggestionSpans = message.spans.filter(span => span.suggested_replacement);
  if (suggestionSpans.length > 0) {
    output += '\nhelp: try this\n';
    suggestionSpans.forEach(span => {
      if (span.suggested_replacement) {
        output += `   ${span.suggested_replacement}\n`;
      }
    });
  }

  // If we have a pre-rendered version, prefer that for ANSI formatting
  if (message.rendered) {
    // Strip ANSI codes for pure text output
    const cleanRendered = message.rendered
      .replace(/\x1b\[[0-9;]*m/g, '') // Remove ANSI escape codes
      .replace(/\r\n/g, '\n') // Normalize line endings
      .trim();

    if (cleanRendered.length > output.length) {
      return cleanRendered;
    }
  }

  return output.trim();
}