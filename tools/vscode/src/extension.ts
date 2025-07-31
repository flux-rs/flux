import * as vscode from "vscode";
import * as path from "path";
import * as child_process from "child_process";
import * as process from "node:process";
import { promisify } from "util";
import * as fs from "fs";
import * as readline from "readline";

const checkerPath = "log/checker";

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
  // Configure vscode so rust-analyzer generates `flux` errors on save
  const rustAnalyzerConfig = vscode.workspace.getConfiguration("rust-analyzer");
  rustAnalyzerConfig
    .update("server.extraEnv", {
      FLUXFLAGS: "-Fdump-checker-trace",
    })
    .then(() => {
      return rustAnalyzerConfig.update(
        "check.overrideCommand",
        [
          "cargo",
          "flux",
          "--workspace",
          "--message-format=json-diagnostic-rendered-ansi",
        ],
        vscode.ConfigurationTarget.Workspace,
      );
    })
    .then(
      () => {
        vscode.window.showInformationMessage("Flux checking enabled");
      },
      (error) => {
        vscode.window.showErrorMessage(
          `Failed to update configuration: ${error}`,
        );
      },
    );

  const workspaceFolders = vscode.workspace.workspaceFolders;
  if (!workspaceFolders) {
    return [];
  }

  // This line of code wll only be executed once when your extension is activated
  const workspacePath = workspaceFolders[0].uri.fsPath;
  console.log('Extension "flux" is now active in workspace:', workspacePath);

  const infoProvider = new InfoProvider(workspacePath);
  const fluxViewProvider = new FluxViewProvider(
    context.extensionUri,
    infoProvider,
  );

  let disposable = vscode.commands.registerCommand("Flux.toggle", () => {
    fluxViewProvider.toggle();
    const editor = vscode.window.activeTextEditor;
    if (editor) {
      infoProvider.runFlux(editor.document.fileName, () => {
        fluxViewProvider.updateView();
      });
    }
  });
  context.subscriptions.push(disposable);

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

  // Reload the flux trace information for changedFiles
  const logFilePattern = new vscode.RelativePattern(workspacePath, checkerPath);
  const fileWatcher = vscode.workspace.createFileSystemWatcher(logFilePattern);
  console.log(`fileWatcher at:`, logFilePattern);

  fileWatcher.onDidChange((uri) => {
    console.log(`checker trace changed: ${uri.fsPath}`);
    infoProvider.loadFluxInfo().then(() => fluxViewProvider.updateView());
  });
}

// Promisify the exec function to use with await
const execPromise = promisify(child_process.exec);

async function runShellCommand(env: NodeJS.ProcessEnv, command: string) {
  try {
    // console.log("Running command: ", command);
    const { stdout, stderr } = await execPromise(command, {
      env: env,
      cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
    });

    // Handle any output
    // if (stdout) { console.log(`Command stdout: ${stdout}`); }
    // if (stderr) { console.warn(`Command stderr: ${stderr}`); }

    return stdout.trim();
  } catch (error) {
    console.log(`Command failed!`);
    // console.log(`Command failed:`, error);
    // vscode.window.showErrorMessage(`Command failed: ${error}`);
    // throw error;
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
async function runCargoFlux(workspacePath: string, file: string) {
  const logDir = path.join(workspacePath, "log");
  const fluxEnv = {
    ...process.env,
    FLUX_LOG_DIR: logDir,
    FLUX_DUMP_CHECKER_TRACE: "1",
    FLUX_CHECK_FILES: file,
  };
  const command = `cargo flux`;
  console.log("Running flux:", fluxEnv, command);
  await runShellCommand(fluxEnv, command);
}

// This method is called when your extension is deactivated
export function deactivate() {}

type LineMap = Map<number, LineInfo>;

enum Position {
  Start,
  End,
}

class InfoProvider {
  constructor(private readonly _workspacePath: string) {}

  private _StartMap: Map<string, LineMap> = new Map();
  private _EndMap: Map<string, LineMap> = new Map();
  private _ModifiedAt: Map<string, Date> = new Map();

  currentFile?: string;
  currentLine: number = 0;
  currentColumn: number = 0;
  currentPosition: Position = Position.End;

  private relFile(file: string): string {
    return path.relative(this._workspacePath, file);
  }

  public setPosition(file: string, line: number, column: number, text: string) {
    this.currentFile = file; // this.relFile(file);
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

  public async runFlux(file: string, beforeLoad: () => void) {
    if (!file.endsWith(".rs")) {
      return;
    }
    const workspacePath = this._workspacePath;
    const src = this.relFile(file);
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
    // note we use `file` for the ABSOLUTE path due to odd cargo workspace behavior
    await runCargoFlux(workspacePath, file);
  }

  public async loadFluxInfo() {
    try {
      const [detachedLinks, lineInfos] = await readFluxCheckerTrace();
      lineInfos.forEach((lineInfo, fileName) => {
        this.updateInfo(fileName, lineInfo);
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

class FluxViewProvider implements vscode.WebviewViewProvider {
  private _view?: vscode.WebviewView;
  private _panel?: vscode.WebviewPanel;
  private _currentFile?: string;
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

  constructor(
    private readonly _extensionUri: vscode.Uri,
    private readonly _infoProvider: InfoProvider,
  ) {}

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
          case "interactiveClicked":
            this._interactive = !this._interactive;
            this.updateView();
            return;
          case "runCheck":
            if (this._currentFile) {
              this.runFluxCheck(this._currentFile);
            }
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
      .runFlux(file, () => {
        this.updateView();
      })
      .then(() => this._infoProvider.loadFluxInfo())
      .then(() => this.updateView());
  }

  public runFlux(file: string) {
    this._currentFile = file;
    if (!this._interactive) {
      this.runFluxCheck(file);
    }
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
      body = this._getHtmlForMessage("Loading...");
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
                    align-items: center;
                    justify-content: center; /* Center items horizontally */
                    width: 100%;
                    padding: 10px 0; /* Add some vertical padding */
                    background-color: var(--vscode-editor-background);
                    border-bottom: 1px solid var(--vscode-panel-border); /* Optional: adds a subtle border */
                }

                .toggle-label {
                  margin-right: 10px;
                  font-weight: 500;
                }
                .toggle-switch {
                  position: relative;
                  display: inline-block;
                  width: 48px;
                  height: 24px;
                  margin-right: 20px;
                }
                .toggle-switch input {
                  opacity: 0;
                  width: 0;
                  height: 0;
                }
                .slider {
                  position: absolute;
                  cursor: pointer;
                  top: 0;
                  left: 0;
                  right: 0;
                  bottom: 0;
                  background-color: var(--vscode-disabledForeground);
                  transition: .3s;
                  border-radius: 24px;
                }
                .slider:before {
                  position: absolute;
                  content: "";
                  height: 16px;
                  width: 16px;
                  left: 4px;
                  bottom: 4px;
                  background-color: white;
                  transition: .3s;
                  border-radius: 50%;
                }
                input:checked + .slider {
                  background-color: var(--vscode-button-background);
                }
                input:checked + .slider:before {
                  transform: translateX(24px);
                }
                button {
                  padding: 8px 16px;
                  border-radius: 4px;
                  font-weight: 500;
                  outline: none;
                  border: none;
                  cursor: pointer;
                }
                button:focus {
                  outline: 2px solid var(--vscode-focusBorder);
                }
                button.disabled {
                  background-color: var(--vscode-disabledForeground);
                  color: var(--vscode-editor-background);
                  cursor: not-allowed;
                }
                button.enabled {
                  background-color: var(--vscode-button-background);
                  color: var(--vscode-button-foreground);
                }
                button.enabled:hover {
                  background-color: var(--vscode-button-hoverBackground);
                }
                .toggle-container {
                    display: flex;
                    align-items: bottom;
                    vertical-align: middle;
                    gap: 10px;
                    margin-bottom: 20px;
                }
                </style>
            </head>
            <body>

              <div id="cursor-position">
                    <table style="border-collapse: collapse">
                    <tr>
                      <td colspan="2">
                        <div class="control-row">
                          <label class="toggle-switch"><input type="checkbox" id="interactive-toggle"><span class="slider"></span></label>
                          <button id="check-button" class="disabled" disabled>Check</button>
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


            const interactiveElement = document.getElementById('interactive-toggle');
            const checkButton = document.getElementById('check-button');

            const isInteractive = ${this._interactive};
            interactiveElement.checked = isInteractive;
            checkButton.disabled = !isInteractive;
            checkButton.className = isInteractive ? 'enabled' : 'disabled';

            interactiveElement.addEventListener('click', () => {
              console.log("interactive toggled!");
              vscode.postMessage({
                  command: 'interactiveClicked',
                  text: interactiveElement.checked
              });
              if (interactiveElement.checked) {
                checkButton.className = 'enabled';
                checkButton.disabled = false;
              } else {
                checkButton.className = 'disabled';
                checkButton.disabled = true;
              }
            });

            checkButton.addEventListener('click', () => {
                vscode.postMessage({
                    command: 'runCheck'
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
      console.error(`Error parsing line: ${line.substring(0, 100)}...`);
      console.error(error);
      throw error; // Uncomment to stop processing on first error
    }
  }

  return events;
}

async function readFluxCheckerTrace(): Promise<[ Array<DetachedLink>, Map<string, LineInfo[]> ] > {
  try {
    // Get the workspace folder
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) {
      return [ new Array(), new Map() ];
    }

    // Read the file using VS Code's file system API
    const workspacePath = workspaceFolders[0].uri.fsPath;
    const logPath = path.join(workspacePath, checkerPath);
    const events = await readEventsStreaming(logPath);
    const data = parseEvents(events);
    const links = parseDetachedLinkEvents(events);
    return [ links, data ];
  } catch (error) {
    // vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
    return [ new Array(), new Map() ];
  }
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

// function parseStatementSpan(span: string): StmtSpan | undefined {
//     if (span) {
//         const parts = span.split(':');
//         if (parts.length === 5) {
//             const end_col_str = parts[4].split(' ')[0];
//             const end_col = parseInt(end_col_str, 10);
//             return {
//                 file: parts[0],
//                 start_line: parseInt(parts[1], 10),
//                 start_col: parseInt(parts[2], 10),
//                 end_line: parseInt(parts[1], 10),
//                 end_col: end_col,
//             };
//         }
//     }
//     return undefined;
// }

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

type DetachedLink = {src_span: StmtSpan, dst_span: StmtSpan};

function parseDetachedLinkEvents(events: any[]): Array<DetachedLink> {
  return events
    .filter(event => event.fields && event.fields.event === "detached_link")
    .map(event => {
      try {
        const src_span = JSON.parse(event.fields.src_span) as StmtSpan;
        const dst_span = JSON.parse(event.fields.dst_span) as StmtSpan;
        return { src_span, dst_span };
      } catch (error) {
        console.log(`Failed to parse detached_link event: ${error}`);
        return null;
      }
    })
    .filter(result => result !== null) as Array<{src_span: StmtSpan, dst_span: StmtSpan}>;
}

function parseEvents(events: any[]): Map<string, LineInfo[]> {
  // const events = logString.split('\n').filter(line => line.trim()).map(line => JSON.parse(line));
  const res = new Map();
  events.forEach((event) => {
    const eventInfo = parseEvent(event);
    if (eventInfo) {
      const [fileName, info] = eventInfo;
      if (!res.has(fileName)) {
        res.set(fileName, []);
      }
      res.get(fileName)?.push(info);
    }
  });
  return res;
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

function nestedStringHtml(node: NestedString): string {
  const hasChildren = node.children && node.children.length > 0;
  const toggleable = hasChildren ? "toggleable" : "";
  const labelclass = hasChildren ? " has-children" : " primitive";
  const keyText = node.key ? node.key + ": " : "";
  const labelText = keyText + node.text;

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
