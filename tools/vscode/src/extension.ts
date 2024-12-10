import * as vscode from 'vscode';
import * as path from 'path';
import * as child_process from 'child_process';
import * as process from 'node:process';
import { promisify } from 'util';
import * as fs from 'fs';

const checkerPath = "log/checker";

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {

    // Configure vscode so rust-analyzer generates `flux` errors on save
    const rustAnalyzerConfig = vscode.workspace.getConfiguration('rust-analyzer');
    rustAnalyzerConfig.update(
        'check.overrideCommand',
        ["cargo", "flux", "--workspace", "--message-format=json-diagnostic-rendered-ansi"],
        vscode.ConfigurationTarget.Workspace
    ).then(() => {
        vscode.window.showInformationMessage('Flux checking enabled');
    }, (error) => {
        vscode.window.showErrorMessage(`Failed to update configuration: ${error}`);
    });


    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) { return []; }

	// This line of code wll only be executed once when your extension is activated
    const workspacePath = workspaceFolders[0].uri.fsPath;
	console.log('Extension "flux" is now active in workspace:', workspacePath);

    const infoProvider = new InfoProvider(workspacePath);
	const fluxViewProvider = new FluxViewProvider(context.extensionUri, infoProvider);


    let disposable = vscode.commands.registerCommand('Flux.toggle', () => {
        fluxViewProvider.toggle();
        const editor = vscode.window.activeTextEditor;
        if (editor) {
            infoProvider.runFlux(editor.document.fileName, () => { fluxViewProvider.updateView(); });
        }
    });
    context.subscriptions.push(disposable);

    /************************************************************/
	// Register a custom webview panel

	context.subscriptions.push(
		vscode.window.registerWebviewViewProvider('fluxView', fluxViewProvider)
	);

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
        }
    ));

    // Track the set of opened files
    context.subscriptions.push(
        vscode.workspace.onDidOpenTextDocument((document) => {
            fluxViewProvider.runFlux(document.fileName);
        }
    ));



    // Reload the flux trace information for changedFiles
    const logFilePattern = new vscode.RelativePattern(workspacePath, checkerPath);
    const fileWatcher = vscode.workspace.createFileSystemWatcher(logFilePattern);

    fileWatcher.onDidChange((uri) => {
        // console.log(`checker trace changed: ${uri.fsPath}`);
        infoProvider.loadFluxInfo()
            .then(() => fluxViewProvider.updateView())
    });

}

// Promisify the exec function to use with await
const execPromise = promisify(child_process.exec);

async function runShellCommand(env: NodeJS.ProcessEnv, command: string) {
    try {
        const { stdout, stderr } = await execPromise(command, {
            env: env,
            cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath
        });

        // Handle any output
        // if (stdout) { console.log(`Command stdout: ${stdout}`); }
        // if (stderr) { console.warn(`Command stderr: ${stderr}`); }

        return stdout.trim();
    } catch (error) {
        console.log(`Command failed: ${error}`);
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
    await runShellCommand(process.env, command)
}

// run `cargo flux` on the file
async function runCargoFlux(file: string) {
    const fluxEnv = {
        ...process.env,
        FLUX_DUMP_CHECKER_TRACE : '1',
        FLUX_CHECK_FILES : file,
    };
    const command = `cargo flux`;
    await runShellCommand(fluxEnv, command);
}

// This method is called when your extension is deactivated
export function deactivate() {}

type LineMap = Map<number, LineInfo>;

enum Position { Start, End };

class InfoProvider {

    constructor(private readonly _workspacePath : string) {}

    private _StartMap: Map<string, LineMap> = new Map();
    private _EndMap: Map<string, LineMap> = new Map();
    private _ModifiedAt : Map<string, Date> = new Map();

    currentFile?: string;
    currentLine: number = 0;
    currentColumn: number = 0;
    currentPosition: Position = Position.End;

    private relFile(file: string) : string {
        return path.relative(this._workspacePath, file);
    }

    public setPosition(file: string, line: number, column: number, text: string) {
        this.currentFile = this.relFile(file);
        this.currentLine = line;
        this.currentColumn = column;
        this.currentPosition = text.slice(0, column - 1).trim() === '' ? Position.Start : Position.End;
    }

    // for the `Start` map we want the _first_ event for that line, while for the `End` map we want the _last_ event,
    // so we need to _reverse_ the array for the `Start` map
    private positionMap(info: LineInfo[], pos: Position) : LineMap {
         if (pos === Position.Start) {
              info = info.slice().reverse();
         }
        return new Map(info.filter(item => item.pos === pos).map(item => [item.line, item]));
   }

    private updateInfo(fileName: string, fileInfo: LineInfo[]) {
        const startMap = this.positionMap(fileInfo, Position.Start);
        const endMap = this.positionMap(fileInfo, Position.End);
        this._StartMap.set(fileName, startMap);
        this._EndMap.set(fileName, endMap);
    }

    public getLineInfo() : LineInfo | 'loading' | undefined {
        const file = this.currentFile;
        const pos = this.currentPosition;
        const line = this.currentLine;
        if (file) {
            const map = pos === Position.Start ? this._StartMap : this._EndMap;
            if (map.has(file)) {
                return map.get(file)?.get(line);
            } else {
                return 'loading';
            }
        }
    }

    public getLine(): number {
        return this.currentLine;
    }

    public async runFlux(file: string, beforeLoad: () => void) {
        if (!file.endsWith('.rs')) { return; }

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
        // console.log("Running flux on ", src);
        // run touch, cargo flux and load the new info
        await runTouch(src);
        const curAt = getFileModificationTime(file);
        this._ModifiedAt.set(src, curAt);
        await runCargoFlux(src)
   }

    public async loadFluxInfo() {
      try {
          // console.log("Loading flux info");
          const lineInfos = await readFluxCheckerTrace();
          lineInfos.forEach((lineInfo, fileName) => {
              this.updateInfo(fileName, lineInfo);
          });
      } catch (error) {
          vscode.window.showErrorMessage(`Failed to load line info: ${error}`);
      }
    }
}

enum DisplayState {
    None,       // no info to display at current cursor position
    Loading,    // running flux and waiting for results
    Info,       // have info to display at current cursor position
}

function collapseBindings(bindings: RcxBind[]): RcxBind[] {
    let sort  : string = '';
    let names : string[] = [];
    let binds : RcxBind[] = [];
    for (const bind of bindings) {
        if (typeof bind.name === 'string') {
            if (bind.sort === sort) {
                // same sort as before
                names.push(bind.name);
            } else {
                // new sort
                if (names.length > 0) { binds.push({name: names, sort: sort}) };
                names = [bind.name];
                sort = bind.sort;
            }
        }
    }
    if (names.length > 0) { binds.push({name: names, sort: sort}) };
    return binds;
}

function parseRcx(rcx: string): Rcx {
    const rcxObj = JSON.parse(rcx);
    rcxObj.bindings = collapseBindings(rcxObj.bindings);
    rcxObj.exprs = rcxObj.exprs.map((s:any) => parseNestedString(s));
    return rcxObj;
}

function parseNestedString(s: string): NestedString {
    return JSON.parse(s);
}

function parseEnv(env: string): TypeEnv {
    return JSON.parse(env)
            .filter((bind: TypeEnvBind) => bind.name)
            .map((b:any) => {
                return {name: b.name, kind: b.kind, ty: parseNestedString(b.ty) }
            });
}

class FluxViewProvider implements vscode.WebviewViewProvider {
    private _view?: vscode.WebviewView;
    private _panel?: vscode.WebviewPanel;
    private _currentLine: number = 0;
    private _currentState : DisplayState = DisplayState.None;
    private _currentRcx : Rcx | undefined;
    private _currentEnv : TypeEnv | undefined;
    private _fontFamily: string | undefined = 'Arial';
    private _fontSize: number | undefined = 14;

    constructor(private readonly _extensionUri: vscode.Uri, private readonly _infoProvider: InfoProvider) {}

    private show() {
        this._panel = vscode.window.createWebviewPanel(
                        'FluxInfoView',
                        'Flux',
                        vscode.ViewColumn.Beside,
                        { enableScripts: true,
                          retainContextWhenHidden: true
                        });
        this._panel.onDidDispose(() => {
            this._panel = undefined;
        });
        this.updateView();
    }

    private hide(){
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

    public runFlux(file: string) {
        this._infoProvider.runFlux(file, () => { this.updateView(); })
            .then(() => this._infoProvider.loadFluxInfo())
            .then(() => this.updateView());
    }

    public setPosition(editor: vscode.TextEditor) {
        const position = editor.selection.active;
        const fileName = editor.document.fileName;
        const line = editor.document.lineAt(position.line);
        this._infoProvider.setPosition(fileName, position.line + 1, position.character + 1, line.text);
    }

    public updateView() {
        this._currentLine = this._infoProvider.getLine();
        const info = this._infoProvider.getLineInfo();
        if (info === 'loading') {
            this._currentState = DisplayState.Loading;
        } else if (info) {
            this._currentState = DisplayState.Info;
            this._currentRcx = parseRcx(info.rcx);
            this._currentEnv = parseEnv(info.env);
            console.log("UpdateView", this._currentEnv);
        } else {
            this._currentState = DisplayState.None;
        }
        const config = vscode.workspace.getConfiguration('editor');
        this._fontFamily = config.get<string>('fontFamily');
        this._fontSize = config.get<number>('fontSize');
        const html = this._getHtmlForWebview();
        if (this._panel) { this._panel.webview.html = html; }
    }

    public resolveWebviewView(
        webviewView: vscode.WebviewView,
        context: vscode.WebviewViewResolveContext,
        _token: vscode.CancellationToken,
    ) {
        this._view = webviewView;
        webviewView.webview.options = {
            enableScripts: true,
            localResourceRoots: [this._extensionUri]
        };

        const config = vscode.workspace.getConfiguration('editor');
        this._fontFamily = config.get<string>('fontFamily');
        this._fontSize = config.get<number>('fontSize');

        webviewView.webview.html = this._getHtmlForWebview();
    }

    private _getHtmlForInfo() {
        const rcxBindings = this._currentRcx?.bindings.map(bind => {
          const name = typeof bind.name === 'string' ? bind.name : bind.name.join(' ');
          return `
            <tr>
                <td><b style="color: #F26123">${name}</b> : ${bind.sort} </td>
            </tr>
          `;
          }).join('');

        const rcxExprs = this._currentRcx?.exprs.map(expr => `
            <tr>
                <td>${nestedStringHtml(expr)}</td>
            </tr>
          `).join('');

        const envBindings = this._currentEnv?.map(bind => `
            <tr>
                <td style="vertical-align: top;"><b style="color: #F26123">${bind.name}</b></td>
                <td>${nestedStringHtml(bind.ty)}</td>
            </tr>
          `).join('');

        return `
                    <table style="border-collapse: collapse">
                    <tr>
                      <th style="color: green">Values</th>
                    </tr>
                    ${rcxBindings}
                    </table>

                    <br>

                    <table>
                    <tr>
                      <th style="color: purple">Constraints</th>
                    </tr>
                    ${rcxExprs}
                    </table>

                    <br>

                    <table style="border-collapse: collapse">
                    <tr>
                      <th style="color: blue">Types</th>
                      <td></td>
                    </tr>
                    ${envBindings}
                    </table>
                `;

    }

    private _getHtmlForMessage(message:string) {
        return `
                    <table style="border-collapse: collapse">
                    <tr>
                      <th>${message}</th>
                    </tr>
                    </table>
                `;

    }

    private _getHtmlForWebview() {
        let body : string;
        if (this._currentState === DisplayState.Info) {
            body = this._getHtmlForInfo();
        } else if (this._currentState === DisplayState.Loading) {
            body = this._getHtmlForMessage('Loading...');
        } else {
            body = this._getHtmlForMessage('No info available');
        }
        const sampleNestedHtml = nestedStringHtml(sampleData);

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
                </style>
            </head>
            <body>
                <div id="cursor-position">
                    <table style="border-collapse: collapse">
                    <tr>
                      <th>Line</th> <td>${this._currentLine}</t>
                    </tr>
                    </table>

                    <br>

                    <div>${body}</div>

                </div>
	        <script>
            document.addEventListener('DOMContentLoaded', () => {
                const toggleables = document.querySelectorAll('.toggleable');
                toggleables.forEach((element, index) => {
                    element.addEventListener('click', (e) => {
                        e.stopPropagation();
                        element.classList.toggle('expanded');
                    });
                });
            });
            </script>
            </body>
            </html>
        `;
    }
}

async function readFluxCheckerTrace(): Promise<Map<string, LineInfo[]>> {
    try {
        // Get the workspace folder
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (!workspaceFolders) { return new Map(); }

        // Read the file using VS Code's file system API
        const workspacePath = workspaceFolders[0].uri.fsPath;
        const logPath = path.join(workspacePath, checkerPath);
        const logUri = vscode.Uri.file(logPath);
        const logData = await vscode.workspace.fs.readFile(logUri);
        const logString = Buffer.from(logData).toString('utf8');

        // Parse the logString
        const data = parseEventLog(logString);
        return data;
    } catch (error) {
        vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
        return new Map();
    }
}

// TODO: add local-info to TypeEnvBind
type TypeEnvBind = {
  name: string | null,
  kind: string,
  ty: NestedString,
}
type TypeEnv = TypeEnvBind[];

type RcxBind = {
    name: string | string[],
    sort: string,
}
type Rcx = {
    bindings: RcxBind[],
    exprs: NestedString[],
}

type StmtSpan = {
    file: string;
    start_line: number;
    start_col: number;
    end_line: number;
    end_col: number;
}

type LineInfo = {
    line: number;
    pos: Position;
    rcx: string;
    env: string;
}

function parseStatementSpan(span: string): StmtSpan | undefined {
    if (span) {
        const parts = span.split(':');
        if (parts.length === 5) {
            const end_col_str = parts[4].split(' ')[0];
            const end_col = parseInt(end_col_str, 10);
            return {
                file: parts[0],
                start_line: parseInt(parts[1], 10),
                start_col: parseInt(parts[2], 10),
                end_line: parseInt(parts[1], 10),
                end_col: end_col,
            };
        }
    }
    return undefined;
}

function parseEvent(event: any): [string, LineInfo] | undefined {
    const position = event.fields.event === 'statement_start' ? Position.Start : (event.fields.event === 'statement_end' ? Position.End : undefined);
    if (position !== undefined) {
        const stmt_span = parseStatementSpan(event.fields.stmt_span);
        if (stmt_span /* && files.has(stmt_span.file) */) {
            const info = {line: stmt_span.end_line, pos: position, rcx: event.fields.rcx_json, env: event.fields.env_json};
            return [stmt_span.file, info];
        }
    }
    return undefined;
}

function parseEventLog(logString: string): Map<string, LineInfo[]> {
    const events = logString.split('\n').filter(line => line.trim()).map(line => JSON.parse(line));
    const res = new Map();
    events.forEach(event => {
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
    text: string,
    key?: string,
    children?: NestedString[],
}

// Sample data (you'd typically get this from somewhere else)
const sampleData: NestedString =
    {
        key: '',
        text: '{..}',
        children: [
            {
                key: 'f1',
                text: '10'
            },
            {
                key: 'f2',
                text: '20'
            },
            {
                key: 'f3',
                text: '{..}',
                children: [
                    { key: 'f4', text: '30' },
                    { key: 'f5', text: '40' }
                ]
            },
        ]
    };

function nestedStringHtml(node: NestedString) : string {
    const hasChildren = node.children && node.children.length > 0;
    const toggleable = hasChildren ? 'toggleable' : '';
    const labelclass = hasChildren ? ' has-children' : ' primitive';
    const keyText = node.key ? node.key + ': ' : '';
    const labelText = keyText + node.text;

    let childrenHtml = '';
    if (node.children) {
        const childrenElements = node.children.map((child) => nestedStringHtml(child)).join('');
        childrenHtml = `<div class="children">${childrenElements}</div>`;
    }

    hasChildren ? node.children?.map((child) => nestedStringHtml(child)).join('') : '';
    const html = `
        <div class="node ${toggleable}">
            <span class="node-label ${labelclass}">${labelText}</span>
            ${childrenHtml}
        </div>
        `;
    return html
}

/**********************************************************************************************/