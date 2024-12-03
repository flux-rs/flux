import * as vscode from 'vscode';
import * as path from 'path';

const checkerPath = "log/checker";

// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
export function activate(context: vscode.ExtensionContext) {
    const workspaceFolders = vscode.workspace.workspaceFolders;
    if (!workspaceFolders) { return []; }

	// This line of code wll only be executed once when your extension is activated
    const workspacePath = workspaceFolders[0].uri.fsPath;
	console.log('Extension "flux" is now active in workspace:', workspacePath);

    // Update rust-analyzer to run `flux` on save
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

    const infoProvider = new InfoProvider(workspacePath);
	const fluxViewProvider = new FluxViewProvider(context.extensionUri, infoProvider);

    let disposable = vscode.commands.registerCommand('Flux.toggle', () => {
        fluxViewProvider.toggle();
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
				const position = event.textEditor.selection.active;
                const fileName = event.textEditor.document.fileName;
                const line = event.textEditor.document.lineAt(position.line);
				infoProvider.setPosition(fileName, position.line + 1, position.character + 1, line.text);
                fluxViewProvider.updateView();
			}
		})
	);

    /* Watch for changes to the trace-file ***********************************************/

    // Track the set of saved (updated) source files
    context.subscriptions.push(
        vscode.workspace.onDidSaveTextDocument((document) => {
            if (document.fileName.endsWith('.rs')) {
                // console.log('source file changed: ' + document.fileName);
                infoProvider.addChangedFile(document.fileName);
            }
        }
    ));

    // Reload the flux trace information for changedFiles
    const logFilePattern = new vscode.RelativePattern(workspacePath, checkerPath);
    const fileWatcher = vscode.workspace.createFileSystemWatcher(logFilePattern);

    fileWatcher.onDidChange((uri) => {
        // console.log(`checker trace changed: ${uri.fsPath}`);
        fluxViewProvider.reloadView();
    });

    /******************************************************************************/

}

// This method is called when your extension is deactivated
export function deactivate() {}

type LineMap = Map<number, LineInfo>;

enum Position { Start, End };

class InfoProvider {

    constructor(private readonly _workspacePath : string) {}

    private _StartMap: Map<string, LineMap> = new Map();
    private _EndMap: Map<string, LineMap> = new Map();

    currentFile?: string;
    currentLine: number = 0;
    currentColumn: number = 0;
    currentPosition: Position = Position.End;

    private _changedFiles: Set<string> = new Set();

    private relFile(file: string) : string {
        return path.relative(this._workspacePath, file);
    }

    public setPosition(file: string, line: number, column: number, text: string) {
        this.currentFile = this.relFile(file);
        this.currentLine = line;
        this.currentColumn = column;
        this.currentPosition = text.slice(0, column - 1).trim() === '' ? Position.Start : Position.End;
    }

    public addChangedFile(file: string) {
        this._changedFiles.add(this.relFile(file));
    }

    private getChangedFiles() : Set<string> {
        const res = new Set([...this._changedFiles]);
        const cur = this.currentFile;
        if (cur) { res.add(cur); };
        return res;
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
        this._changedFiles.delete(fileName);
    }

    public getLineInfo() : LineInfo | undefined {
        const file = this.currentFile;
        const pos = this.currentPosition;
        const line = this.currentLine;
        if (file) {
            if (pos === Position.Start) {
                return this._StartMap.get(file)?.get(line);
            } else {
                return this._EndMap.get(file)?.get(line);
            }
        }
    }

    public getLine(): number {
        return this.currentLine;
    }

    private openFiles() : Set<string> {
        const files = vscode.workspace.textDocuments
                        .filter(doc => doc.fileName.endsWith('.rs'))
                        .map(doc => this.relFile(doc.fileName));
        return new Set(files);
    }

    public async loadFluxInfo() {
      try {
          const changedFiles = this.getChangedFiles();
          const files = changedFiles.size > 0 ? changedFiles : this.openFiles();
          const lineInfos = await readFluxCheckerTrace(files);
          lineInfos.forEach((lineInfo, fileName) => {
              this.updateInfo(fileName, lineInfo);
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
        this.reloadView();
    }

    public hide(){
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

    public async reloadView() {
        this._infoProvider.loadFluxInfo().then(() => {
            this.updateView();
        });
    }


    public updateView() {
        const info = this._infoProvider.getLineInfo();
        this._currentLine = this._infoProvider.getLine();
        if (info) {
          this._currentRcx = JSON.parse(info.rcx);
          this._currentEnv = JSON.parse(info.env);
          const config = vscode.workspace.getConfiguration('editor');
          this._fontFamily = config.get<string>('fontFamily');
          this._fontSize = config.get<number>('fontSize');
          const html = this._getHtmlForWebview();
          if (this._panel) { this._panel.webview.html = html; }
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
            localResourceRoots: [this._extensionUri]
        };

        const config = vscode.workspace.getConfiguration('editor');
        this._fontFamily = config.get<string>('fontFamily');
        this._fontSize = config.get<number>('fontSize');

        webviewView.webview.html = this._getHtmlForWebview();
    }

    private _getHtmlForWebview() {

        const rcxBindings = this._currentRcx?.bindings.map(bind => `
            <tr>
                <td><b style="color: #F26123">${bind.name}</b> : ${bind.sort} </td>
            </tr>
          `).join('');

        const rcxExprs = this._currentRcx?.exprs.map(expr => `
            <tr>
                <td>${expr}</td>
            </tr>
          `).join('');

        const envBindings = this._currentEnv?.map(bind => `
            <tr>
                <td><b style="color: #F26123">${bind.loc}</b> : ${bind.ty} </td>
            </tr>
          `).join('');



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
                </div>
            </body>
            </html>
        `;
    }
}

async function readFluxCheckerTrace(changedFiles: Set<string>): Promise<Map<string, LineInfo[]>> {
    try {
        // Get the workspace folder
        const workspaceFolders = vscode.workspace.workspaceFolders;
        if (!workspaceFolders) { return new Map(); }

        // Read the file using VS Code's file system API
        const workspacePath = workspaceFolders[0].uri.fsPath;
        const logPath = path.join(workspacePath, "log/checker");
        const logUri = vscode.Uri.file(logPath);
        const logData = await vscode.workspace.fs.readFile(logUri);
        const logString = Buffer.from(logData).toString('utf8');

        // Parse the logString
        const data = parseEventLog(changedFiles, logString);
        return data;
    } catch (error) {
        vscode.window.showErrorMessage(`Failed to read line info: ${error}`);
        return new Map();
    }
}

type TypeEnvBind = {
  loc: String,
  kind: String,
  ty: String,
}
type TypeEnv = TypeEnvBind[];
type RcxBind = {
    name: String,
    sort: String,
}
type Rcx = {
    bindings: RcxBind[],
    exprs: String[],
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

function parseEvent(files: Set<string>, event: any): [string, LineInfo] | undefined {
    const position = event.fields.event === 'statement_start' ? Position.Start : (event.fields.event === 'statement_end' ? Position.End : undefined);
    if (position !== undefined) {
        const stmt_span = parseStatementSpan(event.fields.stmt_span);
        if (stmt_span && files.has(stmt_span.file)) {
            const info = {line: stmt_span.end_line, pos: position, rcx: event.fields.rcx_json, env: event.fields.env_json};
            return [stmt_span.file, info];
        }
    }
    return undefined;
}

function parseEventLog(files: Set<string>, logString: string): Map<string, LineInfo[]> {
    const events = logString.split('\n').filter(line => line.trim()).map(line => JSON.parse(line));
    const res = new Map();
    events.forEach(event => {
        const eventInfo = parseEvent(files, event);
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