import * as vscode from "vscode";
import { parseEnv, parseRcx } from "../parsing";
import type { CheckMode, DisplayState, NestedString, Rcx, TypeEnv } from "../types";
import { InfoProvider } from "./InfoProvider";

/**
 * Helper function to render nested string as HTML
 */
function nestedStringHtml(node: NestedString): string {
    const hasChildren = node.children && node.children.length > 0;
    const toggleable = hasChildren ? "toggleable" : "";
    const labelclass = hasChildren ? " has-children" : " primitive";
    const labelText = renderText(node.text);
    const childrenHtml = hasChildren
        ? `<div class="children">${node.children!.map((child) => nestedStringHtml(child)).join("")}</div>`
        : "";

    const html = `
        <div class="node ${toggleable}">
            <span class="node-label ${labelclass}">${labelText}</span>
            ${childrenHtml}
        </div>
        `;
    return html;
}

/**
 * Helper function to render text with KvarApp transformations
 */
function renderText(text: string): string {
    // Replace patterns like ##[<s_0>##<s_1>##...##<s_n>]## with <s_0>(<s_1>, ..., <s_n>)
    return text.replace(/##\[([^\]]+)\]##/g, (match, content) => {
        const parts = content.split("##");
        if (parts.length === 0) {
            return match; // Return original if empty
        }
        const kvarApp = { kvar: parts[0], args: parts.slice(1) };
        return renderKvarApp(kvarApp);
    });
}

/**
 * Helper function to render KvarApp
 */
function renderKvarApp(app: { kvar: string; args: string[] }): string {
    const raw = `${app.kvar}(|${app.args.join(", ")}|)`;
    return `<span class="kvar-app" title="mickey-mouse"><b>${raw}</b></span>`;
}

/**
 * Provides webview functionality for displaying Flux type information
 */
export class FluxViewProvider implements vscode.WebviewViewProvider {
    private _view?: vscode.WebviewView;
    private _panel?: vscode.WebviewPanel;
    private _currentLine: number = 0;
    private _interactive: boolean = false;
    private _currentState: DisplayState = 0; // DisplayState.None
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
        private readonly _infoProvider: InfoProvider
    ) { }

    private show() {
        const panel = vscode.window.createWebviewPanel(
            "FluxInfoView",
            "Flux",
            vscode.ViewColumn.Beside,
            {
                enableScripts: true,
                retainContextWhenHidden: true,
            }
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
            undefined
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
            line.text
        );
    }

    public updateView() {
        this._currentLine = this._infoProvider.getLine();
        const info = this._infoProvider.getLineInfo();
        if (info === "loading") {
            this._currentState = 1; // DisplayState.Loading
        } else if (info) {
            this._currentState = 2; // DisplayState.Info
            this._currentRcx = parseRcx(info.rcx);
            this._currentEnv = parseEnv(info.env);
        } else {
            this._currentState = 0; // DisplayState.None
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
        _token: vscode.CancellationToken
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
          `
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
          `
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
        if (this._currentState === 2) {
            // DisplayState.Info
            body = this._getHtmlForInfo();
        } else if (this._currentState === 1) {
            // DisplayState.Loading
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
                          <input type="checkbox" id="checker-trace-checkbox" class="checker-trace-checkbox" ${this._checkTrace ? "checked" : ""}>
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
