# flux-dev

VS Code extension with language support for flux rust intermediate representations

## Install

**Step 1.** To get the extension running you need to **build** the `vsix` file and **install** it manually

```bash
$ npm install -g typescript
$ npm install -g vsce
$ vsce package
```

**Step 2.** Install `flux`

Following [these instructions](https://flux-rs.github.io/flux/guide/install.html)

**Step 3.** Run the extension!

You can then **enable** the extension by runnning the `Toggle Flux View` command in the command palette.

## Features

Syntax Highlighting

- For `flux` type signatures
- For `flux` constraints (generated with `FLUX_DUMP_CONSTRAINT=1` for debugging)

Flux View Panel: shows the types and environments known at each program point

- If your cursor is _at or before_ the first non-blank character of a line, the panel will show the types and environments _before_ that line
- Else the panel will show the types and environments _after_ that line

![Before Statement](static/flux_view_start.jpg)

![After Statement](static/flux_view_end.jpg)




---

import * as vscode from 'vscode';

export function activate(context: vscode.ExtensionContext) {
  // Register a command that opens the webview panel
  let disposable = vscode.commands.registerCommand('yourExtension.showTogglePanel', () => {
    // Create and show panel
    const panel = vscode.window.createWebviewPanel(
      'toggleButtonPanel',
      'Toggle Button Control',
      vscode.ViewColumn.One,
      {
        enableScripts: true // Allow JavaScript in the webview
      }
    );

    // Set the HTML content
    panel.webview.html = getWebviewContent();

    // Handle messages from the webview
    panel.webview.onDidReceiveMessage(
      message => {
        switch (message.command) {
          case 'performAction':
            vscode.window.showInformationMessage('Action performed from webview!');
            return;
        }
      },
      undefined,
      context.subscriptions
    );
  });

  context.subscriptions.push(disposable);
}

function getWebviewContent() {
  return `<!DOCTYPE html>
  <html lang="en">
  <head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Toggle Button Control</title>
    <style>
      body {
        font-family: var(--vscode-font-family);
        padding: 20px;
        color: var(--vscode-foreground);
      }
      .container {
        display: flex;
        flex-direction: column;
        align-items: center;
        padding: 20px;
        border-radius: 6px;
        background-color: var(--vscode-editor-background);
      }
      h2 {
        margin-bottom: 20px;
      }
      .control-row {
        display: flex;
        align-items: center;
        margin-bottom: 20px;
        width: 100%;
        justify-content: center;
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
    </style>
  </head>
  <body>
    <div class="container">
      <h2>Feature Control Panel</h2>

      <div class="control-row">
        <span class="toggle-label">Enable Feature:</span>
        <label class="toggle-switch">
          <input type="checkbox" id="feature-toggle">
          <span class="slider"></span>
        </label>

        <button id="action-button" class="disabled" disabled>Perform Action</button>
      </div>
    </div>

    <script>
      (function() {
        const vscode = acquireVsCodeApi();
        const toggle = document.getElementById('feature-toggle');
        const actionButton = document.getElementById('action-button');

        toggle.addEventListener('change', () => {
          if (toggle.checked) {
            actionButton.className = 'enabled';
            actionButton.disabled = false;
          } else {
            actionButton.className = 'disabled';
            actionButton.disabled = true;
          }
        });

        actionButton.addEventListener('click', () => {
          vscode.postMessage({
            command: 'performAction'
          });
        });
      })();
    </script>
  </body>
  </html>`;
}