import * as fs from "fs";
import * as path from "path";
import * as vscode from "vscode";

/**
 * Sets up the file system watcher for the flux checker log file
 */
export function setupFileWatcher(
    workspacePath: string,
    checkerPath: string,
    onFileChange: () => void
): vscode.FileSystemWatcher {
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
        onFileChange();
    });

    return fileWatcher;
}
