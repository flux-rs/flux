import * as child_process from "child_process";
import * as process from "node:process";
import { promisify } from "util";
import * as vscode from "vscode";

// Global variable to track the running flux process
let runningFluxProcess: child_process.ChildProcess | null = null;

// Promisify the exec function to use with await
const execPromise = promisify(child_process.exec);

/**
 * Run a shell command with the given environment variables
 */
export async function runShellCommand(
    env: NodeJS.ProcessEnv,
    command: string
): Promise<any> {
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
        const stdout = error.stdout || "";
        const stderr = error.stderr || "";
        const exitCode = error.code;

        console.log(`Command failed with exit code ${exitCode}`);
        // if (stdout) { console.log(`Command stdout: ${stdout}`); }
        // if (stderr) { console.warn(`Command stderr: ${stderr}`); }
        // Return stdout even on failure - useful for commands that output data but exit with non-zero
        return stdout.trim();
    }
}

/**
 * Run `touch` on the file to force cargo/flux to re-run
 */
export async function runTouch(file: string) {
    const command = `touch ${file}`;
    await runShellCommand(process.env, command);
}

/**
 * Run `cargo flux` on the file (absolute path)
 */
export async function runCargoFlux(
    workspacePath: string,
    file: string,
    trace: boolean,
    includeValue: string,
    statusBarItem: vscode.StatusBarItem
): Promise<any> {
    // Show spinning indicator with clickable command
    statusBarItem.text = "$(sync~spin) Running Flux... (click to cancel)";
    statusBarItem.tooltip = "Flux type checker is running - Click to cancel";
    statusBarItem.command = "Flux.killProcess";
    statusBarItem.show();

    let fluxFlags = `-Finclude=${includeValue}`;
    fluxFlags += ` -Fsummary=off`;
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
        const config = vscode.workspace.getConfiguration("flux");
        const baseCommand = config.get<string>("command", "cargo flux");
        const commandArgs = `${baseCommand} --message-format=json-diagnostic-rendered-ansi`.split(
            " "
        );
        const command = commandArgs[0];
        const args = commandArgs.slice(1);

        const start = performance.now();
        console.log(
            `TRACE: Running command: ${command} ${args.join(" ")} flags=`,
            fluxEnv.FLUXFLAGS
        );

        // Use spawn to get a killable process reference
        runningFluxProcess = child_process.spawn(command, args, {
            env: fluxEnv,
            cwd: vscode.workspace.workspaceFolders?.[0]?.uri.fsPath,
            stdio: ["pipe", "pipe", "pipe"],
        });

        let stdout = "";
        let stderr = "";

        runningFluxProcess.stdout?.on("data", (data) => {
            stdout += data.toString();
        });

        runningFluxProcess.stderr?.on("data", (data) => {
            stderr += data.toString();
        });

        runningFluxProcess.on("close", (code, signal) => {
            const end = performance.now();
            console.log(`TRACE: Finish command: execution time: ${end - start} ms`);

            runningFluxProcess = null;
            statusBarItem.hide();
            statusBarItem.command = undefined; // Remove click command

            if (signal === "SIGTERM") {
                console.log("Flux process was terminated by user");
                resolve(""); // Return empty result when cancelled
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

        runningFluxProcess.on("error", (error) => {
            const end = performance.now();
            console.log(`TRACE: Finish command: execution time: ${end - start} ms`);

            runningFluxProcess = null;
            statusBarItem.hide();
            statusBarItem.command = undefined; // Remove click command

            console.error("Failed to start flux process:", error);
            reject(error);
        });
    });
}

/**
 * Kill the running flux process if it exists
 */
export function killFluxProcess(): boolean {
    if (runningFluxProcess) {
        console.log("Killing flux process...");
        runningFluxProcess.kill("SIGTERM");
        runningFluxProcess = null;
        return true;
    }
    return false;
}

/**
 * Get the running flux process reference
 */
export function getRunningFluxProcess(): child_process.ChildProcess | null {
    return runningFluxProcess;
}
