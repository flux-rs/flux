import * as fs from "fs";
import * as readline from "readline";

/**
 * Read events from a log file in streaming fashion
 */
export async function readEventsStreaming(logPath: string): Promise<any[]> {
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
