import * as fs from "fs";

/**
 * Get the modification time of a file
 */
export function getFileModificationTime(filePath: string): Date {
    const stats = fs.statSync(filePath);
    return stats.mtime;
}
