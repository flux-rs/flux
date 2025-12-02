import * as vscode from "vscode";
import type { FluxDef } from "../types";
import { InfoProvider } from "./InfoProvider";

/**
 * Provides go-to-definition functionality for Flux symbols
 */
export class FluxDefinitionProvider implements vscode.DefinitionProvider {
	constructor(
		private readonly _infoProvider: InfoProvider,
		private readonly _context: vscode.ExtensionContext
	) {}

	provideDefinition(
		document: vscode.TextDocument,
		position: vscode.Position,
		token: vscode.CancellationToken
	): vscode.ProviderResult<vscode.Definition | vscode.DefinitionLink[]> {
		const fileName = document.fileName;

		// Convert VS Code 0-based position to 1-based line/column for flux
		const line = position.line + 1;
		const column = position.character + 1;

		// Look up the definition using the info provider
		const fluxDef = this._infoProvider.getDefinition(fileName, line, column);

		if (fluxDef) {
			// Create the source range for the definition link
			const originSelectionRange = new vscode.Range(
				fluxDef.line - 1, // Convert back to 0-based
				fluxDef.column_start - 1, // Convert back to 0-based
				fluxDef.line - 1,
				fluxDef.column_end - 1
			);

			// Create a DefinitionLink with both source and target information
			const definitionLink: vscode.DefinitionLink = {
				originSelectionRange: originSelectionRange,
				targetUri: fluxDef.target.uri,
				targetRange: fluxDef.target.range,
				targetSelectionRange: fluxDef.target.range, // Use the same range for selection
			};

			return [definitionLink];
		}

		// Return undefined if no definition found
		return undefined;
	}
}
