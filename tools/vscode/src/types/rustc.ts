// TypeScript types representing rustc JSON diagnostic format

export interface RustcSpan {
    file_name: string;
    byte_start: number;
    byte_end: number;
    line_start: number;
    line_end: number;
    column_start: number;
    column_end: number;
    is_primary: boolean;
    text: Array<{
        text: string;
        highlight_start: number;
        highlight_end: number;
    }>;
    label?: string;
    suggested_replacement?: string;
    suggestion_applicability?: string;
}

export interface RustcCode {
    code: string;
    explanation?: string;
}

export interface RustcMessage {
    message: string;
    code?: RustcCode;
    level: 'error' | 'warning' | 'note' | 'help' | 'failure-note' | 'ice';
    spans: RustcSpan[];
    children: RustcMessage[];
    rendered?: string;
}

export interface RustcTarget {
    kind: string[];
    crate_types: string[];
    name: string;
    src_path: string;
    edition?: string;
    doctest?: boolean;
}

export interface RustcDiagnostic {
    message: RustcMessage;
    package_id: string;
    manifest_path?: string;
    target: RustcTarget;
}
