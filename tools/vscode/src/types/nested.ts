import type { StmtSpan } from './flux';

export type NestedString = {
    text: string;
    key?: string;
    children?: NestedString[];
};

// TODO: add local-info to TypeEnvBind
export type TypeEnvBind = {
    name: string | null;
    kind: string;
    ty: NestedString;
    span: StmtSpan;
};

export type TypeEnv = TypeEnvBind[];

export type RcxBind = {
    name: string | string[];
    sort: string;
};

export type Rcx = {
    bindings: RcxBind[];
    exprs: NestedString[];
};