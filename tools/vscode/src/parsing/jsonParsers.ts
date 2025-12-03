import type {
    NestedString,
    Rcx,
    RcxBind,
    TypeEnv,
    TypeEnvBind,
} from "../types";

/**
 * Collapse consecutive bindings with the same sort
 */
function collapseBindings(bindings: RcxBind[]): RcxBind[] {
    let sort: string = "";
    let names: string[] = [];
    let binds: RcxBind[] = [];
    for (const bind of bindings) {
        if (typeof bind.name === "string") {
            if (bind.sort === sort) {
                // same sort as before
                names.push(bind.name);
            } else {
                // new sort
                if (names.length > 0) {
                    binds.push({ name: names, sort: sort });
                }
                names = [bind.name];
                sort = bind.sort;
            }
        }
    }
    if (names.length > 0) {
        binds.push({ name: names, sort: sort });
    }
    return binds;
}

/**
 * Parse a refinement context (Rcx) from JSON string
 */
export function parseRcx(rcx: string): Rcx {
    const rcxObj = JSON.parse(rcx);
    rcxObj.bindings = collapseBindings(rcxObj.bindings);
    rcxObj.exprs = rcxObj.exprs.map((s: any) => parseNestedString(s));
    return rcxObj;
}

/**
 * Parse a nested string from JSON
 */
export function parseNestedString(s: string): NestedString {
    return JSON.parse(s);
}

/**
 * Parse a type environment from JSON string
 */
export function parseEnv(env: string): TypeEnv {
    return JSON.parse(env)
        .filter((bind: TypeEnvBind) => bind.name)
        .map((b: any) => {
            return {
                name: b.name,
                kind: b.kind,
                ty: parseNestedString(b.ty),
                span: b.span,
            };
        });
}
