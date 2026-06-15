import LeanFixpoint
import LeanFixpoint.Eval.FusionSearch
import LeanProofs.Flux.Prelude
import LeanProofs.Flux.VC.Append
open Classical
set_option linter.unusedVariables false


namespace F

namespace AppendQualifs

@[qualif]
def EqTrue (n₀ : Prop) : Prop :=
  n₀

@[qualif]
def EqFalse (n₀ : Prop) : Prop :=
  (¬n₀)

@[qualif]
def EqZero (n₀ : Int) : Prop :=
  (n₀ = 0)

@[qualif]
def GtZero (n₀ : Int) : Prop :=
  (n₀ > 0)

@[qualif]
def GeZero (n₀ : Int) : Prop :=
  (n₀ ≥ 0)

@[qualif]
def LtZero (n₀ : Int) : Prop :=
  (n₀ < 0)

@[qualif]
def LeZero (n₀ : Int) : Prop :=
  (n₀ ≤ 0)

@[qualif]
def Eq (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ = a'₁)

@[qualif]
def Gt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ > a'₁)

@[qualif]
def Ge (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≥ a'₁)

@[qualif]
def Lt (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ < a'₁)

@[qualif]
def Le (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ a'₁)

@[qualif]
def Le1 (n₀ : Int) (a'₁ : Int) : Prop :=
  (n₀ ≤ (a'₁ - 1))

end AppendQualifs

open AppendQualifs


end F  -- close namespace F opened by qualifs in head

/-
  RQ3 benchmark prelude. The driver (`scripts/run_rq3.py`) injects everything
  below the `import` line after a benchmark's own imports, then appends two
  theorems wrapped in `benchx`:

    benchx "NAME_A" in theorem NAME_A : VC := by unfold VC; solve_fixpoint
    benchx "NAME_B" in theorem NAME_B : VC := by unfold VC; fusion; all_goals solve_fixpoint

  `benchx` measures the A-vs-B comparison for RQ3:
    • hb     — heartbeats consumed (deterministic; IO.getNumHeartbeats/1000)
    • ms     — wall-clock elaboration (indicative; IO.monoMsNow)
    • depth  — proof-term approxDepth (shape; deterministic term ⇒ shallow)
    • nconst — # distinct constants in the proof term (vocabulary / auditability)
    • kerus  — µs the kernel takes to RE-check the term in isolation (foundational)

  Per-phase heartbeats (`[phase] <tac>:<phase>=<hb>`) come from the gated
  `leanfixpoint.benchPhases` instrumentation, enabled below.
-/
open Lean Elab Command Meta

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option leanfixpoint.benchPhases true

/-- Proof-term shape proxies: (approxDepth, # distinct constants). -/
private def rq3TermMetrics (val : Expr) : Nat × Nat :=
  (val.approxDepth.toNat, val.getUsedConstants.toList.eraseDups.length)

/-- Time (µs) for the kernel to re-check `ci`'s value in isolation, by adding a
    renamed copy under `withoutModifyingEnv`. Returns 0 if there is no value. -/
private def rq3KernelUs (ci : ConstantInfo) : CommandElabM Nat := do
  match ci.value? with
  | none     => return 0
  | some val =>
    let decl := Declaration.thmDecl
      { name := ci.name ++ `__rq3kchk, levelParams := ci.levelParams,
        type := ci.type, value := val }
    let t0 ← IO.monoNanosNow
    try liftCoreM <| withoutModifyingEnv <| addDecl decl
    catch _ => pure ()
    let t1 ← IO.monoNanosNow
    return (t1 - t0) / 1000

elab "benchx " name:str " in" cmd:command : command => do
  let nm := name.getString
  let errsBefore := ((← get).messages.toList.filter (·.severity == .error)).length
  let t0 ← IO.monoMsNow
  let h0 ← IO.getNumHeartbeats
  try elabCommand cmd catch _ => pure ()
  let h1 ← IO.getNumHeartbeats
  let t1 ← IO.monoMsNow
  let errsAfter := ((← get).messages.toList.filter (·.severity == .error)).length
  let status := if errsAfter > errsBefore then "FAIL" else "ok"
  let mut depth := 0
  let mut nconst := 0
  let mut kerus := 0
  if status == "ok" then
    if let some ci := (← getEnv).find? (Name.mkSimple nm) then
      let (d, n) := rq3TermMetrics (ci.value?.getD (mkConst ``True))
      depth := d; nconst := n
      kerus ← rq3KernelUs ci
  logInfo m!"BENCHLINE2 {nm} status={status} hb={(h1-h0)/1000} ms={t1-t0} \
             depth={depth} nconst={nconst} kerus={kerus}"

benchx "Append_proof_zap" in
def Append_proof_zap : F.Append := by
  unfold F.Append
  fusion
  all_goals sorry
