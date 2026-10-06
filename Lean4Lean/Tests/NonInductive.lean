import Lean4Lean.Verify.Environment

namespace Lean4Lean.Tests.NonInductive

open Lean

private def carrier : Expr := .const `Checkpoint.A [.param `u]
private def identityType : Expr := .forallE `x carrier carrier .default
private def identityValue : Expr := .lam `x carrier (.bvar 0) .default

private def declarations : List Declaration := [
  .axiomDecl {
    name := `Checkpoint.A, levelParams := [`u], type := .sort (.param `u), isUnsafe := false },
  .defnDecl {
    name := `Checkpoint.id, levelParams := [`u], type := identityType,
    value := identityValue, hints := .abbrev, safety := .safe },
  .opaqueDecl {
    name := `Checkpoint.opaqueId, levelParams := [`u], type := identityType,
    value := identityValue, isUnsafe := false },
  .thmDecl {
    name := `Checkpoint.idProof, levelParams := [],
    type := .forallE `p (.sort .zero) (.forallE `h (.bvar 0) (.bvar 1) .default) .default,
    value := .lam `p (.sort .zero) (.lam `h (.bvar 0) (.bvar 0) .default) .default },
  .defnDecl {
    name := `Checkpoint.recursive, levelParams := [`u], type := identityType,
    value := .const `Checkpoint.recursive [.param `u], hints := .opaque, safety := .unsafe },
  .mutualDefnDecl [
    {
      name := `Checkpoint.first, levelParams := [`u], type := identityType,
      value := .const `Checkpoint.second [.param `u], hints := .opaque, safety := .partial },
    {
      name := `Checkpoint.second, levelParams := [`u], type := identityType,
      value := .const `Checkpoint.first [.param `u], hints := .opaque, safety := .partial }]]

run_meta
  let start := Kernel.Environment.empty `Checkpoint (stage₁ := true)
  let env ← match declarations.foldlM addDeclVerified start with
    | .ok env => pure env
    | .error e => throwError "checkpoint failed: {e.toMessageData {}}"
  for n in [`Checkpoint.A, `Checkpoint.id, `Checkpoint.opaqueId, `Checkpoint.idProof,
      `Checkpoint.recursive, `Checkpoint.first, `Checkpoint.second] do
    unless (env.find? n).isSome do throwError "missing declaration {n}"
  let p := Level.param `p
  let q := Level.param `q
  let compareLevels (u v : Level) := TypeChecker.M.run env (lparams := [`p, `q])
    (x := TypeChecker.isDefEq (.const `Checkpoint.A [u]) (.const `Checkpoint.A [v]))
  -- Check the actual constant-comparison path, not just the list helper.
  match compareLevels (.max p q) (.max q p) with
  | .ok true => pure ()
  | _ => throwError "standard level equivalence was rejected"
  match compareLevels (.max p q) (.max (.imax q p) q) with
  | .ok false => pure ()
  | _ => throwError "constant comparison used the complete level fallback"
  match addDeclVerified env declarations.head! with
  | .error _ => pure ()
  | .ok _ => throwError "duplicate declaration was accepted"
  let bad : Declaration := .defnDecl {
    name := `Checkpoint.bad, levelParams := [`u], type := carrier,
    value := .sort .zero, hints := .abbrev, safety := .safe }
  match addDeclVerified env bad with
  | .error _ => pure ()
  | .ok _ => throwError "ill-typed definition was accepted"
  match addDeclVerified start (.inductDecl [] 0 [] false) with
  | .error (.other "inductive declarations are outside the verified fragment") => pure ()
  | _ => throwError "inductives were not rejected at the fragment boundary"

-- Initialization and composition describe the same entry point exercised above.
example : (declarations.foldlM addDeclVerified
    (Kernel.Environment.empty `Checkpoint (stage₁ := true))).WF fun env =>
      ∃ ves : VEnvs, ves.WF env :=
  addDeclVerified.fromEmpty `Checkpoint declarations

example (ves : VEnvs) : ¬ves.WF (Kernel.Environment.empty `Checkpoint) :=
  VEnvs.WF.not_empty_stage₂ `Checkpoint

end Lean4Lean.Tests.NonInductive
