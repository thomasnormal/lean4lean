import Lean4Lean.Verify.InductiveMetadata
import Lean4Lean.Verify.InductiveParams

open Lean Lean4Lean Lean4Lean.AddInductive

abbrev HiddenParameterAlias := Type → Type

run_meta
  let env ← Lean.getEnv
  let types : Array InductiveType := #[{
    name := `HiddenParameterDatatype, type := .const ``HiddenParameterAlias [], ctors := [] }]
  let ctx : Context := {
    env := env.toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let checked := checkInductiveTypes 1 types (fun stats => do
    let headers ← declareInductiveTypes stats 1 types 0 false
    withEnv headers do
      checkConstructors types stats false
      declareConstructors stats types false) ctx
  unless checked.isOk do throwError "staged prefix no longer accepts the hidden parameter"
  match Lean4Lean.addDecl env.toKernelEnv (.inductDecl [] 1 types.toList false) with
  | .error (.other message) =>
    unless message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected full-frontend rejection: {message}"
  | _ => throwError "full frontend no longer rejects the hidden parameter"
  match env.addDeclCore 0 (.inductDecl [] 1 types.toList false) none with
  | .error (.other message) =>
    unless message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "unexpected native rejection: {message}"
  | _ => throwError "native kernel no longer rejects the hidden parameter"
