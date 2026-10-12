import Lean

open Lean

run_meta
  let env ← getEnv
  let name := `NativeSourceCapture
  let sortType := Expr.sort (.succ .zero)
  let header := Expr.forallE `A sortType sortType .default
  let ctorType := Expr.forallE `A sortType
    (.forallE `field (.fvar ⟨.num `_nested_fresh 1⟩)
      (mkApp (.const name []) (.bvar 1)) .default) .default
  let ctor : Constructor := { name := name ++ `mk, type := ctorType }
  let decl := Declaration.inductDecl [] 1 [{ name, type := header, ctors := [ctor] }] false
  unless ctorType.hasFVar do throwError "capture reproducer must contain a source free variable"
  match env.addDeclCore 0 1000 decl none with
  | .ok _ => throwError "native kernel unexpectedly accepts the source-capture reproducer"
  | .error (.declHasFVars _ rejectedName rejectedExpr) =>
    unless rejectedName == ctor.name && rejectedExpr == ctorType do
      throwError "native rejection does not identify the original constructor input"
    logInfo "Lean 4.33.0-rc2 rejects the original constructor free variable before source capture"
  | .error error => throwError "unexpected native rejection: {error.toMessageData (← getOptions)}"
