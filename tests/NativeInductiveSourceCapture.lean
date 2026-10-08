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
  match env.addDeclCore 0 decl none with
  | .ok added =>
    let some (.ctorInfo stored) := added.find? ctor.name
      | throwError "native capture did not install its constructor"
    let expected := Expr.forallE `A sortType
      (.forallE `field (.bvar 0) (mkApp (.const name []) (.bvar 1)) .default) .default
    unless stored.type == expected && stored.type != ctorType && !stored.type.hasFVar do
      throwError "native constructor no longer exhibits the pinned source-capture bug"
    logInfo "Lean 4.29.0 accepts an unchecked constructor free variable and stores it as a bound parameter"
  | .error _ => throwError "native kernel no longer accepts the pinned source-capture reproducer"
