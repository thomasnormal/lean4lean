import Lean4Lean.Verify.Expr
import Lean

open Lean

private def nativeInstantiationBoundaries : MetaM Unit := do
  let expression := Expr.bvar 0
  let chronological : Array Expr := #[.sort .zero, .bvar 0]
  let native := expression.instantiateRev chronological
  let structural := expression.instantiateRevList chronological.toList
  unless native == .bvar 0 && structural == .sort .zero && native != structural do
    throwError "historical loose-argument instantiation boundary changed"
  let forward := expression.instantiate chronological.reverse
  unless forward == native && expression.instantiateList chronological.reverse.toList == structural do
    throwError "native reverse/forward boundary changed"
  let underBinder := Expr.lam `binder (.sort .zero) (.bvar 1) .default
  unless underBinder.instantiateRev chronological == underBinder &&
      underBinder.instantiateRevList chronological.toList ==
        .lam `binder (.sort .zero) (.sort .zero) .default do
    throwError "loose-argument boundary beneath a binder changed"
  let closed : List (Array Expr) := [#[], #[.sort .zero], #[.sort .zero, .sort (.succ .zero)],
    #[.fvar ⟨`ClosedFirst⟩, .fvar ⟨`ClosedSecond⟩, .fvar ⟨`ClosedThird⟩]]
  let expressions := [Expr.bvar 0, .bvar 1, .bvar 2, .bvar 3, .sort .zero,
    .app (.bvar 0) (.bvar 2), .lam `binder (.bvar 0) (.app (.bvar 1) (.bvar 3)) .default,
    .forallE `binder (.bvar 1) (.bvar 2) .default,
    .letE `binding (.bvar 1) (.bvar 0) (.app (.bvar 1) (.bvar 3)) true]
  let mut comparisons : Nat := 0
  for replacements in closed do
    for expression in expressions do
      unless expression.instantiate replacements == expression.instantiateList replacements.toList do
        throwError "closed forward instantiation/model comparison failed"
      unless expression.instantiateRev replacements == expression.instantiateRevList replacements.toList do
        throwError "closed reverse instantiation/model comparison failed"
      comparisons := comparisons + 2
  logInfo m!"native instantiation: three loose-argument counterexamples to the existing unscoped sequential specification; {comparisons} closed-argument native/model comparisons; no checker-acceptance or kernel-soundness claim"

run_meta nativeInstantiationBoundaries
