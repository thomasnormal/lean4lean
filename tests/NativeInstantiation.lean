import Lean4Lean.Verify.Expr
import Lean
import Lean.Util.CollectAxioms

open Lean

namespace NativeInstantiationTest

private theorem correctedRawInterface (expression : Expr) (replacements : Array Expr) :
    expression.instantiate replacements = expression.instantiateMany replacements.toList :=
  Expr.instantiate_eq expression replacements

private theorem looseReplacementIsNotSequential :
    (Expr.bvar 0).instantiateMany [.bvar 0, .sort .zero] ≠
      (Expr.bvar 0).instantiateList [.bvar 0, .sort .zero] := by
  intro equality
  cases equality

private def surroundWithBinders : Nat → Expr → Expr
  | 0, expression => expression
  | depth + 1, expression => .lam `protection (.sort .zero) (surroundWithBinders depth expression) .default

private def simultaneousModelControls : MetaM Unit := do
  let arrays : List (Array Expr) := [#[], #[.sort .zero], #[.bvar 0], #[.bvar 1],
    #[.sort .zero, .bvar 0], #[.bvar 0, .sort .zero], #[.bvar 1, .bvar 0], #[.bvar 0, .bvar 0],
    #[.fvar ⟨`ReplacementFVar⟩, .mvar ⟨`ReplacementMVar⟩],
    #[.app (.bvar 0) (.bvar 1), .lam `identity (.sort .zero) (.bvar 0) .default],
    ((List.range 65).map Expr.bvar).toArray, (List.replicate 65 (Expr.sort .zero)).toArray]
  let expressions : List Expr := [.bvar 0, .bvar 1, .bvar 2, .bvar 3, .bvar 12, .bvar 33, .bvar 64,
    .bvar 65, .bvar (2 ^ 19), .const `Fixture [.param `universe], .sort (.param `universe),
    .fvar ⟨`BodyFVar⟩, .mvar ⟨`BodyMVar⟩, .lit (.natVal 7), .lit (.strVal "fixture"),
    .mdata default (.bvar 1), .proj `Structure 2 (.app (.bvar 0) (.bvar 2)),
    .app (.bvar 0) (.bvar 2), .lam `binder (.bvar 0) (.app (.bvar 1) (.bvar 3)) .default,
    .forallE `binder (.bvar 1) (.bvar 2) .implicit,
    .letE `binding (.bvar 1) (.bvar 0) (.app (.bvar 1) (.bvar 3)) true,
    .letE `binding (.bvar 1) (.bvar 0) (.app (.bvar 1) (.bvar 3)) false]
  let pushed : List Expr := [.sort .zero, .fvar ⟨`PushedFVar⟩, .lam `identity (.sort .zero) (.bvar 0) .default]
  let mut comparisons : Nat := 0
  let mut pushComparisons : Nat := 0
  for depth in [0, 1, 2, 5, 33] do
    for expression in expressions do
      let expression := surroundWithBinders depth expression
      for replacements in arrays do
        unless expression.instantiate replacements == expression.instantiateMany replacements.toList do
          throwError "simultaneous forward instantiation mismatch at depth {depth}"
        unless expression.instantiateRev replacements == expression.instantiateMany replacements.toList.reverse do
          throwError "simultaneous reverse instantiation mismatch at depth {depth}"
        comparisons := comparisons + 2
        for replacement in pushed do
          unless expression.instantiateRev (replacements.push replacement) ==
              (expression.instantiate1 replacement).instantiateRev replacements do
            throwError "closed pushed argument/native instantiation mismatch at depth {depth}"
          pushComparisons := pushComparisons + 1
  logInfo m!"simultaneous instantiation: {comparisons} raw native/model comparisons and {pushComparisons} closed-push comparisons; loose/mixed/wide arrays, large representable indices, all constructors and binder depths 0/1/2/5/33"

private def audit (name : Name) (allowed : List Name) : MetaM Unit := do
  let dependencies ← collectAxioms name
  for dependency in dependencies do
    unless allowed.contains dependency do throwError "native instantiation unexpected dependency {dependency} in {name}"
  logInfo m!"{name}: {dependencies.size} logical/existing-native dependencies"

private def nativeInstantiationBoundaries : MetaM Unit := do
  let expression := Expr.bvar 0
  let chronological : Array Expr := #[.sort .zero, .bvar 0]
  let native := expression.instantiateRev chronological
  let structural := expression.instantiateRevList chronological.toList
  unless native == .bvar 0 && structural == .sort .zero && native != structural do
    throwError "historical loose-argument instantiation boundary changed"
  let loosePush := (expression.instantiate1 (.bvar 0)).instantiateRev #[.sort .zero]
  unless loosePush == .sort .zero && loosePush != native do
    throwError "loose pushed argument must remain outside the scoped push identity"
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
  logInfo m!"native instantiation: three historical loose-argument counterexamples to the retired sequential specification plus one loose-push negative; {comparisons} closed-argument sequential comparisons; no checker-acceptance or kernel-soundness claim"

run_meta do
  let logical := [``propext, ``Classical.choice, ``Quot.sound]
  let pureControls := [``Expr.instantiateMany_nil, ``Expr.instantiateMany_eq_self,
    ``Expr.instantiateMany_singleton, ``Expr.instantiateMany_cons,
    ``Expr.instantiateMany_eq_instantiateList, ``Expr.instantiateMany_looseBVarRange,
    ``Expr.instantiateMany_fvars, ``Expr.mkAppRevList_args_noLooseBVars,
    ``looseReplacementIsNotSequential]
  for name in pureControls do audit name logical
  audit ``Expr.instantiateMany logical
  audit ``correctedRawInterface (logical ++ [``Expr.instantiate_eq])
  audit ``Expr.instantiate_eq_of_closed (logical ++ [``Expr.instantiate_eq])
  for name in [``Expr.instantiateRev_eq_of_closed, ``Expr.instantiateRev_push] do
    audit name (logical ++ [``Expr.instantiate_eq, ``Expr.instantiateRev_eq])
  nativeInstantiationBoundaries
  simultaneousModelControls
  logInfo m!"native instantiation: {pureControls.length} admission-free structural proof controls plus model definition and four existing-native interface controls audited"

end NativeInstantiationTest
