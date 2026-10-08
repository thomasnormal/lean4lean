import Lean4Lean.Verify.InductiveParamBinding
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive

namespace NativeAbstractionTest

theorem indexBound (id : FVarId) (ids : List FVarId) (index : Nat)
    (hindex : Expr.abstractFVarIndex id ids = some index) : index < ids.length :=
  Expr.abstractFVarIndex_lt hindex

theorem emptyModel (body : Expr) (depth : Nat) : body.abstractFVars [] depth = body :=
  Expr.abstractFVars_nil body depth

theorem consModel (body : Expr) (head : FVarId) (tail : List FVarId) (depth : Nat)
    (hscope : body.looseBVarRange' ≤ depth) :
    body.abstractFVars (head :: tail) depth =
      (body.abstractFVars tail depth).abstract1 head (depth + tail.length) :=
  Expr.abstractFVars_cons hscope

theorem scopedModel (body : Expr) (ids : List FVarId) (depth : Nat)
    (hscope : body.looseBVarRange' ≤ depth) (hnodup : ids.Nodup) :
    body.abstractFVars ids depth = body.abstractList ids depth :=
  Expr.abstractFVars_eq_abstractList hscope hnodup

theorem scopedNative (body : Expr) (ids : List FVarId)
    (hscope : body.looseBVarRange' = 0) (hnodup : ids.Nodup) :
    body.abstract (ids.map Expr.fvar).toArray = body.abstractList ids :=
  Expr.abstract_eq_of_scope hscope hnodup

theorem rawArity (body : Expr) (ids : List FVarId) (index depth : Nat) :
    AddInductive.declareConstructors.arity index (body.abstractFVars ids depth) =
      AddInductive.declareConstructors.arity index body :=
  arity_abstractFVars body ids index depth

theorem nativeArity (body : Expr) (ids : List FVarId) (index : Nat) :
    AddInductive.declareConstructors.arity index (body.abstract (ids.map Expr.fvar).toArray) =
      AddInductive.declareConstructors.arity index body :=
  arity_abstract body ids index

theorem nativeModel (body : Expr) (ids : List FVarId) :
    body.abstract (ids.map Expr.fvar).toArray = body.abstractFVars ids :=
  Expr.abstract_eq body ids

example (ids : List FVarId) (index depth : Nat) :
    (Expr.bvar index).abstractFVars ids depth = .bvar index := rfl

example (ids : List FVarId) (id : MVarId) (depth : Nat) :
    (Expr.mvar id).abstractFVars ids depth = .mvar id := rfl

example (id : FVarId) (depth : Nat) :
    (Expr.fvar id).abstractFVars [id, id] depth = .bvar depth := by
  simp [Expr.abstractFVars, Expr.abstractFVarIndex]

example (id : FVarId) :
    (Expr.fvar id).abstractList [id, id] = .bvar 1 := by
  simp [Expr.abstractList, Expr.abstract1]

example (id : FVarId) :
    (Expr.bvar 0).abstractFVars [id] ≠ (Expr.bvar 0).abstractList [id] := by
  simp [Expr.abstractFVars, Expr.abstractList, Expr.abstract1]

example (id : MVarId) (ids : List FVarId) (hnodup : ids.Nodup) :
    (Expr.mvar id).abstractFVars ids = (Expr.mvar id).abstractList ids :=
  Expr.abstractFVars_eq_abstractList (by simp [Expr.looseBVarRange']) hnodup

private def fixtureId (index : Nat) : FVarId := ⟨Name.mkNum `NativeAbstract index⟩

private def idFixtures : List (List FVarId) :=
  let first := fixtureId 0
  let second := fixtureId 1
  let third := fixtureId 2
  let wide := (List.range 65).map fixtureId
  [[], [first], [second], [first, second], [second, first], [first, first],
    [first, second, first], [second, first, first], [first, first, second],
    [first, second, third, first, second], wide, first :: wide ++ [first]]

private def bodyFixtures (ids : List FVarId) : List Expr :=
  let first := Expr.fvar (fixtureId 0)
  let second := Expr.fvar (fixtureId 1)
  let third := Expr.fvar (fixtureId 2)
  let application := mkApp first second
  let openBody := mkApp first (.bvar 1)
  [.sort (.succ .zero), .lit (.natVal 7), .const `NativeAbstractConst [.param `u],
    .bvar 0, .bvar 1, .bvar 65, first, second, third,
    .mvar ⟨(fixtureId 0).name⟩, .mvar ⟨`ExternalMeta⟩, application,
    .forallE `inner second openBody .implicit,
    .lam `inner second (mkApp first (.bvar 0)) .strictImplicit,
    .letE `inner second third openBody false,
    .letE `inner second third openBody true,
    .mdata {} first, .proj `NativeAbstractPair 0 second,
    mkAppN (.const `NativeAbstractFamily []) (ids.map Expr.fvar).toArray]

private def underBinders (depth : Nat) (body : Expr) : Expr :=
  (List.range depth).foldr (fun index result =>
    .forallE (Name.mkNum `depth index) (.fvar (fixtureId 1)) result .instImplicit) body

private def checkFixture (ids : List FVarId) (body : Expr) : MetaM Bool := do
  let actual := body.abstract (ids.map Expr.fvar).toArray
  let modeled := body.abstractFVars ids
  unless actual == modeled do
    throwError "raw native abstraction mismatch: ids={repr ids}, body={repr body}"
  for index in [0, 1, 7] do
    unless AddInductive.declareConstructors.arity index actual ==
        AddInductive.declareConstructors.arity index body do
      throwError "native abstraction changed leading binder count"
  let isScoped := body.looseBVarRange' == 0 && ids.eraseDups.length == ids.length
  if isScoped then
    unless actual == body.abstractList ids do
      throwError "scoped/distinct native abstraction disagrees with sequential model"
  return isScoped

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``indexBound, ``emptyModel, ``consModel, ``scopedModel,
      ``rawArity, ``Expr.abstractFVarIndex_lt, ``Expr.abstractFVars_nil,
      ``Expr.abstractFVars_cons, ``Expr.abstractFVars_eq_abstractList, ``arity_abstractFVars] do
    audit theoremName []
  for theoremName in [``scopedNative, ``nativeArity, ``nativeModel,
      ``Expr.abstract_eq_of_scope, ``arity_abstract] do
    audit theoremName [``Expr.abstract_eq]
  let mut fixtures := 0
  let mut scopedFixtures := 0
  for ids in idFixtures do
    for body in bodyFixtures ids do
      for depth in [0, 1, 2, 33] do
        if ← checkFixture ids (underBinders depth body) then
          scopedFixtures := scopedFixtures + 1
        fixtures := fixtures + 1
  logInfo m!"checked {fixtures} raw native/model fixtures, {3 * fixtures} native arity checks, and {scopedFixtures} scoped/distinct sequential comparisons"

end NativeAbstractionTest
