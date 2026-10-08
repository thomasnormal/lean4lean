import Lean4Lean.Verify.TypeChecker.Basic
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.TypeChecker

namespace BindingScopeTest

theorem scopeOfWF (c : MLCtx) (hwf : c.WF env Us) : c.lctx.BindingScope :=
  hwf.bindingScope

theorem typeScopeOfWF (c : MLCtx) (hwf : c.WF env Us)
    (hlookup : c.lctx.find? fvar = some decl) : decl.type.looseBVarRange' = 0 :=
  (hwf.bindingScope fvar decl hlookup).1

theorem valueScopeOfWF (c : MLCtx) (hwf : c.WF env Us)
    (hlookup : c.lctx.find? fvar = some decl)
    (hvalue : decl.value? (allowNondep := true) = some value) :
    value.looseBVarRange' = 0 :=
  (hwf.bindingScope fvar decl hlookup).2 value hvalue

theorem bindingOfScope (lctx : LocalContext) (xs : List FVarId) (body : Expr)
    (isLambda : Bool) (hbody : body.looseBVarRange' = 0)
    (hscope : lctx.BindingScope) (hnodup : xs.Nodup) :
    lctx.mkBinding isLambda (xs.map Expr.fvar).toArray body =
      lctx.mkBindingList isLambda xs body :=
  LocalContext.mkBinding_eq hbody hscope hnodup

theorem partialForallOfWF (c : MLCtx) (hwf : c.WF env Us) (num : Nat)
    (hnum : num ≤ c.length) (arr : Array Expr) (xs : List FVarId) (body : Expr)
    (harr : arr.toList.reverse = xs.map Expr.fvar)
    (hpartial : c.PartialForall num xs body) (hbody : body.looseBVarRange' = 0) :
    c.lctx.mkForall arr body = c.mkForall num hnum body :=
  hwf.mkForall_partial num hnum harr hpartial hbody

theorem forallOfWF (c : MLCtx) (hwf : c.WF env Us) (num : Nat)
    (hnum : num ≤ c.length) (arr : Array Expr) (body : Expr)
    (harr : arr.toList.reverse = (c.fvarRevList num hnum).map Expr.fvar)
    (hbody : body.looseBVarRange' = 0) :
    c.lctx.mkForall arr body = c.mkForall num hnum body :=
  hwf.mkForall_eq num hnum harr hbody

theorem lambdaOfWF (c : MLCtx) (hwf : c.WF env Us) (num : Nat)
    (hnum : num ≤ c.length) (arr : Array Expr) (body : Expr)
    (harr : arr.toList.reverse = (c.fvarRevList num hnum).map Expr.fvar)
    (hbody : body.looseBVarRange' = 0) :
    c.lctx.mkLambda arr body = c.mkLambda num hnum body :=
  hwf.mkLambda_eq num hnum harr hbody

theorem emptyScope : ({} : LocalContext).BindingScope := by
  intro fvar decl hlookup
  rw [LocalContext.WF.find?_eq_find?_toList (lctx := {}) .nil] at hlookup
  cases hlookup

example (body : Expr) (hbody : body.looseBVarRange' = 0) :
    ({} : LocalContext).mkBinding false #[] body = body := by
  simpa [LocalContext.mkBindingList, LocalContext.mkBindingList.go] using
    bindingOfScope {} [] body false hbody emptyScope (by simp)

example : (Expr.bvar 0).looseBVarRange' ≠ 0 := by decide

example (lctx : LocalContext) (fvar : FVarId) (decl : LocalDecl)
    (hlookup : lctx.find? fvar = some decl) (htype : decl.type = .bvar 0) :
    ¬ lctx.BindingScope := by
  intro hscope
  have hzero := (hscope fvar decl hlookup).1
  simp [htype, Expr.looseBVarRange'] at hzero

example (lctx : LocalContext) (fvar : FVarId) (decl : LocalDecl)
    (hlookup : lctx.find? fvar = some decl)
    (hvalue : decl.value? (allowNondep := true) = some (.bvar 0)) :
    ¬ lctx.BindingScope := by
  intro hscope
  have hzero := (hscope fvar decl hlookup).2 (.bvar 0) hvalue
  simp [Expr.looseBVarRange'] at hzero

example (fvar : FVarId) : ¬ [fvar, fvar].Nodup := by simp

private def fixtureId (index : Nat) : FVarId := ⟨Name.mkNum `BindingScoped index⟩

private def fixtureContext (count : Nat) (withLets : Bool) : MLCtx :=
  (List.range count).foldl (fun context index =>
    let name := if index % 2 = 0 then Name.anonymous else `repeated
    let sortType := Expr.sort (.succ .zero)
    let domain := if index = 0 then sortType else .fvar (fixtureId (index - 1))
    let bi := match index % 4 with
      | 0 => BinderInfo.implicit
      | 1 => .strictImplicit
      | 2 => .instImplicit
      | _ => .default
    if withLets && index % 3 = 2 then
      .vlet (fixtureId index) name domain (.fvar (fixtureId (index - 1)))
        (.sort .zero) (.sort .zero) context
    else .vlam (fixtureId index) name domain (.sort .zero) bi context) .nil

private def fixtureBodies (params : Array Expr) : List Expr :=
  let sortType := Expr.sort (.succ .zero)
  let dependent := mkAppN (.const `ScopedFamily []) params
  let binderBody := mkApp dependent (.bvar 0)
  [sortType, .fvar ⟨`Outside⟩, .mvar ⟨`Unassigned⟩, dependent,
    .forallE `inner sortType binderBody .implicit,
    .lam `inner sortType binderBody .strictImplicit,
    .letE `inner sortType dependent binderBody false,
    .mdata {} dependent, .proj `ScopedPair 0 dependent, .lit (.natVal 7)]

private def checkContext (context : MLCtx) : MetaM Unit := do
  for decl in context.decls do
    unless decl.type.looseBVarRange' == 0 do
      throwError "binding fixture contains a loose declaration domain"
    if let some value := decl.value? (allowNondep := true) then
      unless value.looseBVarRange' == 0 do
        throwError "binding fixture contains a loose let value"

private def checkBinding (context : MLCtx) (body : Expr) (isLambda : Bool) : MetaM Unit := do
  let xs := (context.fvarRevList context.length (Nat.le_refl _)).reverse
  let params := (xs.map Expr.fvar).toArray
  unless body.looseBVarRange' == 0 do
    throwError "binding fixture contains a loose body"
  let actual := context.lctx.mkBinding isLambda params body
  let structural := context.lctx.mkBindingList isLambda xs body
  let typed := if isLambda then context.mkLambda context.length (Nat.le_refl _) body
    else context.mkForall context.length (Nat.le_refl _) body
  unless actual == structural && actual == typed do
    throwError "scoped binding mismatch: count={params.size}, lambda={isLambda}"

private def checkLooseBody (count : Nat) (isLambda : Bool) : MetaM Unit := do
  let context := fixtureContext count false
  let xs := (context.fvarRevList context.length (Nat.le_refl _)).reverse
  let body := Expr.bvar 0
  let actual := context.lctx.mkBinding isLambda (xs.map Expr.fvar).toArray body
  let structural := context.lctx.mkBindingList isLambda xs body
  let typed := if isLambda then context.mkLambda context.length (Nat.le_refl _) body
    else context.mkForall context.length (Nat.le_refl _) body
  unless actual != structural && actual != typed do
    throwError "loose-body boundary failed to expose both reconstruction mismatches"

private def checkLooseDeclaration (letValue isLambda : Bool) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let base := MLCtx.vlam (fixtureId 0) `first sortType (.sort .zero) .default .nil
  let context := if letValue then
    MLCtx.vlet (fixtureId 1) `second sortType (.bvar 0) (.sort .zero) (.sort .zero) base
    else MLCtx.vlam (fixtureId 1) `second (.bvar 0) (.sort .zero) .default base
  let xs := [fixtureId 0, fixtureId 1]
  let body := Expr.fvar (fixtureId 1)
  let actual := context.lctx.mkBinding isLambda (xs.map Expr.fvar).toArray body
  let structural := context.lctx.mkBindingList isLambda xs body
  unless body.looseBVarRange' == 0 && actual != structural do
    throwError "loose-domain/value boundary failed to expose indexed abstraction mismatch"

private def checkDuplicateId (isLambda : Bool) : MetaM Unit := do
  let fvar := fixtureId 0
  let xs := [fvar, fvar]
  let body := Expr.fvar fvar
  let params := (xs.map Expr.fvar).toArray
  let lctx := ({} : LocalContext).mkLocalDecl fvar `duplicate (.sort (.succ .zero))
  unless body.looseBVarRange' == 0 && body.abstract params == .bvar 0 &&
      body.abstractList xs == .bvar 1 &&
      lctx.mkBinding isLambda params body != lctx.mkBindingList isLambda xs body do
    throwError "duplicate-ID boundary failed to distinguish native last match from model first match"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let contextInterfaces := [``PersistentHashMap.WF.find?_eq,
    ``PersistentArray.toList'_push, ``PersistentHashMap.WF.toList'_insert]
  audit ``emptyScope contextInterfaces
  let typedInterfaces := ``sorryAx :: contextInterfaces
  for theoremName in [``scopeOfWF, ``typeScopeOfWF, ``valueScopeOfWF,
      ``MLCtx.WF.bindingScope] do
    audit theoremName typedInterfaces
  let bindingInterfaces := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  for theoremName in [``bindingOfScope, ``LocalContext.mkBinding_eq] do
    audit theoremName bindingInterfaces
  for theoremName in [``partialForallOfWF, ``forallOfWF, ``lambdaOfWF,
      ``MLCtx.WF.mkForall_partial, ``MLCtx.WF.mkForall_eq, ``MLCtx.WF.mkLambda_eq] do
    audit theoremName (typedInterfaces ++ bindingInterfaces)
  for count in [0, 1, 2, 3, 31, 32, 33, 65] do
    for withLets in [false, true] do
      let context := fixtureContext count withLets
      checkContext context
      let params := (context.decls.reverse.map fun decl => Expr.fvar decl.fvarId).toArray
      for body in fixtureBodies params do
        for isLambda in [false, true] do
          checkBinding context body isLambda
  for isLambda in [false, true] do
    for count in [1, 2] do
      checkLooseBody count isLambda
    checkLooseDeclaration false isLambda
    checkLooseDeclaration true isLambda
    checkDuplicateId isLambda
  logInfo "checked 320 scoped forall/lambda fixtures against both reconstruction models; 10 premise boundaries"

end BindingScopeTest
