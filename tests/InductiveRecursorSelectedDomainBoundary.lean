import Lean4Lean.Verify.InductiveIndexDomainSupport
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveRecursorSelectedDomainBoundaryTest

/-- Binder integrity proves the native index-domain free-variable boundary.  This is
    the strongest selected-domain fact available before a semantic model is supplied. -/
example {stats : InductiveStats} {types : Array InductiveType}
    {checkedRoot current : Context} {infos : Array RecInfo} {base : List FVarId}
    (integrity : RecursorBinderIntegrity stats types checkedRoot current infos)
    (parameters : stats.params.toList.map Expr.fvarId! ⊆ base) :
    ∀ parent, parent < types.size →
      SelectedRecursorDomainFVars current.lctx base (infos[parent]!.indices.toList.map Expr.fvarId!) :=
  integrity.selectedIndexDomains parameters

/-- A selected-domain support receipt is strictly semantic: it supplies the
    chronological prefix model, translated domain, and typehood for each selected
    binder.  Native cdecl/index integrity alone does not contain these fields. -/
example {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext} {initial : TypeChecker.MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent full initial) :
    ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
      ∃ projected, SelectedRecursorTelescope env universes full initial ids projected ∧
        ∀ identifier, identifier ∈ ids →
          ∃ preIds suffix model physicalIndex name domain binder semantic,
            ids = preIds ++ identifier :: suffix ∧
            SelectedRecursorTelescope env universes full initial preIds model ∧
            full.find? identifier =
              some (.cdecl physicalIndex identifier name domain binder .default) ∧
            model.lctx.find? identifier = none ∧
            TrExprS env universes model.vlctx domain semantic ∧
            env.IsType universes.length model.vlctx.toCtx semantic := by
  exact support.domainReceipts

/-- Grouped type support also exposes the source free-variable obligation. -/
example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {grouped : List FVarId} {body : Expr}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial grouped body) :
    FVarsIn (· ∈ initial.vlctx.fvars)
      (full.mkForall (grouped.map Expr.fvar).toArray body) :=
  support.initialFVarsIn

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {grouped : List FVarId} {body : Expr}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial grouped body)
    {identifier : FVarId}
    (missing : identifier ∉ initial.vlctx.fvars)
    (present : identifier ∈
      (full.mkForall (grouped.map Expr.fvar).toArray body).fvarsList) : False :=
  support.noMissingFVar missing present

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {identifier target : FVarId} {rest : List FVarId}
    {body : Expr} {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial
      (identifier :: rest) body)
    (scope : full.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : (identifier :: rest).Nodup)
    (bindings : SelectedCDeclBindings full (identifier :: rest))
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (present : target ∈ domain.fvarsList)
    (missing : target ∉ initial.vlctx.fvars) : False :=
  support.noMissingDomainFVar scope closed distinct bindings lookup present missing

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {context : VLCtx} {identifier : FVarId} {inner : Expr}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    {semanticDomain semanticBody : VExpr}
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (domainTranslated : TrExprS env universes context domain semanticDomain)
    (domainTyped : env.IsType universes.length context.toCtx semanticDomain)
    (bodyTranslated : TrExprS env universes
      ((none, .vlam semanticDomain) :: context : VLCtx)
      (inner.abstract1 identifier) semanticBody)
    (bodyTyped : env.IsType universes.length
      (VLCtx.toCtx ((none, .vlam semanticDomain) :: context)) semanticBody) :
    TrExprS env universes context
      (full.mkBindingList1 false [] identifier (inner.abstract1 identifier))
      (.forallE semanticDomain semanticBody) ∧
    env.IsType universes.length context.toCtx (.forallE semanticDomain semanticBody) :=
  RecursorGroupedTypeTranslationSupport.headStep lookup domainTranslated domainTyped
    bodyTranslated bodyTyped

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {context : VLCtx} {identifier : FVarId} {inner : Expr}
    {dependencies : List FVarId}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    {semanticDomain semanticBody : VExpr}
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (domainTranslated : TrExprS env universes context domain semanticDomain)
    (domainTyped : env.IsType universes.length context.toCtx semanticDomain)
    (bodyTranslated : TrExprS env universes
      ((some (identifier, dependencies), .vlam semanticDomain) :: context : VLCtx)
      inner semanticBody)
    (bodyTyped : env.IsType universes.length
      (VLCtx.toCtx ((some (identifier, dependencies), .vlam semanticDomain) :: context))
      semanticBody) :
    TrExprS env universes context
      (full.mkBindingList1 false [] identifier (inner.abstract1 identifier))
      (.forallE semanticDomain semanticBody) ∧
    env.IsType universes.length context.toCtx (.forallE semanticDomain semanticBody) :=
  RecursorGroupedTypeTranslationSupport.headStepOfNamedBody lookup domainTranslated domainTyped
    bodyTranslated bodyTyped

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {identifier : FVarId} {rest : List FVarId}
    {body : Expr} {dependencies : List FVarId}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    {semanticDomain semanticTail : VExpr}
    (scope : full.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : (identifier :: rest).Nodup)
    (bindings : SelectedCDeclBindings full (identifier :: rest))
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (domainTranslated : TrExprS env universes initial.vlctx domain semanticDomain)
    (domainTyped : env.IsType universes.length initial.vlctx.toCtx semanticDomain)
    (tailTranslated : TrExprS env universes
      ((some (identifier, dependencies), .vlam semanticDomain) :: initial.vlctx : VLCtx)
      (full.mkForall (rest.map Expr.fvar).toArray body) semanticTail)
    (tailTyped : env.IsType universes.length
      (VLCtx.toCtx
        ((some (identifier, dependencies), .vlam semanticDomain) :: initial.vlctx))
      semanticTail) :
    RecursorGroupedTypeTranslationSupport env universes full initial
      (identifier :: rest) body :=
  RecursorGroupedTypeTranslationSupport.namedTail scope closed distinct bindings lookup
    domainTranslated domainTyped tailTranslated tailTyped

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {identifier : FVarId} {rest : List FVarId}
    {body : Expr} {dependencies : List FVarId}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial
      (identifier :: rest) body)
    (scope : full.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : (identifier :: rest).Nodup)
    (bindings : SelectedCDeclBindings full (identifier :: rest))
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (fresh : identifier ∉ initial.vlctx.fvars) :
    ∃ semanticDomain semanticTail,
      TrExprS env universes initial.vlctx domain semanticDomain ∧
      env.IsType universes.length initial.vlctx.toCtx semanticDomain ∧
      TrExprS env universes
        ((some (identifier, dependencies), .vlam semanticDomain) :: initial.vlctx : VLCtx)
        (full.mkForall (rest.map Expr.fvar).toArray body) semanticTail ∧
      env.IsType universes.length
        (VLCtx.toCtx
          ((some (identifier, dependencies), .vlam semanticDomain) :: initial.vlctx))
        semanticTail :=
  RecursorGroupedTypeTranslationSupport.namedTailNecessary support scope closed distinct bindings
    lookup fresh

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {identifier : FVarId} {rest : List FVarId}
    {body : Expr} {dependencies : List FVarId}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial
      (identifier :: rest) body)
    (scope : full.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : (identifier :: rest).Nodup)
    (bindings : SelectedCDeclBindings full (identifier :: rest))
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (fresh : identifier ∉ initial.vlctx.fvars)
    {target : FVarId}
    (present : target ∈ (full.mkForall (rest.map Expr.fvar).toArray body).fvarsList) :
    target = identifier ∨ target ∈ initial.vlctx.fvars :=
  RecursorGroupedTypeTranslationSupport.namedTailFVarBoundary support scope closed distinct
    bindings lookup fresh (dependencies := dependencies) present

example {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial : TypeChecker.MLCtx} {identifier : FVarId} {rest : List FVarId}
    {body : Expr} {dependencies : List FVarId}
    {index : Nat} {name : Name} {domain : Expr} {binder : BinderInfo}
    (support : RecursorGroupedTypeTranslationSupport env universes full initial
      (identifier :: rest) body)
    (scope : full.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : (identifier :: rest).Nodup)
    (bindings : SelectedCDeclBindings full (identifier :: rest))
    (lookup : full.find? identifier =
      some (.cdecl index identifier name domain binder .default))
    (fresh : identifier ∉ initial.vlctx.fvars)
    {target : FVarId}
    (missing : target ∉ initial.vlctx.fvars)
    (different : target ≠ identifier)
    (present : target ∈ (full.mkForall (rest.map Expr.fvar).toArray body).fvarsList) : False :=
  RecursorGroupedTypeTranslationSupport.namedTailNoMissingFVar support scope closed distinct
    bindings lookup fresh (dependencies := dependencies) missing different present

run_meta
  let fvarTheorem := ``RecursorBinderIntegrity.selectedIndexDomains
  let fvarAxioms ← collectAxioms fvarTheorem
  if fvarAxioms.contains ``sorryAx then
    throwError "index-domain integrity boundary depends on sorryAx"
  let semanticTheorem := ``RecursorSelectedDomainSupport.domainReceipts
  let semanticInfo ← getConstInfo semanticTheorem
  if semanticInfo matches .axiomInfo _ then
    throwError "semantic selected-domain boundary is not theorem-backed"
  let some semanticProof := semanticInfo.value? (allowOpaque := true) |
    throwError "semantic selected-domain boundary proof missing"
  if semanticProof.hasSorry then
    throwError "semantic selected-domain boundary has an admission"
  let groupedTheorem := ``RecursorGroupedTypeTranslationSupport.noMissingFVar
  let groupedInfo ← getConstInfo groupedTheorem
  if groupedInfo matches .axiomInfo _ then
    throwError "grouped source-scope boundary is not theorem-backed"
  let some groupedProof := groupedInfo.value? (allowOpaque := true) |
    throwError "grouped source-scope boundary proof missing"
  if groupedProof.hasSorry then
    throwError "grouped source-scope boundary has an admission"
  let groupedDomainTheorem := ``RecursorGroupedTypeTranslationSupport.noMissingDomainFVar
  let groupedDomainInfo ← getConstInfo groupedDomainTheorem
  if groupedDomainInfo matches .axiomInfo _ then
    throwError "grouped domain-scope boundary is not theorem-backed"
  let some groupedDomainProof := groupedDomainInfo.value? (allowOpaque := true) |
    throwError "grouped domain-scope boundary proof missing"
  if groupedDomainProof.hasSorry then
    throwError "grouped domain-scope boundary has an admission"
  let groupedHeadTheorem := ``RecursorGroupedTypeTranslationSupport.headStep
  let groupedHeadInfo ← getConstInfo groupedHeadTheorem
  if groupedHeadInfo matches .axiomInfo _ then
    throwError "grouped head transport is not theorem-backed"
  let some groupedHeadProof := groupedHeadInfo.value? (allowOpaque := true) |
    throwError "grouped head transport proof missing"
  if groupedHeadProof.hasSorry then
    throwError "grouped head transport has an admission"
  let groupedNamedHeadTheorem := ``RecursorGroupedTypeTranslationSupport.headStepOfNamedBody
  let groupedNamedHeadInfo ← getConstInfo groupedNamedHeadTheorem
  if groupedNamedHeadInfo matches .axiomInfo _ then
    throwError "named grouped head transport is not theorem-backed"
  let some groupedNamedHeadProof := groupedNamedHeadInfo.value? (allowOpaque := true) |
    throwError "named grouped head transport proof missing"
  if groupedNamedHeadProof.hasSorry then
    throwError "named grouped head transport has an admission"
  let groupedNamedTailTheorem := ``RecursorGroupedTypeTranslationSupport.namedTail
  let groupedNamedTailInfo ← getConstInfo groupedNamedTailTheorem
  if groupedNamedTailInfo matches .axiomInfo _ then
    throwError "named grouped tail support is not theorem-backed"
  let some groupedNamedTailProof := groupedNamedTailInfo.value? (allowOpaque := true) |
    throwError "named grouped tail support proof missing"
  if groupedNamedTailProof.hasSorry then
    throwError "named grouped tail support has an admission"
  let groupedNamedTailNecessaryTheorem := ``RecursorGroupedTypeTranslationSupport.namedTailNecessary
  let groupedNamedTailNecessaryInfo ← getConstInfo groupedNamedTailNecessaryTheorem
  if groupedNamedTailNecessaryInfo matches .axiomInfo _ then
    throwError "necessary named grouped tail support is not theorem-backed"
  let some groupedNamedTailNecessaryProof := groupedNamedTailNecessaryInfo.value? (allowOpaque := true) |
    throwError "necessary named grouped tail support proof missing"
  if groupedNamedTailNecessaryProof.hasSorry then
    throwError "necessary named grouped tail support has an admission"
  let groupedNamedTailBoundaryTheorem := ``RecursorGroupedTypeTranslationSupport.namedTailFVarBoundary
  let groupedNamedTailBoundaryInfo ← getConstInfo groupedNamedTailBoundaryTheorem
  if groupedNamedTailBoundaryInfo matches .axiomInfo _ then
    throwError "named grouped tail FVar boundary is not theorem-backed"
  let some groupedNamedTailBoundaryProof := groupedNamedTailBoundaryInfo.value? (allowOpaque := true) |
    throwError "named grouped tail FVar boundary proof missing"
  if groupedNamedTailBoundaryProof.hasSorry then
    throwError "named grouped tail FVar boundary has an admission"
  let groupedNamedTailNoMissingTheorem := ``RecursorGroupedTypeTranslationSupport.namedTailNoMissingFVar
  let groupedNamedTailNoMissingInfo ← getConstInfo groupedNamedTailNoMissingTheorem
  if groupedNamedTailNoMissingInfo matches .axiomInfo _ then
    throwError "named grouped tail missing-FVar contradiction is not theorem-backed"
  let some groupedNamedTailNoMissingProof := groupedNamedTailNoMissingInfo.value? (allowOpaque := true) |
    throwError "named grouped tail missing-FVar proof missing"
  if groupedNamedTailNoMissingProof.hasSorry then
    throwError "named grouped tail missing-FVar contradiction has an admission"
  logInfo "integrity supplies index-domain FVar support; grouped source scope and semantic selected-domain support remain explicit model/pass premises"

end InductiveRecursorSelectedDomainBoundaryTest
