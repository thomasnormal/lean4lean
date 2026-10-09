import Lean4Lean.Verify.InductiveAnnotationStoredTypes
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveTotalAnnotationConsumerTest

private def unary (name : Name) (carrier : Expr) : Expr := .app (.const name [.succ .zero]) carrier

private def binary (name : Name) (carrier extra : Expr) : Expr :=
  .app (.app (.const name [.succ .zero]) carrier) extra

private def tagged : MData := { entries := [(`TotalAnnotationConsumerTag, .ofNat 29)] }

private def sortType : Expr := .sort (.succ .zero)

private theorem executableLocalDomainIsTotal (step : BinderStep) :
    step.localDomain = peelTypeAnnotations step.domain := rfl

private theorem discardedDefaultHasNoStoredFVar (dropped : FVarId) :
    (peelTypeAnnotations (binary ``optParam (.const ``Nat []) (.fvar dropped))).fvarsList = [] := by
  simp [peelTypeAnnotations, binary, Expr.fvarsList]

private theorem actualDiscardedDefaultHasEmptySupport {ctx : Context} {value : Expr}
    {name : Name} {bi : BinderInfo} (dropped : FVarId)
    (declared : BinderDeclaredAt ctx value name
      (peelTypeAnnotations (binary ``optParam (.const ``Nat []) (.fvar dropped))) bi) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.type.fvarsList = [] := by
  obtain ⟨decl, lookup, _, type, _, _⟩ := declared
  refine ⟨decl, lookup, ?_⟩
  rw [type]
  exact discardedDefaultHasNoStoredFVar dropped

private theorem declaredStoredTypeScopeWithoutNativePremise {ctx : Context} {value domain : Expr}
    {name : Name} {bi : BinderInfo} {ids : List FVarId}
    (declared : BinderDeclaredAt ctx value name (peelTypeAnnotations domain) bi)
    (within : IndexFVarsWithin ids domain) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
      decl.type = peelTypeAnnotations domain ∧ IndexFVarsWithin ids decl.type := by
  obtain ⟨decl, lookup, expression, type, _, _⟩ := declared
  refine ⟨decl, lookup, expression, type, ?_⟩
  rw [type]
  exact within.peelTypeAnnotations

private theorem declaredStoredTypeDeterminismWithoutNativePremise
    {pairs : List (FVarId × FVarId)} {checkedCtx generatedCtx : Context}
    {checkedValue generatedValue checkedRaw generatedRaw : Expr} {name : Name} {bi : BinderInfo}
    (checked : BinderDeclaredAt checkedCtx checkedValue name (peelTypeAnnotations checkedRaw) bi)
    (generated : BinderDeclaredAt generatedCtx generatedValue name (peelTypeAnnotations generatedRaw) bi)
    (related : IndexLookupRenaming pairs checkedRaw generatedRaw) :
    ∃ checkedDecl generatedDecl,
      checkedCtx.lctx.find? checkedValue.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedValue.fvarId! = some generatedDecl ∧
      checkedDecl.type = peelTypeAnnotations checkedRaw ∧ generatedDecl.type = peelTypeAnnotations generatedRaw ∧
      IndexLookupRenaming pairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedDecl, checkedLookup, _, checkedType, _, _⟩ := checked
  obtain ⟨generatedDecl, generatedLookup, _, generatedType, _, _⟩ := generated
  refine ⟨checkedDecl, generatedDecl, checkedLookup, generatedLookup, checkedType, generatedType, ?_⟩
  rw [checkedType, generatedType]
  exact related.peelTypeAnnotations

private theorem actualStoredIndexScopesWithoutNativePremise
    {initialPairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeIndexTypeAt initialPairs checkedCtx generatedCtx checkedStart generatedStart
      checked generated position)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated) :
    ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
      checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
      checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
      checkedDecl.type = peelTypeAnnotations checkedStep.domain ∧
      generatedDecl.type = peelTypeAnnotations generatedStep.domain ∧
      IndexFVarsWithin (params ++ (BinderStep.indexValues (checked.take position)).map Expr.fvarId!) checkedDecl.type ∧
      IndexFVarsWithin (params ++ (BinderStep.indexValues (generated.take position)).map Expr.fvarId!) generatedDecl.type ∧
      IndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, checkedLookupStep, generatedLookupStep,
    _, _, _, _, checkedLookup, generatedLookup, _, _, checkedType, generatedType, _, _, _, _, _, _, related, _⟩ := receipt
  refine ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, checkedLookupStep, generatedLookupStep,
    checkedLookup, generatedLookup, checkedType, generatedType, ?_, ?_, ?_⟩
  · rw [checkedType]
    exact (checkedScope position checkedStep checkedLookupStep).peelTypeAnnotations
  · rw [generatedType]
    exact (generatedScope position generatedStep generatedLookupStep).peelTypeAnnotations
  · rw [checkedType, generatedType]
    exact related.peelTypeAnnotations

private theorem arbitraryDeterministicConsumedRenaming (pairs : List (FVarId × FVarId)) (raw : Expr) :
    IndexLookupRenaming pairs (peelTypeAnnotations raw) (peelTypeAnnotations (indexRenameExpr pairs raw)) :=
  (show IndexLookupRenaming pairs raw (indexRenameExpr pairs raw) from rfl).peelTypeAnnotations

private theorem chronologicalStoredScopesAreUnconditional {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) : BinderStoredIndexDomainScope params steps :=
  scope.storedIndexDomainScope

private theorem storedCurrentAndFutureExclusionAreUnconditional {steps : List BinderStep}
    (exclusion : BinderRawIndexExclusion steps) : BinderStoredIndexExclusion steps :=
  exclusion.storedIndexExclusion

private theorem fullNativeStoredTypeReceiptIsUnconditional
    {initialPairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeIndexTypeAt initialPairs checkedCtx generatedCtx checkedStart generatedStart
      checked generated position)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated) :
    NativeStoredIndexTypeAt initialPairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated position := receipt.storedTypeScopes checkedScope generatedScope

private theorem sameParentHistoriesHaveUnconditionalStoredTypes {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (receipt : ParentBinderScopedLookupTypes stats types parent checkedRoot current info) :
    ∃ normalized checked generated checkedTerminal generatedTerminal checkedStart generatedStart pairs,
      NormalizedSortTelescope types[parent]!.type normalized ∧
      OpenedTelescope normalized checked checkedTerminal ∧
      OpenedTelescope normalized generated generatedTerminal ∧
      BinderIndexAllocations checkedRoot checkedStart checked ∧
      BinderIndexAllocations current generatedStart generated ∧
      pairs = List.zip ((BinderStep.indexValues checked).map Expr.fvarId!)
        (info.indices.toList.map Expr.fvarId!) ∧
      BinderLookupNativeTypes [] checkedRoot current checkedStart generatedStart checked generated ∧
      BinderLookupStoredTypeScopes [] (stats.params.toList.map Expr.fvarId!)
        checkedRoot current checkedStart generatedStart checked generated ∧
      BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) checked ∧
      BinderStoredIndexDomainScope (stats.params.toList.map Expr.fvarId!) generated ∧
      BinderStoredIndexExclusion checked ∧ BinderStoredIndexExclusion generated := receipt.storedTypeHistories

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let generatorRoot ← readThe Context
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          generatorRoot.lparams false false
        return (stats, checked, generatorRoot, result)

private def checkValueType (ctx : Context) (value raw : Expr) : MetaM Unit := do
  let some declaration := ctx.lctx.find? value.fvarId!
    | throwError "total-annotation consumer actual local declaration missing"
  unless declaration.toExpr == value && declaration.type == peelTypeAnnotations raw do
    throwError "total-annotation consumer actual declaration is not stored with the total consumer result"
  unless declaration.type.fvarsList.all raw.fvarsList.contains do
    throwError "total-annotation consumer stored declaration gained an unsupported FVar"
  unless raw.consumeTypeAnnotations == declaration.type do
    throwError "total-annotation consumer empirical native comparison differs on a tested raw domain"

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def annotatedHeader : Expr :=
  .forallE `carrier (.app (.const ``outParam [.succ (.succ .zero)]) sortType)
    (.forallE `element (unary ``semiOutParam (.bvar 0)) sortType .default) .implicit

private def headerRegistrations (ctx : Context) : MetaM Unit := do
  let carrierDomain := Expr.app (.const ``outParam [.succ (.succ .zero)]) sortType
  for nparams in [0, 1, 2] do
    let types := #[header (Name.mkNum `TotalAnnotationHeader nparams) annotatedHeader]
    let .ok (stats, checked, generatorRoot, _, infos, generated) := stage nparams types ctx
      | throwError "total-annotation consumer annotated header registration failed"
    let rawDomains := #[carrierDomain, unary ``semiOutParam (stats.params[0]?.getD infos[0]!.indices[0]!)]
    for position in [:nparams] do
      checkValueType checked stats.params[position]! rawDomains[position]!
    for offset in [:2 - nparams] do
      let some declaration := checked.lctx.getAt? (ctx.lctx.numIndices + nparams + offset)
        | throwError "total-annotation consumer checked annotated index missing"
      let raw := if nparams + offset = 0 then carrierDomain else unary ``semiOutParam
        ((checked.lctx.getAt? ctx.lctx.numIndices).get!).toExpr
      checkValueType checked declaration.toExpr raw
      let generatedRaw := if offset = 0 && nparams = 0 then carrierDomain else unary ``semiOutParam
        (stats.params[0]?.getD infos[0]!.indices[0]!)
      checkValueType generated infos[0]!.indices[offset]! generatedRaw
    let .ok (_, _) := mkRecInfos stats types (.succ .zero)
        (fun infos => do return (infos, ← readThe Context)) generatorRoot
      | throwError "total-annotation consumer focused recursor helper failed"
  logInfo "three full annotated-header registrations split parameters/indices 0,1,2 and retain actual total-consumed local types"

private def recursionTypes : Array InductiveType := Id.run do
  let name := `TotalAnnotationRecursive
  let result := Expr.const name []
  let recursiveFunction := Expr.forallE `child (unary ``semiOutParam (.const ``Nat [])) result .default
  let leaf := Expr.forallE `leafArg (binary ``optParam (.const ``Nat []) (.lit (.natVal 7))) result .default
  let branch := Expr.forallE `count (unary ``outParam (.const ``Nat []))
    (.forallE `children recursiveFunction result .default) .default
  let automatic := Expr.forallE `automaticArg
    (binary ``autoParam (.const ``Nat []) (.const ``Lean.Syntax.missing [])) result .default
  return #[{ name, type := sortType, ctors := [
    { name := name ++ `leaf, type := leaf }, { name := name ++ `branch, type := branch },
    { name := name ++ `automatic, type := automatic }] }]

private def recursiveRegistration (ctx : Context) : MetaM Unit := do
  let .ok (_, _, _, env, infos, generated) := stage 0 recursionTypes ctx
    | throwError "total-annotation consumer positivity/recursive constructor registration failed"
  unless infos.size == 1 && infos[0]!.minors.size == 3 do
    throwError "total-annotation consumer recursor minor count changed"
  let mut annotatedFields := 0
  for declaration in generated.lctx.decls.toList.filterMap id do
    if [ `leafArg, `count, `automaticArg, `child ].contains declaration.userName then
      unless declaration.type == (.const ``Nat [] : Expr) do
        throwError "total-annotation consumer recursive/helper local retained its outer annotation"
      annotatedFields := annotatedFields + 1
  unless annotatedFields == 3 do
    throwError "total-annotation consumer recursive fixture failed to retain all three annotated constructor fields"
  let some (.recInfo recursor) := env.find? (mkRecName `TotalAnnotationRecursive)
    | throwError "total-annotation consumer recursive recursor declaration missing"
  unless recursor.rules.length == 3 do
    throwError "total-annotation consumer recursive recursor rule count changed"
  logInfo "one full recursive registration exercises annotated constructor fields, positivity/function binders, recursive-argument readers, recursor indices/major/motive/minors, and recursive hypothesis generation"

private def uncheckedDiscardedDefaults (ctx : Context) : MetaM Unit := do
  let dropped : FVarId := ⟨`TotalAnnotationDiscarded⟩
  for name in [``optParam, ``autoParam] do
    let raw := binary name (.const ``Nat []) (.fvar dropped)
    let type := Expr.forallE `field raw sortType .default
    let stats : InductiveStats := { lctx := ctx.lctx, levels := [], resultLevel := .succ .zero, indConsts := #[], params := #[], nindices := #[], isNotZero := true }
    let .ok (values, current) := mkRecInfos.loopArgs1 stats type 0 #[] ctx.fuel.inductiveFuel
        (fun values => do return (values, ← readThe Context)) ctx
      | throwError "total-annotation consumer unchecked discarded-FVar default fixture failed"
    unless values.size == 1 do
      throwError "total-annotation consumer unchecked index helper count changed"
    checkValueType current values[0]! raw
    let some declaration := current.lctx.find? values[0]!.fvarId!
      | throwError "total-annotation consumer unchecked index helper declaration missing"
    unless declaration.type == (.const ``Nat [] : Expr) && declaration.type.fvarsList.isEmpty do
      throwError "total-annotation consumer retained a discarded default FVar in its actual local type"
  logInfo "two actual unchecked index-helper allocations discard unsupported default FVars without native-equation premises"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``executableLocalDomainIsTotal
  audit ``discardedDefaultHasNoStoredFVar
  audit ``actualDiscardedDefaultHasEmptySupport
  audit ``declaredStoredTypeScopeWithoutNativePremise
  audit ``declaredStoredTypeDeterminismWithoutNativePremise
  audit ``actualStoredIndexScopesWithoutNativePremise
  audit ``arbitraryDeterministicConsumedRenaming
  audit ``chronologicalStoredScopesAreUnconditional
  audit ``storedCurrentAndFutureExclusionAreUnconditional
  audit ``fullNativeStoredTypeReceiptIsUnconditional
  audit ``sameParentHistoriesHaveUnconditionalStoredTypes
  audit ``BinderStoredIndexDomainScope
  audit ``BinderStoredIndexExclusion
  audit ``NativeStoredIndexTypeAt
  audit ``BinderLookupStoredTypeScopes
  audit ``BinderRawDomainScope.storedIndexDomainScope
  audit ``BinderRawIndexExclusion.storedIndexExclusion
  audit ``BinderDeclaredAt.typeFVarsWithin
  audit ``NativeIndexTypeAt.storedTypeScopes
  audit ``BinderLookupNativeTypes.storedTypeScopes
  audit ``ParentBinderScopedLookupTypes.storedTypeHistories
  audit ``peelTypeAnnotations
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  headerRegistrations ctx
  recursiveRegistration ctx
  uncheckedDiscardedDefaults ctx

end InductiveTotalAnnotationConsumerTest
