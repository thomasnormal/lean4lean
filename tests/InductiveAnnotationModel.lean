import Lean4Lean.Verify.InductiveAnnotationModel
import Lean4Lean.Verify.InductiveAnnotationModelScope
import Lean4Lean.Verify.InductiveAnnotationModelRenaming
import Lean4Lean.Verify.InductiveAnnotationNativeScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace InductiveAnnotationModelTest

private def unary (name : Name) (levels : List Level) (carrier : Expr) : Expr :=
  .app (.const name levels) carrier

private def binary (name : Name) (levels : List Level) (carrier extra : Expr) : Expr :=
  .app (.app (.const name levels) carrier) extra

private def tagged : MData := { entries := [(`AnnotationModelTag, .ofNat 13)] }

private theorem outParamShape (levels : List Level) (carrier : Expr) :
    peelTypeAnnotations (unary ``outParam levels carrier) = peelTypeAnnotations carrier :=
  peelTypeAnnotations.outParam levels carrier

private theorem semiOutParamShape (levels : List Level) (carrier : Expr) :
    peelTypeAnnotations (unary ``semiOutParam levels carrier) = peelTypeAnnotations carrier :=
  peelTypeAnnotations.semiOutParam levels carrier

private theorem optParamShape (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (binary ``optParam levels carrier extra) = peelTypeAnnotations carrier :=
  peelTypeAnnotations.optParam levels carrier extra

private theorem autoParamShape (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (binary ``autoParam levels carrier extra) = peelTypeAnnotations carrier :=
  peelTypeAnnotations.autoParam levels carrier extra

private theorem wrongUnaryArityStops (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (.const ``outParam levels) = .const ``outParam levels ∧
    peelTypeAnnotations (.const ``semiOutParam levels) = .const ``semiOutParam levels ∧
    peelTypeAnnotations (binary ``outParam levels carrier extra) = binary ``outParam levels carrier extra ∧
    peelTypeAnnotations (binary ``semiOutParam levels carrier extra) =
      binary ``semiOutParam levels carrier extra := by
  simp [peelTypeAnnotations, binary]

private theorem wrongBinaryArityStops (levels : List Level) (carrier extra last : Expr) :
    peelTypeAnnotations (.const ``optParam levels) = .const ``optParam levels ∧
    peelTypeAnnotations (.const ``autoParam levels) = .const ``autoParam levels ∧
    peelTypeAnnotations (unary ``optParam levels carrier) = unary ``optParam levels carrier ∧
    peelTypeAnnotations (unary ``autoParam levels carrier) = unary ``autoParam levels carrier ∧
    peelTypeAnnotations (.app (binary ``optParam levels carrier extra) last) =
      .app (binary ``optParam levels carrier extra) last ∧
    peelTypeAnnotations (.app (binary ``autoParam levels carrier extra) last) =
      .app (binary ``autoParam levels carrier extra) last := by
  simp [peelTypeAnnotations, unary, binary]

private theorem atomicConstructorsStop (source : FVarId) (metavar : MVarId) (level : Level) :
    peelTypeAnnotations (.bvar 9) = .bvar 9 ∧
    peelTypeAnnotations (.fvar source) = .fvar source ∧
    peelTypeAnnotations (.mvar metavar) = .mvar metavar ∧
    peelTypeAnnotations (.sort level) = .sort level ∧
    peelTypeAnnotations (.const `AnnotationModelOrdinary [level]) = .const `AnnotationModelOrdinary [level] ∧
    peelTypeAnnotations (.lit (.natVal 17)) = .lit (.natVal 17) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ordinaryStructuresStop (name : Name) (data : MData) (bi : BinderInfo)
    (domain body value : Expr) (nondep : Bool) :
    peelTypeAnnotations (.lam name domain body bi) = .lam name domain body bi ∧
    peelTypeAnnotations (.forallE name domain body bi) = .forallE name domain body bi ∧
    peelTypeAnnotations (.letE name domain value body nondep) = .letE name domain value body nondep ∧
    peelTypeAnnotations (.mdata data body) = .mdata data body ∧
    peelTypeAnnotations (.proj name 2 body) = .proj name 2 body := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem ordinaryApplicationStops (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (unary `AnnotationModelOrdinary levels carrier) =
      unary `AnnotationModelOrdinary levels carrier ∧
    peelTypeAnnotations (binary `AnnotationModelOrdinary levels carrier extra) =
      binary `AnnotationModelOrdinary levels carrier extra := by
  simp [peelTypeAnnotations, unary, binary]

private theorem metadataHeadDoesNotPeel (data : MData) (levels : List Level) (carrier extra : Expr) :
    peelTypeAnnotations (.app (.mdata data (.const ``outParam levels)) carrier) =
      .app (.mdata data (.const ``outParam levels)) carrier ∧
    peelTypeAnnotations (.app (.app (.mdata data (.const ``optParam levels)) carrier) extra) =
      .app (.app (.mdata data (.const ``optParam levels)) carrier) extra := by
  exact ⟨rfl, rfl⟩

private theorem carrierChainIgnoresDefaults (levels : List Level) (carrier dropped : FVarId) :
    peelTypeAnnotations
      (unary ``outParam levels
        (binary ``optParam levels
          (unary ``semiOutParam levels
            (binary ``autoParam levels (.fvar carrier) (.fvar dropped)))
          (unary ``outParam levels (.fvar dropped)))) = .fvar carrier := by
  simp [peelTypeAnnotations, unary, binary]

private theorem metadataCarrierStopsChain (data : MData) (levels : List Level) (carrier : Expr) :
    peelTypeAnnotations (unary ``outParam levels (.mdata data (unary ``semiOutParam levels carrier))) =
      .mdata data (unary ``semiOutParam levels carrier) := by
  simp [peelTypeAnnotations, unary]

private theorem discardedDefaultDoesNotRequireOutputSupport (dropped : FVarId) :
    IndexFVarsWithin [] (peelTypeAnnotations (binary ``optParam [] (.const ``Nat []) (.fvar dropped))) ∧
    ¬ IndexFVarsWithin [] (binary ``optParam [] (.const ``Nat []) (.fvar dropped)) := by
  simp [peelTypeAnnotations, binary, IndexFVarsWithin]

private theorem discardedDefaultDoesNotSurvive (dropped : FVarId) :
    dropped ∉
      (peelTypeAnnotations (binary ``autoParam [] (.const ``Nat []) (.fvar dropped))).fvarsList := by
  simp [peelTypeAnnotations, binary, Expr.fvarsList]

private theorem modelSupportOnly (metavar : MVarId) :
    IndexFVarsWithin []
      (peelTypeAnnotations
        (binary ``optParam [] (.app (.const `AnnotationModelUnknown []) (.bvar 5)) (.mvar metavar))) := by
  simp [peelTypeAnnotations, binary, IndexFVarsWithin]

private theorem nativeEvaluationDoesNotYieldKernelEquation : True := by
  fail_if_success
    have reflected : (unary ``outParam [] (.const ``Nat [])).consumeTypeAnnotations = .const ``Nat [] := by
      rfl
  trivial

private theorem modelSupportSubset (value : Expr) :
    (peelTypeAnnotations value).fvarsList ⊆ value.fvarsList := peelTypeAnnotations_fvarsSubset value

private theorem modelPreservesScope {ids : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) : IndexFVarsWithin ids (peelTypeAnnotations value) :=
  within.peelTypeAnnotations

private theorem modelPreservesAvoidance {id : FVarId} {value : Expr}
    (avoids : IndexAvoids id value) : IndexAvoids id (peelTypeAnnotations value) :=
  avoids.peelTypeAnnotations

private theorem modelIdempotent (value : Expr) :
    peelTypeAnnotations (peelTypeAnnotations value) = peelTypeAnnotations value :=
  peelTypeAnnotations_idempotent value

private theorem arbitraryPairsCommute (pairs : List (FVarId × FVarId)) (value : Expr) :
    indexRenameExpr pairs (peelTypeAnnotations value) = peelTypeAnnotations (indexRenameExpr pairs value) :=
  indexRenameExpr_peelTypeAnnotations pairs value

private theorem arbitraryRelatedOutputs {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) :
    IndexLookupRenaming pairs (peelTypeAnnotations left) (peelTypeAnnotations right) :=
  related.peelTypeAnnotations

private theorem identityPairsPeel (source : FVarId) :
    indexRenameExpr [(source, source)]
      (peelTypeAnnotations (binary ``optParam [] (.fvar source) (.lit (.natVal 17)))) = .fvar source := by
  simp [peelTypeAnnotations, binary, indexRenameExpr, indexLookup]

private theorem overlappingPairsDoNotRenameTwice (source target other : FVarId) :
    indexRenameExpr [(source, target), (target, other)]
      (peelTypeAnnotations (unary ``semiOutParam [] (.fvar source))) = .fvar target := by
  simp [peelTypeAnnotations, unary, indexRenameExpr, indexLookup]

private theorem duplicateSourcePairsUseFirstLookup (source target other : FVarId) :
    indexRenameExpr [(source, target), (source, other)]
      (peelTypeAnnotations (binary ``autoParam [] (.fvar source) (.fvar other))) = .fvar target := by
  simp [peelTypeAnnotations, binary, indexRenameExpr, indexLookup]

private theorem nativeScopeRequiresExplicitModel {ids : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) (model : NativeAnnotationModelAt value) :
    IndexFVarsWithin ids value.consumeTypeAnnotations := within.consumeTypeAnnotations_of_model model

private theorem nativeAvoidanceRequiresExplicitModel {id : FVarId} {value : Expr}
    (avoids : IndexAvoids id value) (model : NativeAnnotationModelAt value) :
    IndexAvoids id value.consumeTypeAnnotations := avoids.consumeTypeAnnotations_of_model model

private theorem nativeRenamingRequiresBothModels {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right)
    (leftModel : NativeAnnotationModelAt left) (rightModel : NativeAnnotationModelAt right) :
    IndexLookupRenaming pairs left.consumeTypeAnnotations right.consumeTypeAnnotations :=
  related.consumeTypeAnnotations_of_models leftModel rightModel

private theorem emptyNativeModels : BinderNativeAnnotationModels [] := by
  intro position step selected
  cases selected

private theorem parametersNeedNoNativeModel (domain value : Expr) :
    BinderNativeAnnotationModels
      [{ role := .parameter, name := `parameter, domain, bi := .implicit, value }] := by
  intro position step selected index
  cases position with
  | zero =>
    obtain rfl := Option.some.inj selected
    cases index
  | succ position =>
    simp only [List.getElem?_cons_succ, List.getElem?_nil] at selected
    cases selected

private theorem chronologicalConsumedScopeRequiresFiniteModels {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) (models : BinderNativeAnnotationModels steps) :
    BinderConsumedIndexDomainScope params steps := scope.consumedIndexDomainScope models

private theorem actualDeclaredTypeScopeRequiresModel {ctx : Context} {value rawDomain : Expr}
    {name : Name} {bi : BinderInfo} {ids : List FVarId}
    (declared : BinderDeclaredAt ctx value name rawDomain.consumeTypeAnnotations bi)
    (within : IndexFVarsWithin ids rawDomain) (model : NativeAnnotationModelAt rawDomain) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
      decl.type = rawDomain.consumeTypeAnnotations ∧ decl.userName = name ∧ decl.binderInfo = bi ∧
      IndexFVarsWithin ids decl.type := declared.typeFVarsWithin_of_model within model

private theorem actualNativeTypesRetainBothHistoriesConditionally
    {initialPairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeIndexTypeAt initialPairs checkedCtx generatedCtx checkedStart generatedStart
      checked generated position)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated)
    (checkedModels : BinderNativeAnnotationModels checked) (generatedModels : BinderNativeAnnotationModels generated) :
    ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
      checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
      priorPairs = initialPairs ++ List.zip
        ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
        ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
      checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
      generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
      checkedDecl.type = checkedStep.localDomain ∧ generatedDecl.type = generatedStep.localDomain ∧
      IndexFVarsWithin (params ++ (BinderStep.indexValues (checked.take position)).map Expr.fvarId!) checkedDecl.type ∧
      IndexFVarsWithin (params ++ (BinderStep.indexValues (generated.take position)).map Expr.fvarId!) generatedDecl.type ∧
      IndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type :=
  receipt.typeScopes_of_models checkedScope generatedScope checkedModels generatedModels

private def ordinaryConstructors (source : FVarId) (carrier extra : Expr) : Array Expr := #[
  .bvar 9, .fvar source, .mvar ⟨`AnnotationModelExprMeta⟩, .sort (.succ (.param `u)),
  .const `AnnotationModelOrdinary [.param `u], .lit (.natVal 17),
  .app (.fvar source) carrier,
  .lam `binder carrier extra .implicit, .forallE `binder carrier extra .instImplicit,
  .letE `binder carrier extra (.bvar 0) false, .mdata tagged carrier,
  .proj `AnnotationModelStructure 2 carrier]

private def annotationShapes (levels : List Level) (carrier extra : Expr) : Array Expr := Id.run do
  let mut result := #[]
  for name in [``outParam, ``semiOutParam, ``optParam, ``autoParam] do
    for arity in [:5] do
      result := result.push (mkAppN (.const name levels) (#[carrier, extra, carrier, extra].extract 0 arity))
  result := result ++ #[
    .mdata tagged (unary ``outParam levels carrier),
    .app (.mdata tagged (.const ``outParam levels)) carrier,
    .app (.app (.mdata tagged (.const ``optParam levels)) carrier) extra,
    unary `AnnotationModelOrdinary levels (unary ``outParam levels carrier),
    .app (.lam `head carrier extra .default) (unary ``semiOutParam levels carrier)]
  return result

private def annotationChain (levels : List Level) (carrier extra : Expr) (count : Nat) : Expr :=
  (List.range count).foldl (fun previous position =>
    match position % 4 with
    | 0 => unary ``outParam levels previous
    | 1 => binary ``optParam levels previous extra
    | 2 => unary ``semiOutParam levels previous
    | _ => binary ``autoParam levels previous extra) carrier

private def pairFixtures (source target other : FVarId) : List (List (FVarId × FVarId)) := [
  [], [(source, source)], [(source, target)], [(source, target), (target, other)],
  [(source, target), (source, other)], [(source, target), (target, source)],
  [(source, target), (target, other), (other, source)], [(source, target), (other, target)]]

private def compareNativeAndModel (pairs : List (List (FVarId × FVarId))) (value : Expr) : MetaM Unit := do
  let modeled := peelTypeAnnotations value
  unless value.consumeTypeAnnotations == modeled do
    throwError "native annotation consumption disagrees with the total model on a tested expression"
  unless modeled.fvarsList.all value.fvarsList.contains do
    throwError "modeled annotation consumption introduced a free variable"
  for incoming in pairs do
    let renamedRaw := indexRenameExpr incoming value
    let renamedModel := indexRenameExpr incoming modeled
    unless peelTypeAnnotations renamedRaw == renamedModel do
      throwError "modeled annotation consumption failed arbitrary deterministic renaming"
    unless renamedRaw.consumeTypeAnnotations == renamedModel do
      throwError "native annotation consumption disagrees empirically after tested renaming"
    unless indexRenameExpr incoming value.consumeTypeAnnotations == renamedRaw.consumeTypeAnnotations do
      throwError "tested native annotation consumption failed empirical renaming comparison"

private def checkNativeOpacity : MetaM Unit := do
  let env ← Lean.getEnv
  let some (.opaqueInfo _) := env.find? ``Expr.consumeTypeAnnotations
    | throwError "native annotation consumption no longer has the expected partial opaque declaration"
  for suffix in ["eq_def", "eq_1", "_eq_1"] do
    unless (env.find? (Name.str ``Expr.consumeTypeAnnotations suffix)).isNone do
      throwError "native annotation consumption unexpectedly has a kernel equation theorem"
  unless (unary ``outParam [] (.const ``Nat [])).consumeTypeAnnotations == (.const ``Nat [] : Expr) do
    throwError "native opacity control no longer evaluates to the model output empirically"
  logInfo "native partial annotation consumer remains opaque/no eq_def; evaluated comparisons are controls, not kernel proofs"

private def modelMatrix : MetaM Unit := do
  let source : FVarId := ⟨`AnnotationModelSource⟩
  let target : FVarId := ⟨`AnnotationModelTarget⟩
  let other : FVarId := ⟨`AnnotationModelOther⟩
  let pairs := pairFixtures source target other
  let levels : List (List Level) := [[], [.zero], [.succ .zero], [.param `u],
    [.max (.param `u) (.succ .zero)], [.mvar ⟨`AnnotationModelLevelMeta⟩]]
  let carriers : List Expr := [.const ``Nat [], .fvar source, .fvar target, .bvar 8,
    .mvar ⟨`AnnotationModelExprMeta⟩, .sort (.param `u),
    .app (.fvar source) (.fvar target), .mdata tagged (unary ``outParam [] (.fvar source))]
  let extras : List Expr := [.fvar other, .lit (.natVal 17), .bvar 11,
    binary ``autoParam [] (.fvar other) (.mvar ⟨`AnnotationModelDiscardedMeta⟩)]
  let mut compared := 0
  for carrier in carriers do
    for value in ordinaryConstructors source carrier (.fvar other) do
      unless peelTypeAnnotations value == value do
        throwError "ordinary expression constructor unexpectedly peeled a nested annotation"
      compareNativeAndModel pairs value
      compared := compared + 1
    for universeArgs in levels do
      for extra in extras do
        for value in annotationShapes universeArgs carrier extra do
          compareNativeAndModel pairs value
          compared := compared + 1
      for count in [0, 1, 2, 3, 4, 7, 16, 31, 64, 127, 256] do
        let chain := annotationChain universeArgs carrier (.fvar other) count
        unless peelTypeAnnotations chain == peelTypeAnnotations carrier do
          throwError "annotation chain followed a discarded default instead of the carrier"
        compareNativeAndModel pairs chain
        compared := compared + 1
  logInfo m!"{compared} empirical native/model cases and {compared * pairs.length} arbitrary renamed comparisons: all constructors, exact/wrong arities, levels, metadata, discarded-FVar defaults, chains through length 256, identity/overlap/duplicate pairs"

private def audit (theoremName : Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``outParamShape
  audit ``semiOutParamShape
  audit ``optParamShape
  audit ``autoParamShape
  audit ``wrongUnaryArityStops
  audit ``wrongBinaryArityStops
  audit ``atomicConstructorsStop
  audit ``ordinaryStructuresStop
  audit ``ordinaryApplicationStops
  audit ``metadataHeadDoesNotPeel
  audit ``carrierChainIgnoresDefaults
  audit ``metadataCarrierStopsChain
  audit ``discardedDefaultDoesNotRequireOutputSupport
  audit ``discardedDefaultDoesNotSurvive
  audit ``modelSupportOnly
  audit ``nativeEvaluationDoesNotYieldKernelEquation
  audit ``modelSupportSubset
  audit ``modelPreservesScope
  audit ``modelPreservesAvoidance
  audit ``modelIdempotent
  audit ``arbitraryPairsCommute
  audit ``arbitraryRelatedOutputs
  audit ``identityPairsPeel
  audit ``overlappingPairsDoNotRenameTwice
  audit ``duplicateSourcePairsUseFirstLookup
  audit ``nativeScopeRequiresExplicitModel
  audit ``nativeAvoidanceRequiresExplicitModel
  audit ``nativeRenamingRequiresBothModels
  audit ``emptyNativeModels
  audit ``parametersNeedNoNativeModel
  audit ``chronologicalConsumedScopeRequiresFiniteModels
  audit ``actualDeclaredTypeScopeRequiresModel
  audit ``actualNativeTypesRetainBothHistoriesConditionally
  audit ``peelTypeAnnotations
  audit ``peelTypeAnnotations.outParam
  audit ``peelTypeAnnotations.semiOutParam
  audit ``peelTypeAnnotations.optParam
  audit ``peelTypeAnnotations.autoParam
  audit ``peelTypeAnnotations.unaryOther
  audit ``peelTypeAnnotations.binaryOther
  audit ``peelTypeAnnotations.forallE
  audit ``peelTypeAnnotations.lam
  audit ``peelTypeAnnotations.letE
  audit ``peelTypeAnnotations.mdata
  audit ``peelTypeAnnotations.proj
  audit ``peelTypeAnnotations_fvarsSubset
  audit ``peelTypeAnnotations_idempotent
  audit ``IndexFVarsWithin.peelTypeAnnotations
  audit ``IndexAvoids.peelTypeAnnotations
  audit ``indexRenameExpr_isAppOfArity
  audit ``indexRenameExpr_peelTypeAnnotations
  audit ``IndexLookupRenaming.peelTypeAnnotations
  audit ``NativeAnnotationModelAt
  audit ``BinderNativeAnnotationModels
  audit ``BinderConsumedIndexDomainScope
  audit ``IndexFVarsWithin.consumeTypeAnnotations_of_model
  audit ``IndexAvoids.consumeTypeAnnotations_of_model
  audit ``IndexLookupRenaming.consumeTypeAnnotations_of_models
  audit ``BinderRawDomainScope.consumedIndexDomainScope
  audit ``BinderDeclaredAt.typeFVarsWithin_of_model
  audit ``NativeIndexTypeAt.typeScopes_of_models
  checkNativeOpacity
  modelMatrix

end InductiveAnnotationModelTest
