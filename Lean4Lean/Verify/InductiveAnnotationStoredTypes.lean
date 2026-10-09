import Lean4Lean.Verify.InductiveAnnotationModelScope
import Lean4Lean.Verify.InductiveAnnotationModelRenaming
import Lean4Lean.Verify.InductiveBinderRawScopeAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def BinderStoredIndexDomainScope (params : List FVarId) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    IndexFVarsWithin (params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!) step.localDomain

def BinderStoredIndexExclusion (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (domainStep : BinderStep) (futurePosition : Nat) (futureStep : BinderStep),
    steps[position]? = some domainStep → steps[futurePosition]? = some futureStep →
    futureStep.role = .index → position ≤ futurePosition →
    IndexAvoids futureStep.value.fvarId! domainStep.localDomain

def NativeStoredIndexTypeAt (initialPairs : List (FVarId × FVarId)) (params : List FVarId)
    (checkedCtx generatedCtx : Context) (checkedStart generatedStart : Nat)
    (checked generated : List BinderStep) (position : Nat) : Prop :=
  ∃ checkedStep generatedStep checkedDecl generatedDecl priorPairs,
    checked[position]? = some checkedStep ∧ generated[position]? = some generatedStep ∧
    checkedStep.role = .index ∧ generatedStep.role = .index ∧
    checkedStep.signature = generatedStep.signature ∧
    priorPairs = initialPairs ++ List.zip
      ((BinderStep.indexValues (checked.take position)).map Expr.fvarId!)
      ((BinderStep.indexValues (generated.take position)).map Expr.fvarId!) ∧
    checkedCtx.lctx.find? checkedStep.value.fvarId! = some checkedDecl ∧
    generatedCtx.lctx.find? generatedStep.value.fvarId! = some generatedDecl ∧
    checkedDecl.toExpr = checkedStep.value ∧ generatedDecl.toExpr = generatedStep.value ∧
    checkedDecl.type = checkedStep.localDomain ∧ generatedDecl.type = generatedStep.localDomain ∧
    checkedDecl.userName = checkedStep.name ∧ generatedDecl.userName = generatedStep.name ∧
    checkedDecl.binderInfo = checkedStep.bi ∧ generatedDecl.binderInfo = generatedStep.bi ∧
    checkedDecl.index = checkedStart + (BinderStep.indexValues (checked.take position)).length ∧
    generatedDecl.index = generatedStart + (BinderStep.indexValues (generated.take position)).length ∧
    IndexLookupRenaming priorPairs checkedStep.domain generatedStep.domain ∧
    ConsumedIndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type ∧
    IndexFVarsWithin (params ++ (BinderStep.indexValues (checked.take position)).map Expr.fvarId!) checkedDecl.type ∧
    IndexFVarsWithin (params ++ (BinderStep.indexValues (generated.take position)).map Expr.fvarId!) generatedDecl.type ∧
    IndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type

def BinderLookupStoredTypeScopes (initialPairs : List (FVarId × FVarId)) (params : List FVarId)
    (checkedCtx generatedCtx : Context) (checkedStart generatedStart : Nat)
    (checked generated : List BinderStep) : Prop :=
  ∀ position checkedStep, checked[position]? = some checkedStep → checkedStep.role = .index →
    NativeStoredIndexTypeAt initialPairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated position

theorem BinderRawDomainScope.storedIndexDomainScope {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) : BinderStoredIndexDomainScope params steps :=
  fun position step hstep _ => (scope position step hstep).peelTypeAnnotations

theorem BinderRawIndexExclusion.storedIndexExclusion {steps : List BinderStep}
    (exclusion : BinderRawIndexExclusion steps) : BinderStoredIndexExclusion steps :=
  fun position step futurePosition futureStep hstep hfuture hindex hle =>
    (exclusion position step futurePosition futureStep hstep hfuture hindex hle).peelTypeAnnotations

theorem BinderDeclaredAt.typeFVarsWithin {ctx : Context} {value rawDomain : Expr}
    {name : Name} {bi : BinderInfo} {ids : List FVarId}
    (declared : BinderDeclaredAt ctx value name (peelTypeAnnotations rawDomain) bi)
    (within : IndexFVarsWithin ids rawDomain) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
      decl.type = peelTypeAnnotations rawDomain ∧ decl.userName = name ∧ decl.binderInfo = bi ∧
      IndexFVarsWithin ids decl.type := by
  obtain ⟨decl, hlookup, hexpr, htype, hname, hbi⟩ := declared
  refine ⟨decl, hlookup, hexpr, htype, hname, hbi, ?_⟩
  rw [htype]
  exact within.peelTypeAnnotations

theorem NativeIndexTypeAt.storedTypeScopes
    {initialPairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart position : Nat}
    {checked generated : List BinderStep}
    (receipt : NativeIndexTypeAt initialPairs checkedCtx generatedCtx checkedStart generatedStart
      checked generated position)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated) :
    NativeStoredIndexTypeAt initialPairs params checkedCtx generatedCtx checkedStart generatedStart
      checked generated position := by
  obtain ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    hcheckedIndex, hgeneratedIndex, hsignature, hprior, hcheckedLookup, hgeneratedLookup,
    hcheckedExpr, hgeneratedExpr, hcheckedType, hgeneratedType, hcheckedName, hgeneratedName,
    hcheckedBi, hgeneratedBi, hcheckedPosition, hgeneratedPosition, hdomains, hconsumed⟩ := receipt
  refine ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    hcheckedIndex, hgeneratedIndex, hsignature, hprior, hcheckedLookup, hgeneratedLookup,
    hcheckedExpr, hgeneratedExpr, hcheckedType, hgeneratedType, hcheckedName, hgeneratedName,
    hcheckedBi, hgeneratedBi, hcheckedPosition, hgeneratedPosition, hdomains, hconsumed, ?_, ?_, ?_⟩
  · rw [hcheckedType]
    exact (checkedScope position checkedStep hchecked).peelTypeAnnotations
  · rw [hgeneratedType]
    exact (generatedScope position generatedStep hgenerated).peelTypeAnnotations
  · rw [hcheckedType, hgeneratedType]
    exact hdomains.peelTypeAnnotations

theorem BinderLookupNativeTypes.storedTypeScopes
    {initialPairs : List (FVarId × FVarId)} {params : List FVarId}
    {checkedCtx generatedCtx : Context} {checkedStart generatedStart : Nat}
    {checked generated : List BinderStep}
    (receipt : BinderLookupNativeTypes initialPairs checkedCtx generatedCtx checkedStart generatedStart checked generated)
    (checkedScope : BinderRawDomainScope params checked) (generatedScope : BinderRawDomainScope params generated) :
    BinderLookupStoredTypeScopes initialPairs params checkedCtx generatedCtx checkedStart generatedStart checked generated :=
  fun position step hstep hindex =>
    (receipt position step hstep hindex).storedTypeScopes checkedScope generatedScope

theorem ParentBinderScopedLookupTypes.storedTypeHistories {stats : InductiveStats}
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
      BinderStoredIndexExclusion checked ∧ BinderStoredIndexExclusion generated := by
  obtain ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, _, _, _, _, _, _, _, _, _, _, _, _,
    hcheckedAlloc, hgeneratedAlloc, _, hpairs, _, _, _, _, _, hnative, hcheckedScope, hgeneratedScope,
    hcheckedExclusion, hgeneratedExclusion⟩ := receipt
  exact ⟨normalized, checked, generated, checkedTerminal, generatedTerminal, checkedStart,
    generatedStart, pairs, hnormalized, hchecked, hgenerated, hcheckedAlloc, hgeneratedAlloc, hpairs,
    hnative, hnative.storedTypeScopes hcheckedScope hgeneratedScope,
    hcheckedScope.storedIndexDomainScope, hgeneratedScope.storedIndexDomainScope,
    hcheckedExclusion.storedIndexExclusion, hgeneratedExclusion.storedIndexExclusion⟩

end Lean4Lean.AddInductive
