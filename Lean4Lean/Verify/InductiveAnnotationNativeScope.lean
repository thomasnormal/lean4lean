import Lean4Lean.Verify.InductiveAnnotationModelScope
import Lean4Lean.Verify.InductiveAnnotationModelRenaming
import Lean4Lean.Verify.InductiveBinderRawScopeAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def NativeAnnotationModelAt (value : Expr) : Prop :=
  value.consumeTypeAnnotations = peelTypeAnnotations value

def BinderNativeAnnotationModels (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep),
    steps[position]? = some step → step.role = .index → NativeAnnotationModelAt step.domain

def BinderConsumedIndexDomainScope (params : List FVarId) (steps : List BinderStep) : Prop :=
  ∀ (position : Nat) (step : BinderStep), steps[position]? = some step → step.role = .index →
    IndexFVarsWithin (params ++ (BinderStep.indexValues (steps.take position)).map Expr.fvarId!) step.localDomain

theorem IndexFVarsWithin.consumeTypeAnnotations_of_model {ids : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) (model : NativeAnnotationModelAt value) :
    IndexFVarsWithin ids value.consumeTypeAnnotations := by
  rw [model]
  exact within.peelTypeAnnotations

theorem IndexAvoids.consumeTypeAnnotations_of_model {source : FVarId} {value : Expr}
    (avoids : IndexAvoids source value) (model : NativeAnnotationModelAt value) :
    IndexAvoids source value.consumeTypeAnnotations := by
  rw [model]
  exact avoids.peelTypeAnnotations

theorem IndexLookupRenaming.consumeTypeAnnotations_of_models
    {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right)
    (leftModel : NativeAnnotationModelAt left) (rightModel : NativeAnnotationModelAt right) :
    IndexLookupRenaming pairs left.consumeTypeAnnotations right.consumeTypeAnnotations := by
  change indexRenameExpr pairs left.consumeTypeAnnotations = right.consumeTypeAnnotations
  rw [leftModel, rightModel]
  exact related.peelTypeAnnotations

theorem BinderRawDomainScope.consumedIndexDomainScope {params : List FVarId} {steps : List BinderStep}
    (scope : BinderRawDomainScope params steps) (models : BinderNativeAnnotationModels steps) :
    BinderConsumedIndexDomainScope params steps := by
  intro position step hstep hindex
  exact (scope position step hstep).consumeTypeAnnotations_of_model (models position step hstep hindex)

theorem BinderDeclaredAt.typeFVarsWithin_of_model {ctx : Context} {value rawDomain : Expr}
    {name : Name} {bi : BinderInfo} {ids : List FVarId}
    (declared : BinderDeclaredAt ctx value name rawDomain.consumeTypeAnnotations bi)
    (within : IndexFVarsWithin ids rawDomain) (model : NativeAnnotationModelAt rawDomain) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
      decl.type = rawDomain.consumeTypeAnnotations ∧ decl.userName = name ∧ decl.binderInfo = bi ∧
      IndexFVarsWithin ids decl.type := by
  obtain ⟨decl, hlookup, hexpr, htype, hname, hbi⟩ := declared
  refine ⟨decl, hlookup, hexpr, htype, hname, hbi, ?_⟩
  rw [htype]
  exact within.consumeTypeAnnotations_of_model model

theorem NativeIndexTypeAt.typeScopes_of_models
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
      IndexLookupRenaming priorPairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    hcheckedIndex, hgeneratedIndex, _, hprior, hcheckedLookup, hgeneratedLookup, _, _, hcheckedType,
    hgeneratedType, _, _, _, _, _, _, hdomains, _⟩ := receipt
  have hcheckedModel := checkedModels position checkedStep hchecked hcheckedIndex
  have hgeneratedModel := generatedModels position generatedStep hgenerated hgeneratedIndex
  refine ⟨checkedStep, generatedStep, checkedDecl, generatedDecl, priorPairs, hchecked, hgenerated,
    hprior, hcheckedLookup, hgeneratedLookup, hcheckedType, hgeneratedType, ?_, ?_, ?_⟩
  · rw [hcheckedType]
    exact (checkedScope position checkedStep hchecked).consumeTypeAnnotations_of_model hcheckedModel
  · rw [hgeneratedType]
    exact (generatedScope position generatedStep hgenerated).consumeTypeAnnotations_of_model hgeneratedModel
  · rw [hcheckedType, hgeneratedType]
    exact hdomains.consumeTypeAnnotations_of_models hcheckedModel hgeneratedModel

end Lean4Lean.AddInductive
