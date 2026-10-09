import Lean4Lean.Verify.InductiveBinderLookupCorrespondence
import Lean4Lean.Verify.InductiveAnnotationModelRenaming

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def ConsumedIndexLookupRenaming (pairs : List (FVarId × FVarId)) (left right : Expr) : Prop :=
  ∃ rawLeft rawRight, IndexLookupRenaming pairs rawLeft rawRight ∧
    peelTypeAnnotations rawLeft = left ∧ peelTypeAnnotations rawRight = right

theorem ConsumedIndexLookupRenaming.ofRaw {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) :
    ConsumedIndexLookupRenaming pairs (peelTypeAnnotations left) (peelTypeAnnotations right) :=
  ⟨left, right, related, rfl, rfl⟩

theorem ConsumedIndexLookupRenaming.toIndexLookupRenaming {pairs : List (FVarId × FVarId)}
    {left right : Expr} (related : ConsumedIndexLookupRenaming pairs left right) :
    IndexLookupRenaming pairs left right := by
  obtain ⟨rawLeft, rawRight, hraw, hleft, hright⟩ := related
  rw [← hleft, ← hright]
  exact hraw.peelTypeAnnotations

theorem ConsumedIndexLookupRenaming.toConsumedIndexRenaming {pairs : List (FVarId × FVarId)}
    {left right : Expr} (related : ConsumedIndexLookupRenaming pairs left right) :
    ConsumedIndexRenaming pairs left right := by
  obtain ⟨rawLeft, rawRight, hraw, hleft, hright⟩ := related
  exact ⟨rawLeft, rawRight, hraw.related, hleft, hright⟩

theorem BinderDeclaredAt.lookupRenamingTypes {pairs : List (FVarId × FVarId)}
    {checkedRoot current : Context} {checkedValue generatedValue checkedDomain generatedDomain : Expr}
    {name : Name} {bi : BinderInfo}
    (checkedDeclared : BinderDeclaredAt checkedRoot checkedValue name (peelTypeAnnotations checkedDomain) bi)
    (generatedDeclared : BinderDeclaredAt current generatedValue name (peelTypeAnnotations generatedDomain) bi)
    (hdomains : IndexLookupRenaming pairs checkedDomain generatedDomain) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedValue.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedValue.fvarId! = some generatedDecl ∧
      ConsumedIndexLookupRenaming pairs checkedDecl.type generatedDecl.type := by
  obtain ⟨checkedDecl, hcheckedLookup, _, hcheckedType, _, _⟩ := checkedDeclared
  obtain ⟨generatedDecl, hgeneratedLookup, _, hgeneratedType, _, _⟩ := generatedDeclared
  refine ⟨checkedDecl, generatedDecl, hcheckedLookup, hgeneratedLookup, ?_⟩
  rw [hcheckedType, hgeneratedType]
  exact ConsumedIndexLookupRenaming.ofRaw hdomains

theorem BinderLookupCorrespondence.indexHeadTypes
    {pairs finalPairs : List (FVarId × FVarId)} {checkedFirst generatedFirst : BinderStep}
    {checkedTail generatedTail : List BinderStep} {checkedRoot current : Context}
    (correspondence : BinderLookupCorrespondence pairs
      (checkedFirst :: checkedTail) (generatedFirst :: generatedTail) finalPairs)
    (hindex : checkedFirst.role = .index)
    (checkedDeclared : BinderStepsIndexDeclared checkedRoot (checkedFirst :: checkedTail))
    (generatedDeclared : BinderStepsIndexDeclared current (generatedFirst :: generatedTail)) :
    ∃ checkedDecl generatedDecl,
      checkedRoot.lctx.find? checkedFirst.value.fvarId! = some checkedDecl ∧
      current.lctx.find? generatedFirst.value.fvarId! = some generatedDecl ∧
      ConsumedIndexLookupRenaming pairs checkedDecl.type generatedDecl.type := by
  cases correspondence with
  | parameter name bi checkedDomain generatedDomain value rawDomain tail => cases hindex
  | index name bi checkedDomain generatedDomain checkedId generatedId rawDomain tail =>
    exact (checkedDeclared _ (by simp) rfl).lookupRenamingTypes
      (generatedDeclared _ (by simp) rfl) rawDomain

end Lean4Lean.AddInductive
