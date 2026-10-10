import Lean4Lean.Verify.InductiveParameterPrefixTransport

namespace Lean4Lean
open Lean hiding Environment Exception

structure RetainedFVarPrefixAgreement (env : VEnv) (universes : List Name)
    (source original aligned : VLCtx) (lift : Lift) (identifiers : List FVarId) : Prop where
  transported : RetainedFVarPrefix env universes source aligned lift identifiers
  originalRetained : identifiers ⊆ original.fvars
  lookups : ∀ (position : Nat) (identifier : FVarId), identifiers[position]? = some identifier →
    ∃ semantic type originalSemantic originalType level,
      source.find? (.inr identifier) = some (semantic, type) ∧
      TrExprS env universes source (.fvar identifier) semantic ∧
      env.HasType universes.length source.toCtx semantic type ∧
      original.find? (.inr identifier) = some (originalSemantic, originalType) ∧
      TrExprS env universes original (.fvar identifier) originalSemantic ∧
      env.HasType universes.length original.toCtx originalSemantic originalType ∧
      env.IsDefEq universes.length original.toCtx originalType (type.lift' lift) (.sort level) ∧
      env.IsDefEq universes.length original.toCtx
        originalSemantic (semantic.lift' lift) originalType

theorem RetainedFVarPrefix.agreesWithOriginal
    {env : VEnv} {universes : List Name} {source original aligned : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (receipt : RetainedFVarPrefix env universes source aligned lift identifiers)
    (envWF : env.WF) (contexts : VLCtx.IsDefEq env universes.length original aligned) :
    RetainedFVarPrefixAgreement env universes source original aligned lift identifiers := by
  have originalRetained : identifiers ⊆ original.fvars := by
    simpa only [contexts.fvars] using receipt.targetRetained
  refine ⟨receipt, originalRetained, ?_⟩
  intro position identifier selected
  obtain ⟨semantic, type, sourceLookup, sourceTranslation, sourceType, alignedLookup,
    _, _⟩ := receipt.lookups position identifier selected
  have member : identifier ∈ identifiers := List.mem_of_getElem? selected
  obtain ⟨⟨originalSemantic, originalType⟩, originalLookup⟩ :=
    VLCtx.find?_eq_some.mpr (originalRetained member)
  have originalTyped := contexts.wf.find?_wf envWF.ordered originalLookup
  obtain ⟨level, originalTypeTyped⟩ :=
    originalTyped.isType envWF.ordered contexts.wf.toCtx
  obtain ⟨typeEqualityU, valueEquality⟩ :=
    contexts.find?_uniq envWF originalLookup alignedLookup
  have typeEquality := typeEqualityU.of_l envWF contexts.wf.toCtx originalTypeTyped
  exact ⟨semantic, type, originalSemantic, originalType, level, sourceLookup, sourceTranslation,
    sourceType, originalLookup, .fvar originalLookup, originalTyped, typeEquality, valueEquality⟩

end Lean4Lean
