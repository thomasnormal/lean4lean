import Lean4Lean.Verify.InductiveIndexBaseInsertion

namespace Lean4Lean
open Lean hiding Environment Exception

structure RetainedFVarPrefix (env : VEnv) (universes : List Name)
    (source target : VLCtx) (lift : Lift) (identifiers : List FVarId) : Prop where
  sourceRetained : identifiers ⊆ source.fvars
  targetRetained : identifiers ⊆ target.fvars
  lookups : ∀ (position : Nat) (identifier : FVarId), identifiers[position]? = some identifier →
    ∃ semantic type,
      source.find? (.inr identifier) = some (semantic, type) ∧
      TrExprS env universes source (.fvar identifier) semantic ∧
      env.HasType universes.length source.toCtx semantic type ∧
      target.find? (.inr identifier) = some (semantic.lift' lift, type.lift' lift) ∧
      TrExprS env universes target (.fvar identifier) (semantic.lift' lift) ∧
      env.HasType universes.length target.toCtx (semantic.lift' lift) (type.lift' lift)

theorem VLCtx.FVLift'.retainedPrefix
    {env : VEnv} {universes : List Name} {source target : VLCtx}
    {lift : Lift} {identifiers : List FVarId}
    (weakening : VLCtx.FVLift' source target 0 lift 0)
    (envWF : env.WF) (sourceWF : source.WF env universes.length)
    (targetWF : target.WF env universes.length) (retained : identifiers ⊆ source.fvars) :
    RetainedFVarPrefix env universes source target lift identifiers := by
  refine ⟨retained, fun _ member => weakening.fvars_sublist.subset (retained member), ?_⟩
  intro position identifier selected
  have member : identifier ∈ identifiers := List.mem_of_getElem? selected
  obtain ⟨⟨semantic, type⟩, sourceLookup⟩ := VLCtx.find?_eq_some.mpr (retained member)
  have targetLookup := weakening.find? targetWF sourceLookup
  exact ⟨semantic, type, sourceLookup, .fvar sourceLookup,
    sourceWF.find?_wf envWF.ordered sourceLookup, targetLookup, .fvar targetLookup,
    targetWF.find?_wf envWF.ordered targetLookup⟩

end Lean4Lean
