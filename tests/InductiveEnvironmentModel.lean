import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.InductiveHeaders

namespace Lean4Lean

private theorem boolCtorUvars (ctor : VConstVal)
    (hmem : ctor ∈ boolInductDecl.constructorHeaders) : ctor.uvars = boolInductDecl.uvars := by
  change ctor ∈ ([
    { name := ``Bool.false, uvars := 0, type := .const ``Bool [] },
    { name := ``Bool.true, uvars := 0, type := .const ``Bool [] }
  ] : List VConstVal) at hmem
  simp at hmem
  rcases hmem with rfl | rfl <;> rfl

example : VInductDecl.WF (∅ : VEnv) boolInductDecl := by
  refine ⟨boolInductDecl.headersWF, ?_⟩
  intro env hadd ctor hmem
  exact ⟨boolCtorUvars ctor hmem, boolInductDecl.constructorWF hadd ctor hmem⟩

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) : env.Ordered := by
  exact VEnv.addInduct_WF .empty (by
    refine ⟨boolInductDecl.headersWF, ?_⟩
    intro next haddHeaders ctor hmem
    exact ⟨boolCtorUvars ctor hmem, boolInductDecl.constructorWF haddHeaders ctor hmem⟩) hadd

end Lean4Lean
