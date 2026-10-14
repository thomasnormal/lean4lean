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

namespace Lean4Lean

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    (∅ : VEnv) ≤ env :=
  VEnv.addInduct.le hadd

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    env.constants ``Bool = some boolInductDecl.types[0].toVConstant := by
  simpa [boolInductDecl] using VEnv.addInduct.header boolInductDecl.types[0] hadd
    (by simp [boolInductDecl])

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    env.constants ``Bool.false = some { uvars := 0, type := .const ``Bool [] } := by
  simpa [boolInductDecl] using VEnv.addInduct.constructor
    ({ uvars := 0, type := .const ``Bool [], name := ``Bool.false }) hadd
    (by simp [VInductDecl.constructorHeaders, boolInductDecl])

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    env.defeqs = (∅ : VEnv).defeqs :=
  VEnv.addInduct.defeqs_eq hadd

end Lean4Lean
