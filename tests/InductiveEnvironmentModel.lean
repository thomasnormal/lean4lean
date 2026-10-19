import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.InductiveHeaders
import Lean.Util.CollectAxioms

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

run_meta
  for name in #[``Lean4Lean.VInductDecl.WF, ``Lean4Lean.VEnv.addInduct,
      ``Lean4Lean.VEnv.addInduct_WF, ``Lean4Lean.VEnv.addInduct.le,
      ``Lean4Lean.VEnv.addInduct.headerFresh, ``Lean4Lean.VEnv.addInduct.constructorFresh,
      ``Lean4Lean.VEnv.addInduct.defeqs_eq, ``Lean4Lean.VEnv.addInductWithRecursors_WF] do
    let information ← Lean.getConstInfo name
    if information matches .axiomInfo _ then throwError "abstract signature axiom {name}"
    let some proof := information.value? (allowOpaque := true)
      | throwError "abstract signature proof absent {name}"
    if proof.hasSorry then throwError "abstract signature admission {name}"
    for dependency in (← Lean.collectAxioms name) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "abstract signature registration gained {dependency} in {name}"
  Lean.logInfo "abstract signature registration is constructive; genuine inductive/recursor semantics remain outside this model"

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

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    (∅ : VEnv).constants ``Bool = none := by
  exact VEnv.addInduct.headerFresh boolInductDecl.types[0] hadd
    (by simp [boolInductDecl])

example {env : VEnv} (hadd : VEnv.addInduct ∅ boolInductDecl = some env) :
    (∅ : VEnv).constants ``Bool.false = none := by
  exact VEnv.addInduct.constructorFresh
    ({ uvars := 0, type := .const ``Bool [], name := ``Bool.false }) hadd
    (by simp [VInductDecl.constructorHeaders, boolInductDecl])

private def boolRecursor : VConstVal :=
  { name := ``Bool.rec, uvars := 0, type := .const ``Bool [] }

example : ∃ env, VEnv.addInductWithRecursors (∅ : VEnv) boolInductDecl
    [boolRecursor] = some env := by
  apply VEnv.addInductWithRecursors.exists
  · intro header hmem
    simp [boolInductDecl] at hmem
    subst header
    rfl
  · simp [boolInductDecl]
  · simp [VInductDecl.constructorHeaders, boolInductDecl]
  · intro headerEnv hheader ctor hmem
    simp [VEnv.addInductHeaders, VEnv.addConst, boolInductDecl] at hheader
    have hheader' := Option.some.inj hheader
    rw [← hheader']
    simp [VInductDecl.constructorHeaders, boolInductDecl] at hmem
    rcases hmem with rfl | rfl <;> rfl
  · simp [boolRecursor]
  · intro _ hinduct recursor hmem
    simp [boolRecursor] at hmem
    subst recursor
    rw [VEnv.addInduct.constants_eq hinduct]
    · rfl
    · intro header hheader
      simp [boolInductDecl] at hheader
      subst header
      decide
    · intro ctor hctor
      simp [VInductDecl.constructorHeaders, boolInductDecl] at hctor
      rcases hctor with rfl | rfl <;> decide

example {env : VEnv}
    (hadd : VEnv.addInductWithRecursors (∅ : VEnv) boolInductDecl [boolRecursor] = some env) :
    env.constants ``Bool.rec = some boolRecursor.toVConstant := by
  exact VEnv.addInductWithRecursors.recursor boolRecursor hadd (by simp)

example {env : VEnv}
    (hadd : VEnv.addInductWithRecursors (∅ : VEnv) boolInductDecl [boolRecursor] = some env) :
    (∅ : VEnv).constants ``Bool.rec = none := by
  exact VEnv.addInductWithRecursors.recursorFresh boolRecursor hadd (by simp)

example {env : VEnv}
    (hadd : VEnv.addInductWithRecursors (∅ : VEnv) boolInductDecl [boolRecursor] = some env) :
    env.defeqs = (∅ : VEnv).defeqs := by
  exact VEnv.addInductWithRecursors.defeqs_eq hadd

example {env : VEnv}
    (hadd : VEnv.addInductWithRecursors (∅ : VEnv) boolInductDecl [boolRecursor] = some env) :
    env.Ordered := by
  apply VEnv.addInductWithRecursors_WF .empty
  · refine ⟨boolInductDecl.headersWF, ?_⟩
    intro next haddHeaders ctor hmem
    exact ⟨boolCtorUvars ctor hmem, boolInductDecl.constructorWF haddHeaders ctor hmem⟩
  · intro inductEnv hinduct recursor hmem
    have : recursor = boolRecursor := List.mem_singleton.mp hmem
    subst recursor
    change inductEnv.IsType 0 [] (.const ``Bool [])
    refine ⟨.succ .zero, VEnv.HasType.const (env := inductEnv) (U := 0) (Γ := [])
      (c := ``Bool) (ci := boolInductDecl.types[0].toVConstant) (ls := []) ?_
      (fun _ h => by cases h) rfl⟩
    exact VEnv.addInduct.header boolInductDecl.types[0] hinduct (by simp [boolInductDecl])
  · exact hadd

end Lean4Lean

namespace Lean4Lean

example : ∃ env, VEnv.addInduct (∅ : VEnv) boolInductDecl = some env := by
  apply VEnv.addInduct.exists
  · intro header hmem
    simp [boolInductDecl] at hmem
    subst header
    change none = none
    rfl
  · simp [boolInductDecl]
  · simp [VInductDecl.constructorHeaders, boolInductDecl]
  · intro headerEnv hheader ctor hmem
    simp [VEnv.addInductHeaders, VEnv.addConst, boolInductDecl] at hheader
    have hheader' := Option.some.inj hheader
    rw [← hheader']
    simp [VInductDecl.constructorHeaders, boolInductDecl] at hmem
    rcases hmem with rfl | rfl
    · change none = none
      rfl
    · change none = none
      rfl

end Lean4Lean
