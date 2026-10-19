import Lean4Lean.Theory.Typing.ConcreteReduction
import Lean.Util.CollectAxioms

namespace MutualQuotientReductionTest
open Lean Lean4Lean Lean4Lean.VEnv

def first : VDefVal where
  name := `MutualQuotientFirst
  uvars := 0
  type := .sort (.succ .zero)
  value := .sort .zero

def second : VDefVal where
  name := `MutualQuotientSecond
  uvars := 0
  type := .sort (.succ .zero)
  value := .const first.name []

def definitions := [first, second]
def reserved := (VEnv.empty.addConsts definitions).getD .empty
def extended := reserved.addDefEqs definitions

theorem added : VEnv.empty.addConsts definitions = some reserved := rfl

theorem wellFormed : extended.WF := by
  refine ⟨_, VEnv.WF'.decl (VDecl.WF.mutualDef ?_ added ?_) .empty⟩
  · intro definition member
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨_, .sort trivial⟩
  · intro definition member
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact .sort trivial
    · have found := VEnv.addConsts_constants added first (by simp [definitions])
      simpa [VDefVal.WF, second, first, VExpr.instL, VLevel.inst] using
        (HasType.const found (ls := []) (by simp) rfl (Γ := []) (U := 0))

theorem firstRegistered : extended.defeqs first.toDefEq :=
  (VEnv.addDefEqs_defeqs ..).mpr (.inl ⟨first, by simp [definitions], rfl⟩)

theorem secondRegistered : extended.defeqs second.toDefEq :=
  (VEnv.addDefEqs_defeqs ..).mpr (.inl ⟨second, by simp [definitions], rfl⟩)

example : extended.constants second.name = some second.toVConstant :=
  wellFormed.rewriteMetadata.lookup secondRegistered

example : @ParRed (wellFormed.reductionParams 0) []
    (.const second.name []) (.const first.name []) := by
  letI := wellFormed.reductionParams 0
  have certificate := RewriteRule.equation (universes := 0) (levels := []) (locals := []) wellFormed secondRegistered rfl
  simpa [second, first, VDefVal.toDefEq, VExpr.instL, VLevel.inst, VLevel.params] using certificate.parRed

example : VEnv.empty.addConsts [first, first] = none := rfl

-- This path must work for every checked block, not just the two-constant fixture.
example {environment reserved : VEnv} {definitions : List VDefVal}
    (before : environment.WF)
    (headers : ∀ definition ∈ definitions, definition.toVConstant.WF environment)
    (added : environment.addConsts definitions = some reserved)
    (bodies : ∀ definition ∈ definitions, definition.WF reserved) :
    RewriteMetadata (reserved.addDefEqs definitions) := by
  obtain ⟨history, checked⟩ := before
  exact (show (reserved.addDefEqs definitions).WF from
    ⟨_, checked.decl (.mutualDef headers added bodies)⟩).rewriteMetadata

run_meta
  for name in #[``VEnv.addConsts_defeqs, ``VEnv.addDefEqs_defeqs,
      ``VEnv.addDefEqs_constants, ``VEnv.addDefEqs_extension, ``wellFormed,
      ``firstRegistered, ``secondRegistered] do
    let information ← getConstInfo name
    if information matches .axiomInfo _ then throwError "new mutual axiom {name}"
    if let some proof := information.value? (allowOpaque := true) then
      if proof.hasSorry then throwError "direct mutual admission {name}"
    for dependency in (← collectAxioms name) do
      unless [``propext, ``Quot.sound].contains dependency do
        throwError "mutual history fixture gained {dependency} in {name}"
    logInfo m!"{name}: {repr (← collectAxioms name)}"
  logInfo "mutual definitions retain all signatures, dependent bodies, registered equations, and actual reduction; duplicate names reject; all history witnesses are admission-free"

end MutualQuotientReductionTest
