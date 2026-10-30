import Lean4Lean.Verify.InductiveFrontendScope
namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open ElimNestedInductive
def canonicalBoolType : InductiveType := {
  name := ``Bool, type := .sort (.succ .zero),
  ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩] }
private theorem noConstRaw (lctx : LocalContext) (env : Kernel.Environment) (state : State) (name : Name) :
    Expr.replaceNoCacheT (replaceIfNested lctx #[] #[]) (.const name []) env state =
      Except.ok ((.const name []), state) := by
  unfold Expr.replaceNoCacheT
  rfl
private theorem noConst (lctx : LocalContext) (env : Kernel.Environment) (state : State) (name : Name) :
    replaceAllNested lctx #[] #[] (.const name []) env state =
      Except.ok ((.const name []), state) := by
  unfold replaceAllNested Expr.replaceM
  exact noConstRaw lctx env state name
private theorem noForall (lctx : LocalContext) (env : Kernel.Environment) (state : State)
    (name : Name) (bi : BinderInfo) :
    replaceAllNested lctx #[] #[] (.forallE name (.const ``Nat []) (.const ``Nat []) bi) env state =
      Except.ok ((.forallE name (.const ``Nat []) (.const ``Nat []) bi), state) := by
  unfold replaceAllNested Expr.replaceM Expr.replaceNoCacheT
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  rw [show replaceIfNested lctx #[] #[] (.forallE name (.const ``Nat []) (.const ``Nat []) bi) env state =
      Except.ok (none, state) from rfl]
  simp only [Except.bind, Option.rec, Except.pure, pure_bind]
  simp [(· >>= ·), ReaderT.bind, StateT.bind, Except.bind]
  rw [noConstRaw lctx env state ``Nat]
  simp only
  rw [noConstRaw lctx env state ``Nat]
  rfl
private theorem get_bind {α} (next : State → M α) (env : Kernel.Environment) (state : State) :
    ((get >>= next) env state) = next state env state := rfl
private theorem withParams_zero (type : Expr)
    (next : LocalContext → Expr → Array Expr → M α) :
    withParams type 0 next = next {} type #[] := rfl
private theorem modify_bind (update : State → State) (next : PUnit → M α)
    (env : Kernel.Environment) (state : State) :
    ((modify update >>= next) env state) = next () env (update state) := rfl
private def step (ctor : Constructor) : M Constructor :=
  withParams ctor.type 0 fun lctx remainder sourceParams => do
    let rewritten ← replaceAllNested lctx #[] sourceParams remainder
    return { ctor with type := lctx.mkForall sourceParams rewritten }
private theorem constCtorStep (name : Name) (env : Kernel.Environment) (state : State)
    (inductiveName : Name) :
    (step ⟨name, .const inductiveName []⟩ env state).WF
      (fun result => result.2 = state) := by
  unfold step
  rw [withParams_zero]
  dsimp only
  have hreplace : (replaceAllNested {} #[] #[] (.const inductiveName []) env state).WF
      (fun result => result.2 = state) := by
    rw [noConst]
    exact .pure rfl
  refine hreplace.bind ?_
  intro result hresult
  dsimp only
  exact .pure hresult
private theorem map_steps (ctors : List Constructor) (env : Kernel.Environment) (state : State)
    (hctors : ∀ ctor ∈ ctors, ∃ name, ctor = ⟨name, .const ``Bool []⟩) :
    (ctors.mapM step env state).WF
      (fun result => result.2 = state) := by
  induction ctors generalizing state with
  | nil => exact .pure rfl
  | cons ctor ctors ih =>
    rw [List.mapM_cons]
    obtain ⟨name, hname⟩ := hctors ctor (by simp)
    rw [hname]
    refine (constCtorStep name env state ``Bool).bind ?_
    rintro ⟨ctor', state'⟩ h
    dsimp only at h ⊢
    have hstate : state' = state := h
    subst state'
    refine (ih state (fun c hc => hctors c (by simp [hc]))).bind ?_
    rintro ⟨rest, final⟩ hfinal
    dsimp only at hfinal ⊢
    exact .pure hfinal
private theorem tail (fuel : Nat) (env : Kernel.Environment) (state : State)
    (hsize : state.newTypes.size = 1) (haux : state.nestedAux = #[]) :
    (run.loop 0 {} #[] 1 fuel env state).WF
      (fun result => result.1.aux2nested.size = 0) := by
  cases fuel with
  | zero => exact .throw
  | succ fuel =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · rename_i hindex
      have hnot : ¬ 1 < state.newTypes.size := by simpa [hsize]
      exact False.elim (hnot hindex)
    · rename_i hnot
      apply Except.WF.pure
      dsimp only
      rw [haux]
      rfl
private theorem loop_bool (fuel : Nat) (env : Kernel.Environment) (ngen : NameGenerator)
    (lvls : List Level) (nextIdx : Nat) :
    (run.loop 0 {} #[] 0 (fuel + 1) env
      { ngen, nestedAux := #[], lvls, newTypes := #[canonicalBoolType], nextIdx }).WF
      (fun result => result.1.aux2nested.size = 0) := by
  cases fuel with
  | zero =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      have hm := map_steps canonicalBoolType.ctors env
        { ngen, nestedAux := #[], lvls, newTypes := #[canonicalBoolType], nextIdx }
        (by intro ctor hmem; simp [canonicalBoolType] at hmem; rcases hmem with rfl | rfl <;> exact ⟨_, rfl⟩)
      refine hm.bind ?_
      rintro ⟨ctors, state'⟩ hstate
      dsimp only at hstate ⊢
      cases hstate
      rw [modify_bind]
      exact .throw
    · rename_i hnot
      exact False.elim (hnot (by simp))
  | succ fuel =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      have hm := map_steps canonicalBoolType.ctors env
        { ngen, nestedAux := #[], lvls, newTypes := #[canonicalBoolType], nextIdx }
        (by intro ctor hmem; simp [canonicalBoolType] at hmem; rcases hmem with rfl | rfl <;> exact ⟨_, rfl⟩)
      refine hm.bind ?_
      rintro ⟨ctors, state'⟩ hstate
      dsimp only at hstate ⊢
      cases hstate
      rw [modify_bind]
      apply tail (fuel + 1) env _ (by simp) (by simp)
    · rename_i hnot
      exact False.elim (hnot (by simp))
private theorem loop_bool_any (fuel : Nat) (env : Kernel.Environment) (ngen : NameGenerator)
    (lvls : List Level) (nextIdx : Nat) :
    (run.loop 0 {} #[] 0 fuel env
      { ngen, nestedAux := #[], lvls, newTypes := #[canonicalBoolType], nextIdx }).WF
      (fun result => result.1.aux2nested.size = 0) := by
  cases fuel with
  | zero => exact .throw
  | succ fuel => simpa only [Nat.succ_eq_add_one] using loop_bool fuel env ngen lvls nextIdx
theorem canonicalBoolPreprocess (env : Kernel.Environment) (fuel : FuelConfig) :
    (inductivePreprocessing env [] 0 [canonicalBoolType] fuel).WF
      (fun result => result.aux2nested.size = 0) := by
  unfold inductivePreprocessing
  unfold ElimNestedInductive.run
  change ((withParams canonicalBoolType.type 0 (fun lctx remainder params =>
    run.loop 0 lctx params 0 fuel.inductiveFuel) env).run'
      { lvls := [], newTypes := #[canonicalBoolType] }).WF _
  rw [withParams_zero]
  exact (loop_bool_any fuel.inductiveFuel env _ [] 1).map fun _ h => h
theorem canonicalBoolNonNested (env : Kernel.Environment) (fuel : FuelConfig) :
    NonNestedInductivePreprocessing env [] 0 [canonicalBoolType] fuel := by
  intro preprocessing hpre
  exact canonicalBoolPreprocess env fuel preprocessing hpre
def canonicalNatType (binderName : Name) (binderInfo : BinderInfo) : InductiveType := {
  name := ``Nat, type := .sort (.succ .zero),
  ctors := [⟨``Nat.zero, .const ``Nat []⟩,
    ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩] }
private theorem forallCtorStep (name binder : Name) (bi : BinderInfo) (env : Kernel.Environment) (state : State) :
    (step ⟨name, .forallE binder (.const ``Nat []) (.const ``Nat []) bi⟩ env state).WF
      (fun result => result.2 = state) := by
  unfold step
  rw [withParams_zero]
  dsimp only
  have hreplace : (replaceAllNested {} #[] #[]
      (.forallE binder (.const ``Nat []) (.const ``Nat []) bi) env state).WF
      (fun result => result.2 = state) := by
    rw [noForall]
    exact .pure rfl
  refine hreplace.bind ?_
  intro result hresult
  dsimp only
  exact .pure hresult
private theorem nat_map_steps (binderName : Name) (binderInfo : BinderInfo)
    (env : Kernel.Environment) (state : State) :
    ((canonicalNatType binderName binderInfo).ctors.mapM step env state).WF
      (fun result => result.2 = state) := by
  unfold canonicalNatType
  rw [List.mapM_cons]
  refine (constCtorStep ``Nat.zero env state ``Nat).bind ?_
  rintro ⟨ctor', state'⟩ h
  dsimp only at h ⊢
  have hstate : state' = state := h
  subst state'
  have htail : (([⟨``Nat.succ, .forallE binderName (.const ``Nat [])
      (.const ``Nat []) binderInfo⟩] : List Constructor).mapM step env state).WF
      (fun result => result.2 = state) := by
    rw [List.mapM_cons]
    simp only [List.mapM_nil, pure_bind]
    refine (forallCtorStep ``Nat.succ binderName binderInfo env state).bind ?_
    rintro ⟨ctor'', state''⟩ h
    dsimp only at h ⊢
    exact .pure h
  refine htail.bind ?_
  rintro ⟨rest, final⟩ hfinal
  dsimp only at hfinal ⊢
  exact .pure hfinal
private theorem loop_nat (fuel : Nat) (env : Kernel.Environment) (ngen : NameGenerator)
    (lvls : List Level) (nextIdx : Nat) (binderName : Name) (binderInfo : BinderInfo) :
    (run.loop 0 {} #[] 0 (fuel + 1) env
      { ngen, nestedAux := #[], lvls, newTypes := #[canonicalNatType binderName binderInfo], nextIdx }).WF
      (fun result => result.1.aux2nested.size = 0) := by
  cases fuel with
  | zero =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      have hm := nat_map_steps binderName binderInfo env
        { ngen, nestedAux := #[], lvls, newTypes := #[canonicalNatType binderName binderInfo], nextIdx }
      refine hm.bind ?_
      rintro ⟨ctors, state'⟩ hstate
      dsimp only at hstate ⊢
      cases hstate
      rw [modify_bind]
      exact .throw
    · rename_i hnot
      exact False.elim (hnot (by simp))
  | succ fuel =>
    rw [run.loop.eq_def]
    dsimp only
    rw [get_bind]
    split
    · rename_i hindex
      simp only [withParams.assert_size]
      have hm := nat_map_steps binderName binderInfo env
        { ngen, nestedAux := #[], lvls, newTypes := #[canonicalNatType binderName binderInfo], nextIdx }
      refine hm.bind ?_
      rintro ⟨ctors, state'⟩ hstate
      dsimp only at hstate ⊢
      cases hstate
      rw [modify_bind]
      apply tail (fuel + 1) env _ (by simp) (by simp)
    · rename_i hnot
      exact False.elim (hnot (by simp))
private theorem loop_nat_any (fuel : Nat) (env : Kernel.Environment) (ngen : NameGenerator)
    (lvls : List Level) (nextIdx : Nat) (binderName : Name) (binderInfo : BinderInfo) :
    (run.loop 0 {} #[] 0 fuel env
      { ngen, nestedAux := #[], lvls, newTypes := #[canonicalNatType binderName binderInfo], nextIdx }).WF
      (fun result => result.1.aux2nested.size = 0) := by
  cases fuel with
  | zero => exact .throw
  | succ fuel =>
    have h := loop_nat fuel env ngen lvls nextIdx binderName binderInfo
    simpa only [Nat.succ_eq_add_one] using h
theorem canonicalNatPreprocess (env : Kernel.Environment) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) :
    (inductivePreprocessing env [] 0 [canonicalNatType binderName binderInfo] fuel).WF
      (fun result => result.aux2nested.size = 0) := by
  unfold inductivePreprocessing
  unfold ElimNestedInductive.run
  change ((withParams (canonicalNatType binderName binderInfo).type 0 (fun lctx remainder params =>
    run.loop 0 lctx params 0 fuel.inductiveFuel) env).run'
      { lvls := [], newTypes := #[canonicalNatType binderName binderInfo] }).WF _
  rw [withParams_zero]
  exact (loop_nat_any fuel.inductiveFuel env _ [] 1 binderName binderInfo).map fun _ h => h
theorem canonicalNatNonNested (env : Kernel.Environment) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) :
    NonNestedInductivePreprocessing env [] 0 [canonicalNatType binderName binderInfo] fuel := by
  intro preprocessing hpre
  exact canonicalNatPreprocess env fuel binderName binderInfo preprocessing hpre

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem addDecl.safeCanonicalBool (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl [] 0 [canonicalBoolType] false) check fuel).WF fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope env [] 0 [canonicalBoolType] allowPrimitive fuel result :=
  addDecl.safeNonNestedInductive env [] 0 [canonicalBoolType] check fuel hmap
    (canonicalBoolNonNested env fuel)

theorem addDecl.safeCanonicalNat (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) (hmap : env.constants.WF) :
    (addDecl env (.inductDecl [] 0 [canonicalNatType binderName binderInfo] false) check fuel).WF fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope env [] 0 [canonicalNatType binderName binderInfo] allowPrimitive fuel result :=
  addDecl.safeNonNestedInductive env [] 0 [canonicalNatType binderName binderInfo] check fuel hmap
    (canonicalNatNonNested env fuel binderName binderInfo)

end Lean4Lean
