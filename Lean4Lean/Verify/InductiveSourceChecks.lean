import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.InductiveParamReconstruction

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open ElimNestedInductive

def InductiveSourcesNoMVarNoFVar (types : List InductiveType) : Prop :=
  ∀ indType ∈ types, indType.type.FVarsIn (fun _ => False) ∧
    ∀ ctor ∈ indType.ctors, ctor.type.FVarsIn (fun _ => False)

private theorem checkConstructorSources_WF (env : Environment) (ctors : List Constructor) :
    (ctors.forM fun ctor => env.checkNoMVarNoFVar ctor.name ctor.type).WF fun _ =>
      ∀ ctor ∈ ctors, ctor.type.FVarsIn (fun _ => False) := by
  simp only [List.forM_eq_forM]
  induction ctors with
  | nil => exact .pure (by simp)
  | cons ctor ctors ih =>
    rw [List.forM_cons]
    refine (checkNoMVarNoFVar.WF env ctor.name ctor.type).bind fun _ hctor => ?_
    exact ih.mono fun _ hctors other hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hctor
      · exact hctors other hmem

theorem Environment.checkInductiveSources.WF (env : Environment) (types : List InductiveType) :
    (Environment.checkInductiveSources env types).WF fun _ =>
      InductiveSourcesNoMVarNoFVar types := by
  unfold Environment.checkInductiveSources
  simp only [List.forM_eq_forM]
  induction types with
  | nil => exact .pure (by simp [InductiveSourcesNoMVarNoFVar])
  | cons indType types ih =>
    rw [List.forM_cons]
    refine ((checkNoMVarNoFVar.WF env indType.name indType.type).bind fun _ htype =>
      (checkConstructorSources_WF env indType.ctors).mono fun _ hctors => And.intro htype hctors).bind
        fun _ htype => ?_
    exact ih.mono fun _ htypes other hmem => by
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact htype
      · exact htypes other hmem

private theorem checkNoSourceVars_pure (env : Environment) (name : Name) (type : Expr)
    (hfvars : type.FVarsIn (fun _ => False)) :
    env.checkNoMVarNoFVar name type = .ok () := by
  have hnil : type.fvarsList = [] := List.eq_nil_iff_forall_not_mem.mpr fun fvar hmem =>
    (fvarsIn_iff.mp hfvars).1 fvar hmem
  have hfree := fvarsList_eq_nil.mp hnil
  have hmeta := fvarsIn_iff_hasMVar.mp (hfvars.mono fun _ hfalse => hfalse.elim)
  simp [Kernel.Environment.checkNoMVarNoFVar, Kernel.Environment.checkNoMVar,
    Kernel.Environment.checkNoFVar, hfree, hmeta]
  rfl

private theorem checkConstructorSources_pure (env : Environment) (ctors : List Constructor)
    (hfvars : ∀ ctor ∈ ctors, ctor.type.FVarsIn (fun _ => False)) :
    (ctors.forM fun ctor => env.checkNoMVarNoFVar ctor.name ctor.type) = .ok () := by
  simp only [List.forM_eq_forM]
  revert hfvars
  induction ctors with
  | nil => intro _; rfl
  | cons ctor ctors ih =>
    intro hfvars
    rw [List.forM_cons, checkNoSourceVars_pure env ctor.name ctor.type (hfvars ctor (by simp)),
      show Except.ok () >>= _ = _ from rfl]
    exact ih fun other hmem => hfvars other (List.mem_cons_of_mem ctor hmem)

theorem Environment.checkInductiveSources.eq_pure (env : Environment)
    (types : List InductiveType) (hsources : InductiveSourcesNoMVarNoFVar types) :
    Environment.checkInductiveSources env types = .ok () := by
  unfold Environment.checkInductiveSources
  simp only [List.forM_eq_forM]
  revert hsources
  induction types with
  | nil => intro _; rfl
  | cons indType types ih =>
    intro hsources
    have htype := hsources indType (List.mem_cons_self ..)
    have hctors : (forM indType.ctors fun ctor => env.checkNoMVarNoFVar ctor.name ctor.type) =
        Except.ok () := by
      simpa only [List.forM_eq_forM] using checkConstructorSources_pure env indType.ctors htype.2
    rw [List.forM_cons, checkNoSourceVars_pure env indType.name indType.type htype.1,
      hctors]
    change (forM types fun indType => do
      env.checkNoMVarNoFVar indType.name indType.type
      forM indType.ctors fun ctor => env.checkNoMVarNoFVar ctor.name ctor.type) = Except.ok ()
    exact ih fun other hmem => hsources other (List.mem_cons_of_mem indType hmem)

theorem SourceReserved.of_fvarsIn_false {type : Expr}
    (hfvars : type.FVarsIn (fun _ => False)) (ngen : NameGenerator) : SourceReserved type ngen :=
  fun fvar hmem => False.elim ((fvarsIn_iff.mp hfvars).1 fvar hmem)

theorem InductiveSourcesNoMVarNoFVar.headerReserved {types : List InductiveType}
    (hsources : InductiveSourcesNoMVarNoFVar types) (indType : InductiveType)
    (hmem : indType ∈ types) (ngen : NameGenerator) : SourceReserved indType.type ngen :=
  SourceReserved.of_fvarsIn_false (hsources indType hmem).1 ngen

theorem InductiveSourcesNoMVarNoFVar.constructorReserved {types : List InductiveType}
    (hsources : InductiveSourcesNoMVarNoFVar types) (indType : InductiveType)
    (hmem : indType ∈ types) (ctor : Constructor) (hctor : ctor ∈ indType.ctors)
    (ngen : NameGenerator) : SourceReserved ctor.type ngen :=
  SourceReserved.of_fvarsIn_false ((hsources indType hmem).2 ctor hctor) ngen

theorem Environment.addInductive.sources (env : Environment) (lparams : List Name)
    (numParams : Nat) (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) :
    (Environment.addInductive env lparams numParams types isUnsafe allowPrimitive fuel).WF fun _ =>
      InductiveSourcesNoMVarNoFVar types := by
  unfold Environment.addInductive
  exact (Environment.checkInductiveSources.WF env types).bind fun _ hsources _ _ => hsources

theorem addDecl.inductiveSources (env : Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (isUnsafe check : Bool) (fuel : FuelConfig) :
    (addDecl env (.inductDecl lparams numParams types isUnsafe) check fuel).WF fun _ =>
      InductiveSourcesNoMVarNoFVar types := by
  unfold addDecl
  have hprimitive : (Environment.checkPrimitiveInductive env lparams numParams types isUnsafe).WF
      fun _ => True := fun _ _ => trivial
  exact hprimitive.bind fun allowPrimitive _ =>
    Environment.addInductive.sources env lparams numParams types isUnsafe allowPrimitive fuel

theorem Environment.addInductive.constructorReserved (env : Environment)
    (lparams : List Name) (numParams : Nat) (types : List InductiveType)
    (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    (Environment.addInductive env lparams numParams types isUnsafe allowPrimitive fuel).WF fun _ =>
      ∀ indType ∈ types, ∀ ctor ∈ indType.ctors, ∀ ngen, SourceReserved ctor.type ngen :=
  (Environment.addInductive.sources env lparams numParams types isUnsafe allowPrimitive fuel).mono
    fun _ hsources indType hmem ctor hctor ngen =>
      hsources.constructorReserved indType hmem ctor hctor ngen

end Lean4Lean
