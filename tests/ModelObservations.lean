import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Obs
import Lean.Util.CollectAxioms

namespace ModelObservationsTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open scoped Lean4Lean.VEnv.Model

def oneF : List Nat → Nat := fun _ => 1
def one : VLevel := .succ .zero
def D : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort one)
def c : VExpr → Prop := ElCls VEnv.empty 0 [] D (.sort .zero)
def tag : Ob := .sort zeroF

def a : Ob := .app D c [] tag
def b : Ob := .app D c [tag] tag
def d : Ob := .app D c [tag, tag] tag

theorem emptyCoverage : Covers [tag] [] := nofun

theorem innerAB : a ≼ b := .app' emptyCoverage .refl

theorem innerBD : b ≼ d := by
  apply Ob.Le.app' (ho := .refl)
  intro k hk
  have : k = tag := List.mem_singleton.1 hk
  subst k
  exact ⟨tag, .head _, .refl⟩

theorem badDirection (h : b ≼ a) : False := by
  have cover := (Ob.Le.app_iff.1 h).1
  obtain ⟨_, impossible, _⟩ := cover tag (.head _)
  cases impossible

def keysX : List Ob := [b, b, tag]
def keysY : List Ob := [a, tag, b]
def keysZ : List Ob := [a, tag, a, tag]

theorem coverYX : Covers keysY keysX := by
  intro k hk
  rcases hk with _ | ⟨_, hk⟩
  · exact ⟨a, .head _, innerAB⟩
  rcases hk with _ | ⟨_, hk⟩
  · exact ⟨a, .head _, innerAB⟩
  cases hk with
  | head => exact ⟨tag, .tail _ (.head _), .refl⟩
  | tail _ h => cases h

theorem coverZY : Covers keysZ keysY := by
  intro k hk
  rcases hk with _ | ⟨_, hk⟩
  · exact ⟨a, .head _, .refl⟩
  rcases hk with _ | ⟨_, hk⟩
  · exact ⟨tag, .tail _ (.head _), .refl⟩
  cases hk with
  | head => exact ⟨a, .head _, innerAB⟩
  | tail _ h => cases h

theorem finiteIndices :
    ∃ f : Fin keysX.length → Fin keysZ.length,
      ∀ i, keysZ[f i] ≼ keysX[i] :=
  Covers.indices (coverZY.trans coverYX)

theorem nestedComposition :
    Ob.piCodOb c keysX a ≼ Ob.piCodOb c keysZ d :=
  (Ob.Le.piCodOb_of_covers coverYX innerAB).trans
    (Ob.Le.piCodOb_of_covers coverZY innerBD)

theorem nestedSyntax : Ob.piCodOb c keysX a ≠ Ob.piCodOb c keysZ d := by
  intro h
  have e := congrArg List.length (Ob.piCodOb.inj h).2.1
  change 3 = 4 at e
  cases e

-- The typing filter has an actual typed class, not a postulated class certificate.
theorem cTyped : TypedElCls VEnv.empty 0 [] D c :=
  .of_hasType (HasType.sort (by trivial))

def typeObs : List Ob :=
  [.piDom D, .piDomOb (.sort oneF), .piCod c D, .piCodOb c [tag] (.sort oneF)]
def strongerTypes : List Ob :=
  [.piCodOb c [] (.sort oneF), .piCod c D, .piDomOb (.sort oneF), .piDom D]

theorem typeCoverage : Covers strongerTypes typeObs := by
  intro x hx
  rcases hx with _ | ⟨_, hx⟩
  · exact ⟨.piDom D, .tail _ (.tail _ (.tail _ (.head _))), .refl⟩
  rcases hx with _ | ⟨_, hx⟩
  · exact ⟨.piDomOb (.sort oneF), .tail _ (.tail _ (.head _)), .refl⟩
  rcases hx with _ | ⟨_, hx⟩
  · exact ⟨.piCod c D, .tail _ (.head _), .refl⟩
  cases hx with
  | head => exact ⟨_, .head _, .piCodOb_of_covers emptyCoverage .refl⟩
  | tail _ h => cases h

theorem applicationTyped : TypedOb VEnv.empty 0 [] c
    (.app D c [tag] tag) typeObs := by
  refine .app (τd := [.sort oneF]) (τc := [.sort oneF])
    (.head _) ?_ ?_ ?_ cTyped (.tail _ (.tail _ (.head _))) ?_ (.sort (.head _))
  · intro x hx
    cases List.mem_singleton.1 hx
    exact .tail _ (.head _)
  · intro k hk
    cases List.mem_singleton.1 hk
    exact .sort (.head _)
  · intro o ho w hw
    cases List.mem_singleton.1 ho
    cases hw
  · intro x hx
    cases List.mem_singleton.1 hx
    exact ⟨[tag], .tail _ (.tail _ (.tail _ (.head _))), .refl⟩

theorem applicationStrengthened : TypedOb VEnv.empty 0 [] c
    (.app D c [tag] tag) strongerTypes :=
  applicationTyped.strengthen typeCoverage

-- There is a real observation of a proposition, but none of its inhabitants.
theorem propositionObserved : TypedOb VEnv.empty 0 [] c (.piDom D) [.sort zeroF] :=
  .piDom (.head _)

theorem proofObservationsEmpty (h : TypedOb VEnv.empty 0 [] c o [.piDom D]) : False :=
  h.not_prop fun x hx => by
    cases List.mem_singleton.1 hx
    exact ⟨c, propositionObserved⟩

-- Pure field annotations exercise hereditary backing without asserting expression projections.
def field : Ob := .fieldOb (Name.mkSimple "S") 1 [[tag]]
  (.fieldOb (Name.mkSimple "T") 0 [] tag)
def fieldWitness : Ob := .fieldOb (Name.mkSimple "S") 0 [] tag

theorem fieldClosure : field.cl = [field, fieldWitness] := by
  have base : fieldWitness.cl = [fieldWitness] := by
    rw [Ob.cl]
    simp [fieldWitness, Ob.wit, tag]
  have witnesses : field.wit = [fieldWitness] := by
    simp [field, fieldWitness, Ob.wit, tag]
  rw [Ob.cl]
  rw [List.flatMap_subtype (g := Ob.cl) (fun _ _ => rfl), List.unattach_attach, witnesses]
  simpa using congrArg (field :: ·) base

theorem fieldWitnessMember : fieldWitness ∈ field.wit := by
  simp [field, fieldWitness, Ob.wit, tag]

theorem fieldWitnessSmaller : fieldWitness.sz < field.sz :=
  Ob.sz_wit fieldWitnessMember

theorem backedClosure : ∃ K' : List Ob,
    (∀ k ∈ [field], k ∈ K') ∧
    (∀ k ∈ K', k ∈ field.cl) ∧ Backed (· ∈ K') := by
  apply Backed.close (fun _ ho _ hw => Ob.cl_closed ho hw)
  intro k hk
  cases List.mem_singleton.1 hk
  exact Ob.mem_cl_self field

def equalityEnvironment : VEnv := {
  constants name := if Name.mkSimple "Eq" = name then some eqConst else none
  defeqs _ := False }
def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem quotientEnvironmentWF : quotientEnvironment.WF := by
  have added : VEnv.empty.addConst (Name.mkSimple "Eq") eqConst = some equalityEnvironment := by
    rfl
  have equalityWF : equalityEnvironment.WF := by
    refine ⟨_, .decl (.axiom (ci := ⟨eqConst, Name.mkSimple "Eq"⟩) ?_ added) .empty⟩
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : equalityEnvironment.QuotReady := by simp [QuotReady, equalityEnvironment]
  obtain ⟨_, checked⟩ := equalityWF
  exact ⟨_, .decl (.quot ready
    (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)) checked⟩

theorem quotientCtorFamily : CtorFam quotientEnvironment
    (Name.str (Name.mkSimple "Quot") "mk") (Name.mkSimple "Quot") := by
  refine ⟨quotMkConst,
    [.sort (.param 0), .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1],
    [.param 0], [.bvar 2, .bvar 1], ?_, rfl⟩
  exact addQuot_quotMk
    (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)

theorem quotientStoredFamilyHead : ∃ ci,
    quotientEnvironment.constants (Name.str (Name.mkSimple "Quot") "mk") = some ci ∧
    resultHead ci.type = some (Name.mkSimple "Quot") :=
  quotientCtorFamily.result_head

theorem otherFamilyRejected
    (other : CtorFam quotientEnvironment (Name.str (Name.mkSimple "Quot") "mk")
      (Name.mkSimple "Eq")) : False := by
  have equal := CtorFam.unique quotientEnvironment quotientCtorFamily other
  exact (by decide : Name.mkSimple "Quot" ≠ Name.mkSimple "Eq") equal

def ctorClass : VExpr → Prop := ElCls quotientEnvironment 0 []
  (TyCls quotientEnvironment 0 [] (quotMkConst.type.instL [one]))
  (.const (Name.str (Name.mkSimple "Quot") "mk") [one])

theorem ctorClassTyped : TypedElCls quotientEnvironment 0 []
    (TyCls quotientEnvironment 0 [] (quotMkConst.type.instL [one])) ctorClass := by
  apply TypedElCls.of_hasType
  exact .const (addQuot_quotMk
    (show equalityEnvironment.addQuot = some quotientEnvironment from rfl))
    (by simp [one, VLevel.WF]) rfl

def ctorTypes : List Ob := [.rigid (Name.mkSimple "Quot") [oneF] 2 oneF]
def ctorObservation : Ob :=
  .ctorArgOb 2 [] (.app D c [tag] field)

theorem ctorObservationTyped : TypedOb quotientEnvironment 0 [] ctorClass ctorObservation ctorTypes := by
  refine .ctorArgOb ⟨_, _, _, _, .head _, quotientCtorFamily, ?_⟩
  intro e
  have impossible : 1 = 0 := congrFun e []
  cases impossible

theorem typedFiniteClosure : ∃ K' : List Ob,
    (∀ k ∈ [ctorObservation], k ∈ K') ∧
    (∀ k ∈ K', TypedOb quotientEnvironment 0 [] ctorClass k ctorTypes) ∧ Backed (· ∈ K') :=
  TypedOb.finite_close fun k hk => by
    cases List.mem_singleton.1 hk
    exact ctorObservationTyped

theorem typedWitness : TypedOb quotientEnvironment 0 [] ctorClass
    (.ctorArgOb 2 [] (.app D c [tag] fieldWitness)) ctorTypes := by
  apply ctorObservationTyped.wit
  simp only [ctorObservation, Ob.wit, List.mem_map]
  exact ⟨_, ⟨_, fieldWitnessMember, rfl⟩, rfl⟩

theorem noPropConstructor
    (h : TypedOb quotientEnvironment 0 [] ctorClass
      (.ctorHead (Name.str (Name.mkSimple "Quot") "mk") [oneF] 3)
      [.rigid (Name.mkSimple "Quot") [zeroF] 2 zeroF]) : False := by
  apply h.not_prop
  intro x hx
  cases List.mem_singleton.1 hx
  exact ⟨c, .rigid (.head _)⟩

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.exists_fin_function,
    `Lean4Lean.VEnv.Model.Covers.indices,
    `Lean4Lean.VEnv.Model.Covers.of_indices,
    `Lean4Lean.VEnv.Model.Covers.iff_indices,
    `Lean4Lean.VEnv.Model.Ob.Le.app',
    `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_of_covers,
    `Lean4Lean.VEnv.Model.Ob.Le.trans_aux,
    `Lean4Lean.VEnv.Model.Ob.Le.trans,
    `Lean4Lean.VEnv.Model.Covers.refl,
    `Lean4Lean.VEnv.Model.Covers.trans,
    `Lean4Lean.VEnv.Model.Covers.of_subset,
    `Lean4Lean.VEnv.Model.Ob.Sub.refl,
    `Lean4Lean.VEnv.Model.Ob.Sub.trans,
    `Lean4Lean.VEnv.Model.Ob.Sub.of_imp,
    `Lean4Lean.VEnv.Model.Ob.Le.sort_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.piDom_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.piCod_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.rigid_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.rigidArg_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.ctorHead_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.ctorArg_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.ctorArgOb_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.fieldOb_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.fieldTy_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.fieldDom_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.piDomOb_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.app_inv,
    `Lean4Lean.VEnv.Model.Ob.Le.app_iff,
    `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_iff,
    `Lean4Lean.VEnv.Model.exists_list_cover,
    `Lean4Lean.VEnv.Model.wrap_nil,
    `Lean4Lean.VEnv.Model.wrap_cons,
    `Lean4Lean.VEnv.Model.wrap_append,
    `Lean4Lean.VEnv.Model.RigidEnd.notApp,
    `Lean4Lean.VEnv.Model.wrap_inj,
    `Lean4Lean.VEnv.Model.Ob.mem_wit_fieldOb,
    `Lean4Lean.VEnv.Model.Ob.sz_le_szL,
    `Lean4Lean.VEnv.Model.Ob.szLL_take,
    `Lean4Lean.VEnv.Model.Ob.sz_wit,
    `Lean4Lean.VEnv.Model.Ob.mem_cl_self,
    `Lean4Lean.VEnv.Model.Ob.cl_sub,
    `Lean4Lean.VEnv.Model.Ob.cl_closed,
    `Lean4Lean.VEnv.Model.Backed.close,
    `Lean4Lean.VLevel.eval_inst_eq_evalAt,
    `Lean4Lean.VEnv.Model.constantHead_foldl,
    `Lean4Lean.VEnv.Model.resultHead_of_constantHead,
    `Lean4Lean.VEnv.Model.CtorFam.result_head,
    `Lean4Lean.VEnv.Model.CtorFam.unique,
    `Lean4Lean.VEnv.Model.TypedOb.strengthen,
    `Lean4Lean.VEnv.Model.TypedOb.mono,
    `Lean4Lean.VEnv.Model.TypedOb.not_sort_zero,
    `Lean4Lean.VEnv.Model.TypedOb.sort_congr,
    `Lean4Lean.VEnv.Model.TypedOb.not_prop,
    `Lean4Lean.VEnv.Model.TypedOb.wit,
    `Lean4Lean.VEnv.Model.TypedOb.backed,
    `Lean4Lean.VEnv.Model.TypedOb.finite_close,
    `Lean4Lean.VEnv.Model.Ob.cl,
    `ModelObservationsTest.emptyCoverage,
    `ModelObservationsTest.innerAB,
    `ModelObservationsTest.innerBD,
    `ModelObservationsTest.badDirection,
    `ModelObservationsTest.coverYX,
    `ModelObservationsTest.coverZY,
    `ModelObservationsTest.finiteIndices,
    `ModelObservationsTest.nestedComposition,
    `ModelObservationsTest.nestedSyntax,
    `ModelObservationsTest.cTyped,
    `ModelObservationsTest.typeCoverage,
    `ModelObservationsTest.applicationTyped,
    `ModelObservationsTest.applicationStrengthened,
    `ModelObservationsTest.propositionObserved,
    `ModelObservationsTest.proofObservationsEmpty,
    `ModelObservationsTest.fieldClosure,
    `ModelObservationsTest.fieldWitnessMember,
    `ModelObservationsTest.fieldWitnessSmaller,
    `ModelObservationsTest.backedClosure,
    `ModelObservationsTest.quotientEnvironmentWF,
    `ModelObservationsTest.quotientCtorFamily,
    `ModelObservationsTest.quotientStoredFamilyHead,
    `ModelObservationsTest.otherFamilyRejected,
    `ModelObservationsTest.ctorClassTyped,
    `ModelObservationsTest.ctorObservationTyped,
    `ModelObservationsTest.typedFiniteClosure,
    `ModelObservationsTest.typedWitness,
    `ModelObservationsTest.noPropConstructor]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.exists_fin_function, [`propext]),
    (`Lean4Lean.VEnv.Model.Covers.indices, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Covers.of_indices, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Covers.iff_indices, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.app', [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piCodOb_of_covers, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.trans_aux, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.trans, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Covers.refl, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Covers.trans, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Covers.of_subset, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Sub.refl, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Sub.trans, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Sub.of_imp, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.sort_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piDom_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piCod_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.rigid_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.rigidArg_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.ctorHead_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.ctorArg_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.ctorArgOb_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.fieldOb_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.fieldTy_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.fieldDom_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piDomOb_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piCodOb_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.app_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.app_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piCodOb_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.exists_list_cover, []),
    (`Lean4Lean.VEnv.Model.wrap_nil, []),
    (`Lean4Lean.VEnv.Model.wrap_cons, []),
    (`Lean4Lean.VEnv.Model.wrap_append, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RigidEnd.notApp, [`propext]),
    (`Lean4Lean.VEnv.Model.wrap_inj, [`propext]),
    (`Lean4Lean.VEnv.Model.Ob.mem_wit_fieldOb, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.sz_le_szL, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.szLL_take, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.sz_wit, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.mem_cl_self, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.cl_sub, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.cl_closed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Backed.close, [`Quot.sound, `propext]),
    (`Lean4Lean.VLevel.eval_inst_eq_evalAt, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.constantHead_foldl, [`propext]),
    (`Lean4Lean.VEnv.Model.resultHead_of_constantHead, [`propext]),
    (`Lean4Lean.VEnv.Model.CtorFam.result_head, [`propext]),
    (`Lean4Lean.VEnv.Model.CtorFam.unique, [`propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.strengthen, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.mono, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.not_sort_zero, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.sort_congr, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.not_prop, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.wit, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.backed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.finite_close, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.cl, [`Quot.sound, `propext]),
    (`ModelObservationsTest.emptyCoverage, [`Quot.sound, `propext]),
    (`ModelObservationsTest.innerAB, [`Quot.sound, `propext]),
    (`ModelObservationsTest.innerBD, [`Quot.sound, `propext]),
    (`ModelObservationsTest.badDirection, [`Quot.sound, `propext]),
    (`ModelObservationsTest.coverYX, [`Quot.sound, `propext]),
    (`ModelObservationsTest.coverZY, [`Quot.sound, `propext]),
    (`ModelObservationsTest.finiteIndices, [`Quot.sound, `propext]),
    (`ModelObservationsTest.nestedComposition, [`Quot.sound, `propext]),
    (`ModelObservationsTest.nestedSyntax, [`propext]),
    (`ModelObservationsTest.cTyped, [`propext]),
    (`ModelObservationsTest.typeCoverage, [`Quot.sound, `propext]),
    (`ModelObservationsTest.applicationTyped, [`Quot.sound, `propext]),
    (`ModelObservationsTest.applicationStrengthened, [`Quot.sound, `propext]),
    (`ModelObservationsTest.propositionObserved, [`Quot.sound, `propext]),
    (`ModelObservationsTest.proofObservationsEmpty, [`Quot.sound, `propext]),
    (`ModelObservationsTest.fieldClosure, [`Quot.sound, `propext]),
    (`ModelObservationsTest.fieldWitnessMember, [`Quot.sound, `propext]),
    (`ModelObservationsTest.fieldWitnessSmaller, [`Quot.sound, `propext]),
    (`ModelObservationsTest.backedClosure, [`Quot.sound, `propext]),
    (`ModelObservationsTest.quotientEnvironmentWF, [`Quot.sound, `propext]),
    (`ModelObservationsTest.quotientCtorFamily, [`Quot.sound, `propext]),
    (`ModelObservationsTest.quotientStoredFamilyHead, [`Quot.sound, `propext]),
    (`ModelObservationsTest.otherFamilyRejected, [`Quot.sound, `propext]),
    (`ModelObservationsTest.ctorClassTyped, [`Quot.sound, `propext]),
    (`ModelObservationsTest.ctorObservationTyped, [`Quot.sound, `propext]),
    (`ModelObservationsTest.typedFiniteClosure, [`Quot.sound, `propext]),
    (`ModelObservationsTest.typedWitness, [`Quot.sound, `propext]),
    (`ModelObservationsTest.noPropConstructor, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-observation manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-observation manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-observation axiom {root}"
    let some proof := info.value? (allowOpaque := true) | throwError "missing model-observation proof {root}"
    if proof.hasSorry then throwError "direct model-observation admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-observation axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-observation dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration.type.hasSorry then throwError "admitted model-observation type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then throwError "model-observation admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "model-observation traversal exceeded bound"
    let required :=
      if root == `Lean4Lean.VEnv.Model.Covers.indices then [`Lean4Lean.VEnv.Model.exists_fin_function]
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.app' then [`Lean4Lean.VEnv.Model.Covers.indices, `Lean4Lean.VEnv.Model.Ob.Le.app]
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_of_covers then [`Lean4Lean.VEnv.Model.Covers.indices, `Lean4Lean.VEnv.Model.Ob.Le.piCodOb]
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.trans then [`Lean4Lean.VEnv.Model.Ob.Le.trans_aux]
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.app_iff then [`Lean4Lean.VEnv.Model.Covers.of_indices, `Lean4Lean.VEnv.Model.Ob.Le.app']
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_iff then [`Lean4Lean.VEnv.Model.Covers.of_indices, `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_of_covers]
      else if root == `Lean4Lean.VEnv.Model.TypedOb.strengthen then [`Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.Covers.trans, `Lean4Lean.VEnv.Model.Ob.Le.piCodOb_inv, `Lean4Lean.VEnv.Model.Ob.Le.piDomOb_inv]
      else if root == `Lean4Lean.VEnv.Model.TypedOb.not_prop then [`Lean4Lean.VEnv.Model.TypedOb.not_sort_zero, `Lean4Lean.VEnv.Model.TypedOb.sort_congr]
      else if root == `Lean4Lean.VEnv.Model.TypedOb.finite_close then [`Lean4Lean.VEnv.Model.Backed.close, `Lean4Lean.VEnv.Model.TypedOb.backed]
      else if root == `Lean4Lean.VEnv.Model.Backed.close then [`Lean4Lean.VEnv.Model.Ob.cl, `Lean4Lean.VEnv.Model.Ob.cl_closed, `Lean4Lean.VEnv.Model.Ob.cl_sub]
      else if root == `Lean4Lean.VEnv.Model.Ob.cl then [`Lean4Lean.VEnv.Model.Ob.sz_wit]
      else if root == `ModelObservationsTest.nestedComposition then [`Lean4Lean.VEnv.Model.Ob.Le.trans, `Lean4Lean.VEnv.Model.Covers.indices, `ModelObservationsTest.innerAB, `ModelObservationsTest.innerBD, `ModelObservationsTest.coverYX, `ModelObservationsTest.coverZY]
      else if root == `ModelObservationsTest.badDirection then [`Lean4Lean.VEnv.Model.Ob.Le.app_iff]
      else if root == `ModelObservationsTest.finiteIndices then [`Lean4Lean.VEnv.Model.Covers.indices, `Lean4Lean.VEnv.Model.Covers.trans]
      else if root == `ModelObservationsTest.applicationStrengthened then [`Lean4Lean.VEnv.Model.TypedOb.strengthen, `ModelObservationsTest.typeCoverage, `ModelObservationsTest.applicationTyped]
      else if root == `ModelObservationsTest.fieldClosure then [`Lean4Lean.VEnv.Model.Ob.cl]
      else if root == `ModelObservationsTest.backedClosure then [`Lean4Lean.VEnv.Model.Backed.close, `Lean4Lean.VEnv.Model.Ob.cl_closed]
      else if root == `ModelObservationsTest.typedFiniteClosure then [`Lean4Lean.VEnv.Model.TypedOb.finite_close, `ModelObservationsTest.ctorObservationTyped]
      else if root == `ModelObservationsTest.typedWitness then [`Lean4Lean.VEnv.Model.TypedOb.wit, `ModelObservationsTest.ctorObservationTyped]
      else if root == `ModelObservationsTest.noPropConstructor then [`Lean4Lean.VEnv.Model.TypedOb.not_prop]
      else if root == `ModelObservationsTest.ctorObservationTyped then [`ModelObservationsTest.quotientCtorFamily]
      else if root == `ModelObservationsTest.proofObservationsEmpty then [`Lean4Lean.VEnv.Model.TypedOb.not_prop, `ModelObservationsTest.propositionObserved]
      else if root == `Lean4Lean.VEnv.Model.CtorFam.result_head then [`Lean4Lean.VEnv.Model.constantHead_foldl, `Lean4Lean.VEnv.Model.resultHead_of_constantHead]
      else if root == `Lean4Lean.VEnv.Model.CtorFam.unique then [`Lean4Lean.VEnv.Model.CtorFam.result_head]
      else if root == `ModelObservationsTest.quotientStoredFamilyHead then [`Lean4Lean.VEnv.Model.CtorFam.result_head, `ModelObservationsTest.quotientCtorFamily]
      else if root == `ModelObservationsTest.otherFamilyRejected then [`Lean4Lean.VEnv.Model.CtorFam.unique, `ModelObservationsTest.quotientCtorFamily]
      else []
    unless required.all visited.contains do
      throwError "model-observation proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelObservationsTest
