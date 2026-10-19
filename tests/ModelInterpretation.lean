import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Interp
import Lean.Util.CollectAxioms

namespace ModelInterpretationTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open scoped Lean4Lean.VEnv.Model

def one : VLevel := .succ .zero
def oneF : List Nat → Nat := fun _ => 1
def D : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort one)
def c : VExpr → Prop := ElCls VEnv.empty 0 [] D (.sort .zero)
def tag : Ob := .sort zeroF

theorem cTyped : TypedElCls VEnv.empty 0 [] D c :=
  .of_hasType (.sort (by trivial))

theorem tagBacked : Backed (listSet [tag]) := by
  intro o ho w hw
  cases List.mem_singleton.1 ho
  cases hw

theorem identityObserved : Obs VEnv.empty 0 [] .id .empty
    (.lam (.sort one) (.bvar 0)) (.app D c [tag] tag) := by
  refine .lam (τs := [.sort oneF]) (x := .sort .zero) cTyped ?_ ?_ tagBacked ?_ (.bvar (.head _))
  · intro τ hτ
    cases List.mem_singleton.1 hτ
    exact .sort
  · intro k hk
    cases List.mem_singleton.1 hk
    exact .sort (.head _)
  · exact ElCls.self

theorem identityApplied : Obs VEnv.empty 0 [] .id .empty
    (.app (.lam (.sort one) (.bvar 0)) (.sort .zero)) tag :=
  .app identityObserved rfl (K' := [tag]) (fun k hk => by
    cases List.mem_singleton.1 hk
    exact .sort) .refl

theorem instantiatedIdentity : Obs VEnv.empty 0 [] .id .empty
    ((VExpr.bvar 0).inst (.sort .zero)) tag := by
  apply Obs.inst_iff.2
  exact .bvar .sort

-- Substitution crosses both binders, including free variables in binder types.
theorem nestedSubstitution (τ σ : VExpr.Subst) (S : ObSets) (o : Ob) :
    Obs VEnv.empty 0 [] σ S
      ((VExpr.lam (.sort one) (.forallE (.bvar 0) (.app (.bvar 2) (.bvar 1)))).subst τ) o ↔
    Obs VEnv.empty 0 [] (τ.comp σ) (fun i => Obs VEnv.empty 0 [] σ S (τ i))
      (.lam (.sort one) (.forallE (.bvar 0) (.app (.bvar 2) (.bvar 1)))) o :=
  Obs.subst_iff

def weakKey : Ob := .app D c [] tag
def strongKey : Ob := .app D c [tag] tag

theorem keyStrict : weakKey ≼ strongKey := .app' (fun _ h => nomatch h) .refl

theorem keyDifferent : weakKey ≠ strongKey := by
  intro h
  have := (Ob.app.inj h).2.2.1
  cases this

def sourceSets : ObSets := fun _ o => o = strongKey
def targetSets : ObSets := fun _ o => o = weakKey

theorem sourceApplication : Obs VEnv.empty 0 [] .id sourceSets
    (.app (.bvar 0) (.sort .zero)) tag :=
  .app (.bvar rfl) rfl (K' := [tag]) (fun k hk => by
    cases List.mem_singleton.1 hk
    exact .sort) .refl

theorem applicationSubsumed : ∃ o,
    Obs VEnv.empty 0 [] .id targetSets (.app (.bvar 0) (.sort .zero)) o ∧ o ≼ tag := by
  apply sourceApplication.mono_le
  intro i o h
  cases h
  exact ⟨weakKey, rfl, keyStrict⟩

theorem lambdaDemand : Obs VEnv.empty 0 [] .id
    (ObSets.empty.cons (fun _ => True))
    (.lam (.sort one) (.app (.bvar 1) (.bvar 0))) strongKey := by
  refine .lam (τs := [.sort oneF]) (x := .sort .zero) cTyped ?_ ?_ tagBacked ?_ ?_
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort
  · intro k hk; cases List.mem_singleton.1 hk; exact .sort (.head _)
  · exact ElCls.self
  · exact .app (D := D) (c := c) (.bvar trivial) rfl (K' := [tag]) (fun k hk => .bvar hk) .refl

theorem finiteDemand : ∃ K : List Ob, Backed (listSet K) ∧
    Obs VEnv.empty 0 [] .id (ObSets.empty.cons (listSet K))
      (.lam (.sort one) (.app (.bvar 1) (.bvar 0))) strongKey := by
  obtain ⟨K, _, hb, ho⟩ := lambdaDemand.compact0B (fun _ _ _ _ => trivial)
  exact ⟨K, hb, ho⟩

theorem demandNonempty (h : Obs VEnv.empty 0 [] .id (ObSets.empty.cons (listSet K))
    (.lam (.sort one) (.app (.bvar 1) (.bvar 0))) strongKey) : K ≠ [] := by
  intro e
  subst K
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hbody⟩ := Obs.lam_iff.1 h
  obtain ⟨_, _, _, _, hf, _, _, _⟩ := Obs.app_iff.1 hbody
  have impossible := Obs.bvar_iff.1 hf
  cases impossible

def witness : Ob := .ctorArgOb 0 [] tag
def field : Ob := .fieldOb (Name.mkSimple "F") 1 [[tag]] witness

theorem witnessedObservation : Obs VEnv.empty 0 [] .id
    (fun _ o => o ∈ field.cl) (.bvar 0) field := .bvar (Ob.mem_cl_self field)

theorem hereditaryWitness : Obs VEnv.empty 0 [] .id
    (fun _ o => o ∈ field.cl) (.bvar 0) (.fieldOb (Name.mkSimple "F") 0 [] tag) := by
  apply witnessedObservation.backed (fun _ _ ho _ hw => Ob.cl_closed ho hw)
  exact Ob.mem_wit_fieldOb.2 (.inl ⟨0, [tag], tag, rfl, .head _, rfl⟩)

theorem valuationCons : TV VEnv.empty 0 [] [.sort one]
    (VExpr.Subst.id.cons (.sort .zero)) (ObSets.empty.cons (listSet [tag])) := by
  refine TV.cons TV.empty tagBacked ?_
  intro k hk
  cases List.mem_singleton.1 hk
  exact ⟨[.sort oneF], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort,
    .sort (.head _)⟩

-- A checked definition supplies actual lookup, equation and type observations.
def deltaName : Name := Name.mkSimple "ObservedProp"
def deltaValue : VDefVal := ⟨⟨⟨0, .sort one⟩, deltaName⟩, .sort .zero⟩
def deltaBase : VEnv := {
  constants n := if deltaName = n then some deltaValue.toVConstant else none
  defeqs _ := False }
def deltaEnv : VEnv := deltaBase.addDefEq deltaValue.toDefEq

theorem deltaEnvironmentWF : deltaEnv.WF := by
  refine ⟨_, .decl (.def (ci := deltaValue) ?_ ?_) .empty⟩
  · exact .sort (by trivial)
  · rfl

theorem rigidBeforeDefinition : Obs deltaBase 0 [] .id .empty
    (.const deltaName []) (.rigid deltaName [] 0 oneF) := by
  refine .const (ci := deltaValue.toVConstant) (τs := [.sort oneF]) (keys := [])
    (fun _ h => nomatch h) ?_ ?_ (.rigid (.head _)) (.inl ⟨oneF, rfl⟩)
  · simp [deltaBase]
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort

theorem deltaObserved : Obs deltaEnv 0 [] .id .empty (.const deltaName []) tag := by
  refine .delta (df := deltaValue.toDefEq) (ci := deltaValue.toVConstant)
    (τs := [.sort oneF]) (.inl rfl) rfl ?_ ?_ (.sort (.head _)) .sort
  · simp [deltaEnv, VEnv.addDefEq, deltaBase]
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort

theorem deltaNotRigid : ¬ deltaEnv.Rigid deltaName := by
  intro h
  exact h deltaValue.toDefEq (.inl rfl) [] rfl

theorem deltaFiltered : TypedAt deltaEnv 0 []
    (ElCls deltaEnv 0 [] (TyCls deltaEnv 0 [] (.sort one)) (.const deltaName []))
    .id .empty (.sort one) tag :=
  deltaObserved.const_typed (ci := deltaValue.toVConstant) (by simp [deltaEnv, VEnv.addDefEq, deltaBase])

theorem missingConstantRejected (h : Obs VEnv.empty 0 [] σ S (.const deltaName []) o) : False := by
  obtain ⟨_, impossible⟩ := h.const_lookup
  cases impossible

-- The actual installed quotient equation is pattern-headed, not a delta rule.
def equalityEnvironment : VEnv := {
  constants n := if Name.mkSimple "Eq" = n then some eqConst else none
  defeqs _ := False }
def quotientEnvironment : VEnv := (equalityEnvironment.addQuot).getD .empty

theorem quotientStored : quotientEnvironment.defeqs quotDefEq :=
  addQuot_defeq (show equalityEnvironment.addQuot = some quotientEnvironment from rfl)

theorem quotientMajor : quotDefEq.HasConstructorMajor (Name.str (Name.mkSimple "Quot") "mk") :=
  ⟨_, [.param 0], [.bvar 5, .bvar 4, .bvar 0], rfl⟩

theorem quotientConstructorInstalled : IsInstalledCtor quotientEnvironment
    (Name.str (Name.mkSimple "Quot") "mk") := ⟨quotDefEq, quotientStored, quotientMajor⟩

theorem quotientRuleNotRigid : ¬ quotientEnvironment.Rigid
    (Name.str (Name.mkSimple "Quot") "lift") := by
  intro h
  exact h quotDefEq quotientStored [.param 0, .param 1] rfl

theorem wrongQuotientMajorRejected
    (h : quotDefEq.HasConstructorMajor (Name.mkSimple "Eq")) : False := by
  have e := quotientMajor.unique h
  cases e

theorem quotientRuleUnique (df : VDefEq) (h : quotientEnvironment.defeqs df) : df = quotDefEq := by
  exact h.elim id nofun

-- Repeated leading variables take their first matching key.
theorem firstRuleBinding : RuleBind VEnv.empty 0 [] [.sort one] []
    [.bvar 0, .bvar 0] 0 [] false [(D, c, [tag]), (D, c, [])] []
    (fun _ => .sort .zero) (fun _ => listSet [tag]) := by
  refine ⟨fun _ => tagBacked, fun x hx => ?_⟩
  have : x = 0 := by simpa using hx
  subst x
  refine .inl ⟨0, (D, c, [tag]), rfl, ?_, rfl, ?_, ?_, rfl⟩
  · intro j hj; omega
  · exact cTyped
  · exact ElCls.self

theorem laterBindingRejected
    (h : ∀ j < 1, ([VExpr.bvar 0, .bvar 0] : List VExpr)[j]? ≠ some (.bvar 0)) : False :=
  h 0 (by decide) rfl

theorem closedIdentity (σ : VExpr.Subst) (S : ObSets) : Obs VEnv.empty 0 [] σ S
    (.lam (.sort one) (.bvar 0)) (.app D c [tag] tag) :=
  (Obs.closed_iff_id (by exact ⟨trivial, Nat.zero_lt_succ 0⟩)).2 identityObserved

-- The proof-field alternative still supplies an actual term and a Prop type.
def P : VExpr := .const (Name.mkSimple "P") []
def proofTerm : VExpr := .const (Name.mkSimple "p") []
def proofEnv : VEnv := {
  constants n := if n = Name.mkSimple "P" then some ⟨0, .sort .zero⟩
    else if n = Name.mkSimple "p" then some ⟨0, P⟩ else none
  defeqs _ := False }

theorem proofTyped : proofEnv.HasType 0 [] proofTerm P :=
  .const (ci := ⟨0, P⟩) (by rfl) (by simp) rfl

theorem propositionTyped : proofEnv.HasType 0 [] P (.sort .zero) :=
  .const (ci := ⟨0, .sort .zero⟩) (by rfl) (by simp) rfl

theorem proofFieldBinding : RuleBind proofEnv 0 [] [P] [] [] 0 [0] true [] []
    (fun _ => proofTerm) ObSets.empty := by
  refine ⟨(fun _ _ h => nomatch h), fun x hx => ?_⟩
  have : x = 0 := by simpa using hx
  subst x
  refine .inr ⟨fun i => by cases i <;> simp, 0, rfl, .inr ?_⟩
  exact ⟨⟨P, TyCls.self, proofTyped⟩, ⟨P, TyCls.self, propositionTyped⟩, rfl⟩

theorem singletonConditionRejectsAmbiguity
    (h : ∀ df ls, (quotientEnvironment.addDefEq { quotDefEq with rhs := .sort .zero }).defeqs df →
      df.lhs.stripLams.appHead = .const (Name.str (Name.mkSimple "Quot") "lift") ls →
      df = quotDefEq) : False := by
  have bad := h { quotDefEq with rhs := .sort .zero } [.param 0, .param 1] (.inl rfl) rfl
  have impossible := congrArg VDefEq.rhs bad
  cases impossible

end ModelInterpretationTest

namespace ModelInterpretationAudit
open Lean

-- Traverse types, constructors and opaque bodies directly on both toolchains.
run_meta
  let roots : List Name := [
    `Lean4Lean.VExpr.mkApps,
    `Lean4Lean.VExpr.wrapLams,
    `Lean4Lean.VExpr.stripLams,
    `Lean4Lean.VExpr.appHead,
    `Lean4Lean.VExpr.appHead_mkApps,
    `Lean4Lean.VExpr.stripLams_wrapLams,
    `Lean4Lean.VEnv.Rigid,
    `Lean4Lean.VDefEq.HasConstructorMajor,
    `Lean4Lean.VDefEq.HasConstructorMajor.unique,
    `Lean4Lean.VEnv.Model.ObSets,
    `Lean4Lean.VEnv.Model.ObSets.cons,
    `Lean4Lean.VEnv.Model.ObSets.lift_l,
    `Lean4Lean.VEnv.Model.ObSets.empty,
    `Lean4Lean.VEnv.Model.ObSets.update,
    `Lean4Lean.VEnv.Model.ObSets.lift_l_cons,
    `Lean4Lean.VEnv.Model.ObSets.update_cons,
    `Lean4Lean.VExpr.Subst.lift_l_cons,
    `Lean4Lean.VExpr.Subst.lift_comp_cons,
    `Lean4Lean.VEnv.Model.listSet,
    `Lean4Lean.VEnv.Model.IsInstalledCtor,
    `Lean4Lean.VEnv.Model.CtorEnd,
    `Lean4Lean.VEnv.Model.KeysBacked,
    `Lean4Lean.VEnv.Model.piCodChain,
    `Lean4Lean.VEnv.Model.piCodChain_nil,
    `Lean4Lean.VEnv.Model.piCodChain_cons,
    `Lean4Lean.VEnv.Model.piCodChain_append,
    `Lean4Lean.VEnv.Model.binderTy,
    `Lean4Lean.VEnv.Model.RuleBind,
    `Lean4Lean.VEnv.Model.Obs,
    `Lean4Lean.VEnv.Model.TypedAt,
    `Lean4Lean.VEnv.Model.TV,
    `Lean4Lean.VEnv.Model.Obs.bvar_iff,
    `Lean4Lean.VEnv.Model.Obs.sort_iff,
    `Lean4Lean.VEnv.Model.Obs.forallE_iff,
    `Lean4Lean.VEnv.Model.Obs.lam_iff,
    `Lean4Lean.VEnv.Model.Obs.app_iff,
    `Lean4Lean.VEnv.Model.Obs.const_indep,
    `Lean4Lean.VEnv.Model.Obs.piDom_mem,
    `Lean4Lean.VEnv.Model.Obs.piDomOb_mem,
    `Lean4Lean.VEnv.Model.Obs.piCod_mem,
    `Lean4Lean.VEnv.Model.Obs.piCodOb_mem,
    `Lean4Lean.VEnv.Model.Obs.piCodOb_backed,
    `Lean4Lean.VEnv.Model.Obs.sort_mem,
    `Lean4Lean.VEnv.Model.Obs.lift'_iff,
    `Lean4Lean.VEnv.Model.Obs.lift_cons_iff,
    `Lean4Lean.VEnv.Model.Obs.lift_cons_set,
    `Lean4Lean.VEnv.Model.Obs.subst_iff,
    `Lean4Lean.VEnv.Model.Obs.inst_iff,
    `Lean4Lean.VEnv.Model.Obs.mono,
    `Lean4Lean.VEnv.Model.Obs.mono_le,
    `Lean4Lean.VEnv.Model.Obs.collect,
    `Lean4Lean.VEnv.Model.Obs.update_mono,
    `Lean4Lean.VEnv.Model.Obs.compact_bvar,
    `Lean4Lean.VEnv.Model.Obs.compact,
    `Lean4Lean.VEnv.Model.Obs.compact0,
    `Lean4Lean.VEnv.Model.Obs.compact0B,
    `Lean4Lean.VExpr.ClosedN.subst_congr,
    `Lean4Lean.VEnv.Model.Obs.closed_iff,
    `Lean4Lean.VEnv.Model.Obs.closed_iff_id,
    `Lean4Lean.VEnv.Model.wit_wrap,
    `Lean4Lean.VEnv.Model.mem_wit_wrap,
    `Lean4Lean.VEnv.Model.Obs.backed,
    `Lean4Lean.VEnv.Model.TypedAt.mono_le,
    `Lean4Lean.VEnv.Model.TypedAt.congr_cls,
    `Lean4Lean.VEnv.Model.TypedAt.merge,
    `Lean4Lean.VEnv.Model.TypedAt.lift_cons,
    `Lean4Lean.VEnv.Model.vcls_bvar_zero,
    `Lean4Lean.VEnv.Model.vcls_bvar_succ,
    `Lean4Lean.VEnv.Model.TV.empty,
    `Lean4Lean.VEnv.Model.TV.cons,
    `Lean4Lean.VEnv.Model.Obs.const_lookup,
    `Lean4Lean.VEnv.Model.Obs.const_typed,
    `ModelInterpretationTest.one,
    `ModelInterpretationTest.oneF,
    `ModelInterpretationTest.D,
    `ModelInterpretationTest.c,
    `ModelInterpretationTest.tag,
    `ModelInterpretationTest.cTyped,
    `ModelInterpretationTest.tagBacked,
    `ModelInterpretationTest.identityObserved,
    `ModelInterpretationTest.identityApplied,
    `ModelInterpretationTest.instantiatedIdentity,
    `ModelInterpretationTest.nestedSubstitution,
    `ModelInterpretationTest.weakKey,
    `ModelInterpretationTest.strongKey,
    `ModelInterpretationTest.keyStrict,
    `ModelInterpretationTest.keyDifferent,
    `ModelInterpretationTest.sourceSets,
    `ModelInterpretationTest.targetSets,
    `ModelInterpretationTest.sourceApplication,
    `ModelInterpretationTest.applicationSubsumed,
    `ModelInterpretationTest.lambdaDemand,
    `ModelInterpretationTest.finiteDemand,
    `ModelInterpretationTest.demandNonempty,
    `ModelInterpretationTest.witness,
    `ModelInterpretationTest.field,
    `ModelInterpretationTest.witnessedObservation,
    `ModelInterpretationTest.hereditaryWitness,
    `ModelInterpretationTest.valuationCons,
    `ModelInterpretationTest.deltaName,
    `ModelInterpretationTest.deltaValue,
    `ModelInterpretationTest.deltaBase,
    `ModelInterpretationTest.deltaEnv,
    `ModelInterpretationTest.deltaEnvironmentWF,
    `ModelInterpretationTest.rigidBeforeDefinition,
    `ModelInterpretationTest.deltaObserved,
    `ModelInterpretationTest.deltaNotRigid,
    `ModelInterpretationTest.deltaFiltered,
    `ModelInterpretationTest.missingConstantRejected,
    `ModelInterpretationTest.equalityEnvironment,
    `ModelInterpretationTest.quotientEnvironment,
    `ModelInterpretationTest.quotientStored,
    `ModelInterpretationTest.quotientMajor,
    `ModelInterpretationTest.quotientConstructorInstalled,
    `ModelInterpretationTest.quotientRuleNotRigid,
    `ModelInterpretationTest.wrongQuotientMajorRejected,
    `ModelInterpretationTest.quotientRuleUnique,
    `ModelInterpretationTest.firstRuleBinding,
    `ModelInterpretationTest.laterBindingRejected,
    `ModelInterpretationTest.closedIdentity,
    `ModelInterpretationTest.P,
    `ModelInterpretationTest.proofTerm,
    `ModelInterpretationTest.proofEnv,
    `ModelInterpretationTest.proofTyped,
    `ModelInterpretationTest.propositionTyped,
    `ModelInterpretationTest.proofFieldBinding,
    `ModelInterpretationTest.singletonConditionRejectsAmbiguity,
    `Lean4Lean.VEnv.Model.Obs.bvar,
    `Lean4Lean.VEnv.Model.Obs.sort,
    `Lean4Lean.VEnv.Model.Obs.piDom,
    `Lean4Lean.VEnv.Model.Obs.piDomOb,
    `Lean4Lean.VEnv.Model.Obs.piCod,
    `Lean4Lean.VEnv.Model.Obs.piCodOb,
    `Lean4Lean.VEnv.Model.Obs.lam,
    `Lean4Lean.VEnv.Model.Obs.app,
    `Lean4Lean.VEnv.Model.Obs.const,
    `Lean4Lean.VEnv.Model.Obs.delta,
    `Lean4Lean.VEnv.Model.Obs.ctor,
    `Lean4Lean.VEnv.Model.Obs.rule]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VExpr.mkApps, []),
    (`Lean4Lean.VExpr.wrapLams, []),
    (`Lean4Lean.VExpr.stripLams, [`propext]),
    (`Lean4Lean.VExpr.appHead, [`propext]),
    (`Lean4Lean.VExpr.appHead_mkApps, [`propext]),
    (`Lean4Lean.VExpr.stripLams_wrapLams, [`propext]),
    (`Lean4Lean.VEnv.Rigid, [`propext]),
    (`Lean4Lean.VDefEq.HasConstructorMajor, [`propext]),
    (`Lean4Lean.VDefEq.HasConstructorMajor.unique, [`propext]),
    (`Lean4Lean.VEnv.Model.ObSets, []),
    (`Lean4Lean.VEnv.Model.ObSets.cons, []),
    (`Lean4Lean.VEnv.Model.ObSets.lift_l, []),
    (`Lean4Lean.VEnv.Model.ObSets.empty, []),
    (`Lean4Lean.VEnv.Model.ObSets.update, []),
    (`Lean4Lean.VEnv.Model.ObSets.lift_l_cons, [`Quot.sound]),
    (`Lean4Lean.VEnv.Model.ObSets.update_cons, [`Quot.sound]),
    (`Lean4Lean.VExpr.Subst.lift_l_cons, [`Quot.sound]),
    (`Lean4Lean.VExpr.Subst.lift_comp_cons, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.listSet, []),
    (`Lean4Lean.VEnv.Model.IsInstalledCtor, [`propext]),
    (`Lean4Lean.VEnv.Model.CtorEnd, []),
    (`Lean4Lean.VEnv.Model.KeysBacked, [`propext]),
    (`Lean4Lean.VEnv.Model.piCodChain, []),
    (`Lean4Lean.VEnv.Model.piCodChain_nil, []),
    (`Lean4Lean.VEnv.Model.piCodChain_cons, []),
    (`Lean4Lean.VEnv.Model.piCodChain_append, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.binderTy, [`propext]),
    (`Lean4Lean.VEnv.Model.RuleBind, [`propext]),
    (`Lean4Lean.VEnv.Model.Obs, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.bvar_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.sort_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.forallE_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lam_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.app_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.const_indep, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piDom_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piDomOb_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piCod_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piCodOb_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piCodOb_backed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.sort_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lift'_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lift_cons_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lift_cons_set, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.subst_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.inst_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.mono, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.mono_le, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.collect, [`propext]),
    (`Lean4Lean.VEnv.Model.Obs.update_mono, [`propext]),
    (`Lean4Lean.VEnv.Model.Obs.compact_bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.compact, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.compact0, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.compact0B, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.ClosedN.subst_congr, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.closed_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.closed_iff_id, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wit_wrap, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mem_wit_wrap, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.backed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.mono_le, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.congr_cls, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.merge, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.lift_cons, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_bvar_zero, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_bvar_succ, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.empty, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.cons, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.const_lookup, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.const_typed, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.one, []),
    (`ModelInterpretationTest.oneF, []),
    (`ModelInterpretationTest.D, [`propext]),
    (`ModelInterpretationTest.c, [`propext]),
    (`ModelInterpretationTest.tag, []),
    (`ModelInterpretationTest.cTyped, [`propext]),
    (`ModelInterpretationTest.tagBacked, [`propext]),
    (`ModelInterpretationTest.identityObserved, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.identityApplied, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.instantiatedIdentity, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.nestedSubstitution, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.weakKey, [`propext]),
    (`ModelInterpretationTest.strongKey, [`propext]),
    (`ModelInterpretationTest.keyStrict, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.keyDifferent, [`propext]),
    (`ModelInterpretationTest.sourceSets, [`propext]),
    (`ModelInterpretationTest.targetSets, [`propext]),
    (`ModelInterpretationTest.sourceApplication, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.applicationSubsumed, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.lambdaDemand, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.finiteDemand, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.demandNonempty, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.witness, []),
    (`ModelInterpretationTest.field, []),
    (`ModelInterpretationTest.witnessedObservation, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.hereditaryWitness, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.valuationCons, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaName, []),
    (`ModelInterpretationTest.deltaValue, []),
    (`ModelInterpretationTest.deltaBase, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaEnv, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaEnvironmentWF, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.rigidBeforeDefinition, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaObserved, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaNotRigid, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.deltaFiltered, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.missingConstantRejected, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.equalityEnvironment, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.quotientEnvironment, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.quotientStored, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.quotientMajor, [`propext]),
    (`ModelInterpretationTest.quotientConstructorInstalled, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.quotientRuleNotRigid, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.wrongQuotientMajorRejected, [`propext]),
    (`ModelInterpretationTest.quotientRuleUnique, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.firstRuleBinding, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.laterBindingRejected, [`propext]),
    (`ModelInterpretationTest.closedIdentity, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.P, []),
    (`ModelInterpretationTest.proofTerm, []),
    (`ModelInterpretationTest.proofEnv, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.proofTyped, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.propositionTyped, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.proofFieldBinding, [`Quot.sound, `propext]),
    (`ModelInterpretationTest.singletonConditionRejectsAmbiguity, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.sort, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piDom, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piDomOb, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piCod, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.piCodOb, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lam, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.app, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.const, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.delta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.ctor, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.rule, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-interpretation manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-interpretation manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-interpretation axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-interpretation admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-interpretation value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-interpretation dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-interpretation type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-interpretation admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-interpretation dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-interpretation traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-interpretation axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.Obs then [`Lean4Lean.VEnv.Model.Obs.bvar, `Lean4Lean.VEnv.Model.Obs.sort, `Lean4Lean.VEnv.Model.Obs.piDom, `Lean4Lean.VEnv.Model.Obs.piDomOb, `Lean4Lean.VEnv.Model.Obs.piCod, `Lean4Lean.VEnv.Model.Obs.piCodOb, `Lean4Lean.VEnv.Model.Obs.lam, `Lean4Lean.VEnv.Model.Obs.app, `Lean4Lean.VEnv.Model.Obs.const, `Lean4Lean.VEnv.Model.Obs.delta, `Lean4Lean.VEnv.Model.Obs.ctor, `Lean4Lean.VEnv.Model.Obs.rule]
      else if root == `Lean4Lean.VEnv.Model.Obs.rule then [`Lean4Lean.VEnv.Model.RuleBind, `Lean4Lean.VEnv.Model.KeysBacked, `Lean4Lean.VEnv.Model.TypedOb, `Lean4Lean.VEnv.Model.piCodChain, `Lean4Lean.VEnv.defeqs, `Lean4Lean.VEnv.constants, `Lean4Lean.VExpr.wrapLams, `Lean4Lean.VExpr.mkApps, `Lean4Lean.VExpr.stripLams, `Lean4Lean.VExpr.appHead]
      else if root == `Lean4Lean.VEnv.Model.Obs.delta then [`Lean4Lean.VEnv.defeqs, `Lean4Lean.VEnv.constants, `Lean4Lean.VEnv.Model.TypedOb, `Lean4Lean.VExpr.instL]
      else if root == `Lean4Lean.VEnv.Model.Obs.ctor then [`Lean4Lean.VEnv.Model.IsInstalledCtor, `Lean4Lean.VEnv.Model.KeysBacked, `Lean4Lean.VEnv.Model.CtorEnd, `Lean4Lean.VEnv.Model.TypedOb]
      else if root == `Lean4Lean.VEnv.Model.IsInstalledCtor then [`Lean4Lean.VDefEq.HasConstructorMajor, `Lean4Lean.VEnv.defeqs]
      else if root == `Lean4Lean.VEnv.Rigid then [`Lean4Lean.VExpr.stripLams, `Lean4Lean.VExpr.appHead]
      else if root == `Lean4Lean.VDefEq.HasConstructorMajor.unique then [`Lean4Lean.VExpr.appHead_mkApps]
      else if root == `Lean4Lean.VEnv.Model.Obs.subst_iff then [`Lean4Lean.VEnv.Model.Obs.lift_cons_set, `Lean4Lean.VEnv.Model.Obs.const_indep, `Lean4Lean.VExpr.Subst.lift_comp_cons, `Lean4Lean.VExpr.subst_subst]
      else if root == `Lean4Lean.VEnv.Model.Obs.inst_iff then [`Lean4Lean.VEnv.Model.Obs.subst_iff]
      else if root == `Lean4Lean.VEnv.Model.Obs.lift_cons_set then [`Lean4Lean.VEnv.Model.Obs.lift_cons_iff]
      else if root == `Lean4Lean.VEnv.Model.Obs.mono_le then [`Lean4Lean.VEnv.Model.TypedOb.strengthen, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.Ob.Le.app_inv, `Lean4Lean.VEnv.Model.Covers.trans, `Lean4Lean.VEnv.Model.Covers.indices]
      else if root == `Lean4Lean.VEnv.Model.Obs.compact then [`Lean4Lean.VEnv.Model.Obs.collect, `Lean4Lean.VEnv.Model.Obs.update_mono, `Lean4Lean.VEnv.Model.ObSets.update_cons, `Lean4Lean.VEnv.Model.Obs.mono]
      else if root == `Lean4Lean.VEnv.Model.Obs.compact0B then [`Lean4Lean.VEnv.Model.Backed.close, `Lean4Lean.VEnv.Model.Obs.compact0]
      else if root == `Lean4Lean.VEnv.Model.Obs.closed_iff then [`Lean4Lean.VExpr.ClosedN.subst_congr, `Lean4Lean.VEnv.Model.Obs.const_indep]
      else if root == `Lean4Lean.VEnv.Model.Obs.backed then [`Lean4Lean.VEnv.Model.TypedOb.wit, `Lean4Lean.VEnv.Model.mem_wit_wrap, `Lean4Lean.VEnv.Model.RuleBind, `Lean4Lean.VEnv.Model.KeysBacked]
      else if root == `Lean4Lean.VEnv.Model.TypedAt.merge then [`Lean4Lean.VEnv.Model.Obs.collect, `Lean4Lean.VEnv.Model.TypedOb.mono]
      else if root == `Lean4Lean.VEnv.Model.TV.cons then [`Lean4Lean.VEnv.Model.TypedAt.lift_cons, `Lean4Lean.VEnv.Model.vcls_bvar_zero, `Lean4Lean.VEnv.Model.vcls_bvar_succ]
      else if root == `ModelInterpretationTest.identityApplied then [`Lean4Lean.VEnv.Model.Obs.app, `ModelInterpretationTest.identityObserved, `Lean4Lean.VEnv.Model.Covers.refl]
      else if root == `ModelInterpretationTest.nestedSubstitution then [`Lean4Lean.VEnv.Model.Obs.subst_iff]
      else if root == `ModelInterpretationTest.applicationSubsumed then [`Lean4Lean.VEnv.Model.Obs.mono_le, `ModelInterpretationTest.keyStrict, `ModelInterpretationTest.sourceApplication]
      else if root == `ModelInterpretationTest.finiteDemand then [`Lean4Lean.VEnv.Model.Obs.compact0B, `ModelInterpretationTest.lambdaDemand]
      else if root == `ModelInterpretationTest.demandNonempty then [`Lean4Lean.VEnv.Model.Obs.lam_iff, `Lean4Lean.VEnv.Model.Obs.app_iff, `Lean4Lean.VEnv.Model.Obs.bvar_iff]
      else if root == `ModelInterpretationTest.hereditaryWitness then [`Lean4Lean.VEnv.Model.Obs.backed, `Lean4Lean.VEnv.Model.Ob.cl_closed, `Lean4Lean.VEnv.Model.Ob.mem_wit_fieldOb]
      else if root == `ModelInterpretationTest.valuationCons then [`Lean4Lean.VEnv.Model.TV.cons]
      else if root == `ModelInterpretationTest.deltaEnvironmentWF then [`Lean4Lean.VDecl.WF.def, `Lean4Lean.VEnv.HasType.sort]
      else if root == `ModelInterpretationTest.deltaObserved then [`Lean4Lean.VEnv.Model.Obs.delta, `Lean4Lean.VDefVal.toDefEq]
      else if root == `ModelInterpretationTest.deltaFiltered then [`Lean4Lean.VEnv.Model.Obs.const_typed, `ModelInterpretationTest.deltaObserved]
      else if root == `ModelInterpretationTest.missingConstantRejected then [`Lean4Lean.VEnv.Model.Obs.const_lookup]
      else if root == `ModelInterpretationTest.quotientConstructorInstalled then [`ModelInterpretationTest.quotientMajor, `ModelInterpretationTest.quotientStored]
      else if root == `ModelInterpretationTest.quotientRuleNotRigid then [`ModelInterpretationTest.quotientStored, `Lean4Lean.VEnv.Rigid]
      else if root == `ModelInterpretationTest.wrongQuotientMajorRejected then [`Lean4Lean.VDefEq.HasConstructorMajor.unique, `ModelInterpretationTest.quotientMajor]
      else if root == `ModelInterpretationTest.firstRuleBinding then [`Lean4Lean.VEnv.Model.RuleBind, `Lean4Lean.VEnv.Model.binderTy, `ModelInterpretationTest.cTyped]
      else if root == `ModelInterpretationTest.proofFieldBinding then [`Lean4Lean.VEnv.Model.RuleBind, `ModelInterpretationTest.proofTyped, `ModelInterpretationTest.propositionTyped, `Lean4Lean.VEnv.Model.TyCls.self]
      else if root == `ModelInterpretationTest.closedIdentity then [`Lean4Lean.VEnv.Model.Obs.closed_iff_id, `ModelInterpretationTest.identityObserved]
      else if root == `ModelInterpretationTest.singletonConditionRejectsAmbiguity then [`Lean4Lean.VEnv.addDefEq]
      else []
    unless required.all visited.contains do
      throwError "model-interpretation proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelInterpretationAudit
