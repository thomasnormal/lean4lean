import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Structural
import Lean.Util.CollectAxioms

namespace ModelTelescopesTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open scoped Lean4Lean.VEnv.Model

def one : VLevel := .succ .zero
def two : VLevel := .succ one
def three : VLevel := .succ two
def altZero : VLevel := .max .zero .zero
def oneF : List Nat → Nat := fun _ => 1
def twoF : List Nat → Nat := fun _ => 2
def tag : Ob := .sort zeroF
def typeTag : Ob := .sort oneF

theorem zeroEq : VLevel.zero ≈ altZero :=
  VLevel.equiv_def.2 fun _ => by simp [altZero, VLevel.eval]

theorem distinctLevels : VLevel.zero ≠ altZero := by intro h; cases h

def betaType : VExpr := .app (.lam (.sort two) (.bvar 0)) (.sort one)

theorem betaEquality : VEnv.empty.IsDefEq 0 [] betaType (.sort one) (.sort two) :=
  .beta (.bvar .zero) (HasType.sort (by trivial))

theorem distinctRepresentatives : betaType ≠ VExpr.sort one := by intro h; cases h

def D1 : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort two)
def c1 : VExpr → Prop := ElCls VEnv.empty 0 [] D1 (.sort one)
def D2 : VExpr → Prop := TyCls VEnv.empty 0 [] betaType
def c2 : VExpr → Prop := ElCls VEnv.empty 0 [] D2 (.sort .zero)

theorem c1Typed : TypedElCls VEnv.empty 0 [] D1 c1 :=
  .of_hasType (HasType.sort (by trivial))

theorem betaMember : c1 betaType := .mem_of_defeq betaEquality.symm

theorem c2Typed : TypedElCls VEnv.empty 0 [] D2 c2 :=
  .of_hasType (.defeqDF betaEquality.symm (HasType.sort (by trivial)))

theorem sortBacked (l : List Nat → Nat) : Backed (listSet [.sort l]) := by
  intro o ho w hw
  cases List.mem_singleton.1 ho
  cases hw

def k1 : Key := (D1, c1, [typeTag])
def k2 : Key := (D2, c2, [tag])
def keys : List Key := [k1, k2]
def doms : List VExpr := [.sort two, .bvar 0]
def endType : VExpr := .bvar 1
def piType : VExpr := .wrapForalls doms endType
def lambdaTerm : VExpr := .wrapLams doms (.bvar 0)
def σ1 : VExpr.Subst := VExpr.Subst.id.cons betaType
def σ2 : VExpr.Subst := σ1.cons (.sort .zero)
def S1 : ObSets := ObSets.empty.cons (listSet [typeTag])
def S2 : ObSets := S1.cons (listSet [tag])
def cv : VExpr → Prop := vcls VEnv.empty 0 [] .id lambdaTerm piType

theorem lambdaTyped : VEnv.empty.HasType 0 [] lambdaTerm piType :=
  .lamDF (HasType.sort (by trivial)) (.lamDF (.bvar .zero) (.bvar .zero))

theorem firstKeyTyped : ∀ k ∈ [typeTag], TypedAt VEnv.empty 0 [] c1 .id .empty (.sort two) k := by
  intro k hk
  cases List.mem_singleton.1 hk
  exact ⟨[.sort twoF], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort, .sort (.head _)⟩

theorem secondDomainObserved : ∀ τ ∈ [typeTag], Obs VEnv.empty 0 [] σ1 S1 (.bvar 0) τ := by
  intro τ hτ
  exact .bvar hτ

theorem secondKeyTyped : ∀ k ∈ [tag], TypedAt VEnv.empty 0 [] c2 σ1 S1 (.bvar 0) k := by
  intro k hk
  cases List.mem_singleton.1 hk
  exact ⟨[typeTag], secondDomainObserved, .sort (.head _)⟩

theorem telescopeKeys : TeleKeys VEnv.empty 0 [] .id .empty doms keys σ2 S2 :=
  .cons c1Typed betaMember firstKeyTyped (sortBacked oneF)
    (.cons c2Typed ElCls.self secondKeyTyped (sortBacked zeroF) .nil)

theorem twoKeys : keys.length = doms.length := telescopeKeys.length

theorem lambdaObserved : Obs VEnv.empty 0 [] .id .empty lambdaTerm (wrap keys tag) :=
  Obs.wrapLams_iff.2 ⟨keys, σ2, S2, tag, telescopeKeys, rfl, .bvar (.head _)⟩

theorem telescopeCodomain : Obs VEnv.empty 0 [] .id .empty piType (piCodChain keys typeTag) :=
  tele_obs telescopeKeys (.bvar (.head _))

theorem codomainObserved : ∀ τ ∈ [typeTag], Obs VEnv.empty 0 [] σ2 S2 endType τ := by
  intro τ hτ
  exact .bvar hτ

-- Construction uses both dependent domains and actual typed argument classes.
theorem wrappedTyped : ∃ τs : List Ob,
    (∀ τ ∈ τs, Obs VEnv.empty 0 [] .id .empty piType τ) ∧
    TypedOb VEnv.empty 0 [] cv (wrap keys tag) τs := by
  obtain ⟨τinner, hinner, inner⟩ := pi_list (env := VEnv.empty) (U := 0) (Δ := [])
    (σ := σ1) (S := S1) (A := .bvar 0) (B := endType) (K := [tag]) (τk := [typeTag])
    (τc := [typeTag]) c2Typed ElCls.self secondDomainObserved
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort (.head _))
    (sortBacked zeroF) codomainObserved
  obtain ⟨τouter, houter, outer⟩ := pi_list (env := VEnv.empty) (U := 0) (Δ := [])
    (σ := .id) (S := .empty) (A := .sort two) (B := .forallE (.bvar 0) endType)
    (K := [typeTag]) (τk := [.sort twoF]) (τc := τinner) c1Typed betaMember
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort)
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort (.head _))
    (sortBacked oneF) hinner
  exact ⟨τouter, houter, outer cv _ (inner _ tag (.sort (.head _)))⟩

theorem domainSD : SD VEnv.empty 0 [] [.sort two] (.bvar 0) (.bvar 0) (.sort two) :=
  SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl)

theorem bodySD : SD VEnv.empty 0 [] [.bvar 0, .sort two] endType endType (.sort two) :=
  SD.bvar (.succ .zero) (by trivial) (SD.sort (by trivial) (by trivial) rfl)

theorem innerPiSD : SD VEnv.empty 0 [] [.sort two]
    (.forallE (.bvar 0) endType) (.forallE (.bvar 0) endType) (.sort (.imax two two)) :=
  SD.forallE .empty (by trivial) (by trivial) (by trivial) domainSD bodySD

theorem telescopeSD : PiSD VEnv.empty 0 [] [] doms endType :=
  .cons (SD.sort (by trivial) (by trivial) rfl) innerPiSD (.cons domainSD bodySD .nil)

-- Unwinding consumes proved codomain soundness; no soundness certificate is assumed.
theorem unwound : ∃ σ' S', TeleKeys VEnv.empty 0 [] .id .empty doms keys σ' S' ∧
    ∃ τc cv', (∀ τ ∈ τc, Obs VEnv.empty 0 [] σ' S' endType τ) ∧
      TypedOb VEnv.empty 0 [] cv' tag τc := by
  obtain ⟨τs, hτ, htyped⟩ := wrappedTyped
  exact tele_unwind .empty (by trivial) telescopeSD .nil TV.empty twoKeys htyped hτ

-- The input observations use betaType; the output reads the dependent codomain
-- at the syntactically different member Type, proved equal by beta reduction.
theorem changeRepresentative : ∃ τc,
    (∀ τ ∈ τc, Obs VEnv.empty 0 [] (VExpr.Subst.id.cons (.sort one)) S1
      (.forallE (.bvar 0) endType) τ) ∧
    TypedOb VEnv.empty 0 []
      (appCls VEnv.empty 0 [] cv c1
        (TyCls VEnv.empty 0 [] ((VExpr.forallE (.bvar 0) endType).subst
          (VExpr.Subst.id.cons (.sort one))))) (wrap [k2] tag) τc := by
  obtain ⟨τs, hτ, htyped⟩ := wrappedTyped
  have result := pi_step .empty (by trivial) (HasType.sort (by trivial))
    innerPiSD.1.defeq innerPiSD.2 (show Ctx.SubstEq VEnv.empty 0 [] .id .id [] from .nil)
    (show TV VEnv.empty 0 [] [] .id .empty from TV.empty) htyped hτ
    (show c1 (.sort one) from ElCls.self)
  exact result.2.2.2.2

-- Equivalent, syntactically different level instances of a checked definition.
def polyName : Name := Name.mkSimple "ObservedUniverse"
def polyValue : VDefVal := ⟨⟨⟨1, .sort (.succ (.param 0))⟩, polyName⟩, .sort (.param 0)⟩
def polyBase : VEnv := {
  constants n := if polyName = n then some polyValue.toVConstant else none
  defeqs _ := False }
def polyEnv : VEnv := polyBase.addDefEq polyValue.toDefEq

theorem polyEnvironmentWF : polyEnv.WF := by
  refine ⟨_, .decl (.def (ci := polyValue) ?_ ?_) .empty⟩
  · exact .sort (by decide)
  · rfl

theorem polyObserved : Obs polyEnv 0 [] .id .empty (.const polyName [.zero]) tag := by
  refine .delta (df := polyValue.toDefEq) (ci := polyValue.toVConstant)
    (τs := [typeTag]) (.inl rfl) rfl ?_ ?_ (.sort (.head _)) .sort
  · simp [polyEnv, VEnv.addDefEq, polyBase]
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort

theorem polyTransferred (σ : VExpr.Subst) (S : ObSets) :
    Obs polyEnv 0 [] σ S (.const polyName [altZero]) tag := by
  exact polyObserved.const_levels (by simp [VLevel.WF])
    (by simp [altZero, VLevel.WF]) (.cons zeroEq .nil)

theorem equivalentLambda : LvEq 0 (VExpr.lam (.sort one) (.sort .zero))
    (.lam (.sort (.succ altZero)) (.sort altZero)) :=
  .lam (.sort (by trivial) (by simp [VLevel.WF, altZero]) (VLevel.succ_congr zeroEq))
    (.sort (by trivial) (by simp [VLevel.WF, altZero]) zeroEq)

theorem lambdaLevelInvariant : Obs VEnv.empty 0 [] σ S
    (.lam (.sort one) (.sort .zero)) o ↔
    Obs VEnv.empty 0 [] σ S (.lam (.sort (.succ altZero)) (.sort altZero)) o :=
  Obs.lvEq_iff equivalentLambda

theorem sortSound : SoundAt VEnv.empty 0 [] [] (.sort .zero) (.sort altZero) (.sort one) :=
  SoundAt.sort zeroEq

theorem variableSound : SoundAt VEnv.empty 0 [] [.sort two] (.bvar 0) (.bvar 0) (.sort two) :=
  SoundAt.bvar .zero

theorem soundComposition : SoundAt VEnv.empty 0 [] [] (.sort .zero) (.sort .zero) (.sort one) :=
  sortSound.trans .empty (by trivial) (sortSound.symm .empty (by trivial))

def bindingD : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort one)
def bindingClass : VExpr → Prop := ElCls VEnv.empty 0 [] bindingD (.sort .zero)

theorem bindingClassTyped : TypedElCls VEnv.empty 0 [] bindingD bindingClass :=
  .of_hasType (HasType.sort (by trivial))

theorem storedBinding : RuleBind VEnv.empty 0 [] [.sort (.succ (.param 0))] [.zero]
    [.bvar 0] 0 [] false [(bindingD, bindingClass, [tag])] []
    (fun _ => .sort .zero) (fun _ => listSet [tag]) := by
  refine ⟨fun _ => sortBacked zeroF, fun x hx => ?_⟩
  have : x = 0 := by simpa using hx
  subst x
  refine .inl ⟨0, (bindingD, bindingClass, [tag]), rfl, ?_, rfl,
    bindingClassTyped, ElCls.self, rfl⟩
  intro j hj; omega

theorem bindingTransferred : RuleBind VEnv.empty 0 [] [.sort (.succ (.param 0))] [altZero]
    [.bvar 0] 0 [] false [(bindingD, bindingClass, [tag])] []
    (fun _ => .sort .zero) (fun _ => listSet [tag]) :=
  storedBinding.lvEq (by simp [VLevel.WF]) (by simp [VLevel.WF, altZero]) (.cons zeroEq .nil)

theorem lambdaBeforeLevels : Obs VEnv.empty 0 [] .id .empty
    (.lam (.sort one) (.sort .zero)) (.app bindingD bindingClass [] tag) :=
  .lam (τs := []) (x := .sort .zero) bindingClassTyped nofun nofun
    (fun _ h => nomatch h) ElCls.self .sort

theorem lambdaAfterLevels : Obs VEnv.empty 0 [] .id .empty
    (.lam (.sort (.succ altZero)) (.sort altZero)) (.app bindingD bindingClass [] tag) :=
  lambdaLevelInvariant.1 lambdaBeforeLevels

theorem observationTypingTransferred : TypedAt VEnv.empty 0 [] bindingClass .id .empty
    (.sort (.succ altZero)) tag :=
  (show TypedAt VEnv.empty 0 [] bindingClass .id .empty (.sort one) tag from
    ⟨[typeTag], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort, .sort (.head _)⟩).lvEq
      (.sort (by trivial) (by simp [VLevel.WF, altZero]) (VLevel.succ_congr zeroEq))

theorem nonreflexivePiSound : SoundAt VEnv.empty 0 [] []
    (.forallE (.sort .zero) (.sort .zero)) (.forallE (.sort altZero) (.sort .zero))
    (.sort (.imax one one)) :=
  SoundAt.forallEDF .empty (by trivial)
    (.sortDF (by trivial) (by simp [VLevel.WF, altZero]) zeroEq)
    (.sortDF (by trivial) (by trivial) rfl) (SoundAt.sort zeroEq) (SoundAt.sort rfl)

theorem propositionPiSD : SD VEnv.empty 0 [] []
    (.forallE (.sort .zero) (.bvar 0)) (.forallE (.sort .zero) (.bvar 0))
    (.sort (.imax one .zero)) :=
  SD.forallE .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl)
    (SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl))

theorem betaObserved : Obs VEnv.empty 0 [] .id .empty betaType typeTag := by
  have function : Obs VEnv.empty 0 [] .id .empty
      (.lam (.sort two) (.bvar 0)) (.app D1 c1 [typeTag] typeTag) := by
    refine .lam (τs := [.sort twoF]) (x := .sort one) c1Typed ?_ ?_
      (sortBacked oneF) ElCls.self (.bvar (.head _))
    · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort
    · intro k hk; cases List.mem_singleton.1 hk; exact .sort (.head _)
  exact .app function rfl (K' := [typeTag])
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort) .refl

theorem spineTyped : VEnv.empty.HasType 0 []
    (VExpr.mkApps lambdaTerm [betaType, .sort .zero]) betaType :=
  .appDF (.appDF lambdaTyped betaEquality.hasType.1)
    (.defeqDF betaEquality.symm (HasType.sort (by trivial)))

theorem actualSpine : Obs VEnv.empty 0 [] .id .empty
    (VExpr.mkApps lambdaTerm [betaType, .sort .zero]) tag := by
  apply obs_mkApps_of_wrap (keys := keys) (args := [betaType, .sort .zero]) _ lambdaObserved
  refine .cons ⟨?_, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)
  · exact (ElCls.eq_of_mem betaMember).symm
  · intro x hx; cases List.mem_singleton.1 hx; exact betaObserved
  · intro x hx; cases List.mem_singleton.1 hx; exact .sort

theorem recoveredHead : ∃ ks : List Key,
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls VEnv.empty 0 [] k.1 (a.subst .id))
      ks [betaType, .sort .zero] ∧ Obs VEnv.empty 0 [] .id .empty lambdaTerm (wrap ks tag) :=
  wrap_of_obs_mkApps actualSpine

end ModelTelescopesTest

namespace ModelTelescopesAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.map_eval_eq,
    `Lean4Lean.VEnv.Model.RuleBind.lvEq,
    `Lean4Lean.VEnv.Model.constCls_lvEq,
    `Lean4Lean.VEnv.Model.Obs.lvEq,
    `Lean4Lean.VEnv.Model.Obs.lvEq_iff,
    `Lean4Lean.VEnv.Model.Obs.const_levels,
    `Lean4Lean.VEnv.Model.TypedAt.lvEq,
    `Lean4Lean.VExpr.wrapForalls,
    `Lean4Lean.VExpr.mkApps_snoc,
    `Lean4Lean.VEnv.Model.SoundAt,
    `Lean4Lean.VEnv.Model.SD,
    `Lean4Lean.VEnv.Model.TeleKeys,
    `Lean4Lean.VEnv.Model.PiSD,
    `Lean4Lean.VEnv.Model.TeleKeys.length,
    `Lean4Lean.VEnv.Model.mkApps_inv,
    `Lean4Lean.VEnv.Model.mkApps_const_inv,
    `Lean4Lean.VEnv.Model.obs_mkApps_of_wrap,
    `Lean4Lean.VEnv.Model.wrap_of_obs_mkApps,
    `Lean4Lean.VEnv.Model.typedAt_sort_iff,
    `Lean4Lean.VEnv.Model.pi_list,
    `Lean4Lean.VEnv.Model.tele_obs,
    `Lean4Lean.VEnv.Model.Obs.wrapLams_iff,
    `Lean4Lean.VEnv.Model.TV.cons_cls,
    `Lean4Lean.VEnv.Model.pi_step,
    `Lean4Lean.VEnv.Model.tele_unwind,
    `Lean4Lean.VEnv.Model.SoundAt.bvar,
    `Lean4Lean.VEnv.Model.SoundAt.sort,
    `Lean4Lean.VEnv.Model.SD.sort,
    `Lean4Lean.VEnv.Model.SoundAt.symm,
    `Lean4Lean.VEnv.Model.SoundAt.trans,
    `Lean4Lean.VEnv.Model.imax_eval_zero,
    `Lean4Lean.VEnv.Model.SD.bvar,
    `Lean4Lean.VEnv.Model.keys_transfer,
    `Lean4Lean.VEnv.Model.keys_transfer_symm,
    `Lean4Lean.VEnv.Model.SoundAt.forallEDF,
    `Lean4Lean.VEnv.Model.SD.forallE,
    `ModelTelescopesTest.one,
    `ModelTelescopesTest.two,
    `ModelTelescopesTest.three,
    `ModelTelescopesTest.altZero,
    `ModelTelescopesTest.oneF,
    `ModelTelescopesTest.twoF,
    `ModelTelescopesTest.tag,
    `ModelTelescopesTest.typeTag,
    `ModelTelescopesTest.zeroEq,
    `ModelTelescopesTest.distinctLevels,
    `ModelTelescopesTest.betaType,
    `ModelTelescopesTest.betaEquality,
    `ModelTelescopesTest.distinctRepresentatives,
    `ModelTelescopesTest.D1,
    `ModelTelescopesTest.c1,
    `ModelTelescopesTest.D2,
    `ModelTelescopesTest.c2,
    `ModelTelescopesTest.c1Typed,
    `ModelTelescopesTest.betaMember,
    `ModelTelescopesTest.c2Typed,
    `ModelTelescopesTest.sortBacked,
    `ModelTelescopesTest.k1,
    `ModelTelescopesTest.k2,
    `ModelTelescopesTest.keys,
    `ModelTelescopesTest.doms,
    `ModelTelescopesTest.endType,
    `ModelTelescopesTest.piType,
    `ModelTelescopesTest.lambdaTerm,
    `ModelTelescopesTest.σ1,
    `ModelTelescopesTest.σ2,
    `ModelTelescopesTest.S1,
    `ModelTelescopesTest.S2,
    `ModelTelescopesTest.cv,
    `ModelTelescopesTest.lambdaTyped,
    `ModelTelescopesTest.firstKeyTyped,
    `ModelTelescopesTest.secondDomainObserved,
    `ModelTelescopesTest.secondKeyTyped,
    `ModelTelescopesTest.telescopeKeys,
    `ModelTelescopesTest.twoKeys,
    `ModelTelescopesTest.lambdaObserved,
    `ModelTelescopesTest.telescopeCodomain,
    `ModelTelescopesTest.codomainObserved,
    `ModelTelescopesTest.wrappedTyped,
    `ModelTelescopesTest.domainSD,
    `ModelTelescopesTest.bodySD,
    `ModelTelescopesTest.innerPiSD,
    `ModelTelescopesTest.telescopeSD,
    `ModelTelescopesTest.unwound,
    `ModelTelescopesTest.changeRepresentative,
    `ModelTelescopesTest.polyName,
    `ModelTelescopesTest.polyValue,
    `ModelTelescopesTest.polyBase,
    `ModelTelescopesTest.polyEnv,
    `ModelTelescopesTest.polyEnvironmentWF,
    `ModelTelescopesTest.polyObserved,
    `ModelTelescopesTest.polyTransferred,
    `ModelTelescopesTest.equivalentLambda,
    `ModelTelescopesTest.lambdaLevelInvariant,
    `ModelTelescopesTest.sortSound,
    `ModelTelescopesTest.variableSound,
    `ModelTelescopesTest.soundComposition,
    `ModelTelescopesTest.bindingD,
    `ModelTelescopesTest.bindingClass,
    `ModelTelescopesTest.bindingClassTyped,
    `ModelTelescopesTest.storedBinding,
    `ModelTelescopesTest.bindingTransferred,
    `ModelTelescopesTest.lambdaBeforeLevels,
    `ModelTelescopesTest.lambdaAfterLevels,
    `ModelTelescopesTest.observationTypingTransferred,
    `ModelTelescopesTest.nonreflexivePiSound,
    `ModelTelescopesTest.propositionPiSD,
    `ModelTelescopesTest.betaObserved,
    `ModelTelescopesTest.spineTyped,
    `ModelTelescopesTest.actualSpine,
    `ModelTelescopesTest.recoveredHead,
    `Lean4Lean.VEnv.Model.TeleKeys.nil,
    `Lean4Lean.VEnv.Model.TeleKeys.cons,
    `Lean4Lean.VEnv.Model.PiSD.nil,
    `Lean4Lean.VEnv.Model.PiSD.cons]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.map_eval_eq, [`propext]),
    (`Lean4Lean.VEnv.Model.RuleBind.lvEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.constCls_lvEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lvEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.lvEq_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.const_levels, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.lvEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.wrapForalls, []),
    (`Lean4Lean.VExpr.mkApps_snoc, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.PiSD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.length, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mkApps_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mkApps_const_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.obs_mkApps_of_wrap, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrap_of_obs_mkApps, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.typedAt_sort_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pi_list, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_obs, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Obs.wrapLams_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.cons_cls, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pi_step, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_unwind, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.sort, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.sort, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.symm, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.trans, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.imax_eval_zero, [`propext]),
    (`Lean4Lean.VEnv.Model.SD.bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.keys_transfer, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.keys_transfer_symm, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.forallEDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.forallE, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.one, []),
    (`ModelTelescopesTest.two, []),
    (`ModelTelescopesTest.three, []),
    (`ModelTelescopesTest.altZero, []),
    (`ModelTelescopesTest.oneF, []),
    (`ModelTelescopesTest.twoF, []),
    (`ModelTelescopesTest.tag, []),
    (`ModelTelescopesTest.typeTag, []),
    (`ModelTelescopesTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.distinctLevels, []),
    (`ModelTelescopesTest.betaType, []),
    (`ModelTelescopesTest.betaEquality, [`propext]),
    (`ModelTelescopesTest.distinctRepresentatives, []),
    (`ModelTelescopesTest.D1, [`propext]),
    (`ModelTelescopesTest.c1, [`propext]),
    (`ModelTelescopesTest.D2, [`propext]),
    (`ModelTelescopesTest.c2, [`propext]),
    (`ModelTelescopesTest.c1Typed, [`propext]),
    (`ModelTelescopesTest.betaMember, [`propext]),
    (`ModelTelescopesTest.c2Typed, [`propext]),
    (`ModelTelescopesTest.sortBacked, [`propext]),
    (`ModelTelescopesTest.k1, [`propext]),
    (`ModelTelescopesTest.k2, [`propext]),
    (`ModelTelescopesTest.keys, [`propext]),
    (`ModelTelescopesTest.doms, []),
    (`ModelTelescopesTest.endType, []),
    (`ModelTelescopesTest.piType, []),
    (`ModelTelescopesTest.lambdaTerm, []),
    (`ModelTelescopesTest.σ1, []),
    (`ModelTelescopesTest.σ2, []),
    (`ModelTelescopesTest.S1, []),
    (`ModelTelescopesTest.S2, []),
    (`ModelTelescopesTest.cv, [`propext]),
    (`ModelTelescopesTest.lambdaTyped, [`propext]),
    (`ModelTelescopesTest.firstKeyTyped, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.secondDomainObserved, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.secondKeyTyped, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.telescopeKeys, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.twoKeys, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.lambdaObserved, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.telescopeCodomain, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.codomainObserved, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.wrappedTyped, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.domainSD, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.bodySD, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.telescopeSD, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.unwound, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.changeRepresentative, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.polyName, []),
    (`ModelTelescopesTest.polyValue, []),
    (`ModelTelescopesTest.polyBase, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.polyEnv, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.polyEnvironmentWF, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.polyObserved, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.polyTransferred, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.equivalentLambda, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.lambdaLevelInvariant, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.sortSound, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.variableSound, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.soundComposition, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.bindingD, [`propext]),
    (`ModelTelescopesTest.bindingClass, [`propext]),
    (`ModelTelescopesTest.bindingClassTyped, [`propext]),
    (`ModelTelescopesTest.storedBinding, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.bindingTransferred, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.lambdaBeforeLevels, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.lambdaAfterLevels, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.observationTypingTransferred, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.nonreflexivePiSound, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.propositionPiSD, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.spineTyped, [`propext]),
    (`ModelTelescopesTest.actualSpine, [`Quot.sound, `propext]),
    (`ModelTelescopesTest.recoveredHead, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.nil, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.cons, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.PiSD.nil, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.PiSD.cons, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-telescope manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-telescope manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-telescope axiom {root}"
    if let some proof := info.value? (allowOpaque := true) then
      if proof.hasSorry then throwError "direct model-telescope admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-telescope value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-telescope dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-telescope type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then throwError "model-telescope admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-telescope dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-telescope traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-telescope axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.Obs.lvEq then [`Lean4Lean.VEnv.Model.RuleBind.lvEq, `Lean4Lean.VEnv.Model.constCls_lvEq, `Lean4Lean.VEnv.Model.map_eval_eq, `Lean4Lean.VEnv.Model.LvEq.instL, `Lean4Lean.VEnv.Model.Obs.rule, `Lean4Lean.VEnv.Model.Obs.delta]
      else if root == `Lean4Lean.VEnv.Model.RuleBind.lvEq then [`Lean4Lean.VEnv.Model.TyCls.eq_of_lvEq, `Lean4Lean.VEnv.Model.LvEq.instL, `Lean4Lean.VEnv.Model.LvEq.subst, `Lean4Lean.VEnv.Model.RuleBind, `Lean4Lean.VEnv.Model.binderTy]
      else if root == `Lean4Lean.VEnv.Model.Obs.const_levels then [`Lean4Lean.VEnv.Model.Obs.const_indep, `Lean4Lean.VEnv.Model.Obs.lvEq]
      else if root == `Lean4Lean.VEnv.Model.TeleKeys then [`Lean4Lean.VEnv.Model.TypedAt, `Lean4Lean.VEnv.Model.TypedElCls, `Lean4Lean.VEnv.Model.Backed, `Lean4Lean.VEnv.Model.TyCls, `Lean4Lean.VEnv.Model.ObSets.cons]
      else if root == `Lean4Lean.VEnv.Model.PiSD then [`Lean4Lean.VEnv.Model.SD, `Lean4Lean.VEnv.Model.SoundAt, `Lean4Lean.VEnv.IsDefEqStrong]
      else if root == `Lean4Lean.VEnv.Model.pi_list then [`Lean4Lean.VEnv.Model.TypedOb.app, `Lean4Lean.VEnv.Model.Obs.piCodOb, `Lean4Lean.VEnv.Model.TypedElCls]
      else if root == `Lean4Lean.VEnv.Model.Obs.wrapLams_iff then [`Lean4Lean.VEnv.Model.TeleKeys, `Lean4Lean.VEnv.Model.Obs.lam_iff, `Lean4Lean.VEnv.Model.TypedAt.merge]
      else if root == `Lean4Lean.VEnv.Model.pi_step then [`Lean4Lean.VEnv.Model.TypedElCls.defeq, `Lean4Lean.VEnv.Model.TyCls.eq_of_defeq, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.TypedOb.strengthen, `Lean4Lean.VEnv.Model.Obs.mono_le, `Lean4Lean.VEnv.Model.TV.cons_cls]
      else if root == `Lean4Lean.VEnv.Model.tele_unwind then [`Lean4Lean.VEnv.Model.pi_step, `Lean4Lean.VEnv.Model.TypedElCls.nonempty, `Lean4Lean.VEnv.Model.TeleKeys.cons]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.forallEDF then [`Lean4Lean.VEnv.Model.keys_transfer, `Lean4Lean.VEnv.Model.keys_transfer_symm, `Lean4Lean.VEnv.Model.imax_eval_zero, `Lean4Lean.VEnv.Model.TypedOb.piCodOb, `Lean4Lean.VEnv.Model.TV.cons_cls, `Lean4Lean.VEnv.Model.TyCls.eq_of_defeq, `Lean4Lean.VEnv.Model.Covers.indices]
      else if root == `Lean4Lean.VEnv.Model.SD.forallE then [`Lean4Lean.VEnv.Model.SoundAt.forallEDF, `Lean4Lean.VEnv.IsDefEqStrong.forallEDF]
      else if root == `Lean4Lean.VEnv.Model.SD.bvar then [`Lean4Lean.VEnv.Model.SoundAt.bvar, `Lean4Lean.VEnv.IsDefEqStrong.bvar]
      else if root == `Lean4Lean.VEnv.Model.SD.sort then [`Lean4Lean.VEnv.Model.SoundAt.sort, `Lean4Lean.VEnv.IsDefEqStrong.sortDF]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.symm then [`Lean4Lean.VEnv.Model.SubstEq.symm]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.trans then [`Lean4Lean.VEnv.Model.Ob.Sub.trans, `Lean4Lean.VEnv.Model.SubstEq.right]
      else if root == `ModelTelescopesTest.telescopeKeys then [`ModelTelescopesTest.betaMember, `ModelTelescopesTest.c2Typed, `ModelTelescopesTest.firstKeyTyped, `ModelTelescopesTest.secondKeyTyped]
      else if root == `ModelTelescopesTest.wrappedTyped then [`Lean4Lean.VEnv.Model.pi_list, `ModelTelescopesTest.c1Typed, `ModelTelescopesTest.c2Typed]
      else if root == `ModelTelescopesTest.unwound then [`Lean4Lean.VEnv.Model.tele_unwind, `ModelTelescopesTest.wrappedTyped, `ModelTelescopesTest.telescopeSD]
      else if root == `ModelTelescopesTest.changeRepresentative then [`Lean4Lean.VEnv.Model.pi_step, `ModelTelescopesTest.innerPiSD, `ModelTelescopesTest.wrappedTyped, `ModelTelescopesTest.betaEquality]
      else if root == `ModelTelescopesTest.innerPiSD then [`Lean4Lean.VEnv.Model.SD.forallE, `ModelTelescopesTest.domainSD, `ModelTelescopesTest.bodySD]
      else if root == `ModelTelescopesTest.nonreflexivePiSound then [`Lean4Lean.VEnv.Model.SoundAt.forallEDF, `ModelTelescopesTest.zeroEq]
      else if root == `ModelTelescopesTest.propositionPiSD then [`Lean4Lean.VEnv.Model.SD.forallE, `Lean4Lean.VEnv.Model.imax_eval_zero]
      else if root == `ModelTelescopesTest.polyTransferred then [`Lean4Lean.VEnv.Model.Obs.const_levels, `ModelTelescopesTest.polyObserved, `ModelTelescopesTest.zeroEq]
      else if root == `ModelTelescopesTest.polyEnvironmentWF then [`Lean4Lean.VDecl.WF.def, `Lean4Lean.VEnv.HasType.sort]
      else if root == `ModelTelescopesTest.bindingTransferred then [`Lean4Lean.VEnv.Model.RuleBind.lvEq, `ModelTelescopesTest.storedBinding, `ModelTelescopesTest.zeroEq]
      else if root == `ModelTelescopesTest.observationTypingTransferred then [`Lean4Lean.VEnv.Model.TypedAt.lvEq, `ModelTelescopesTest.zeroEq]
      else if root == `ModelTelescopesTest.lambdaAfterLevels then [`Lean4Lean.VEnv.Model.Obs.lvEq_iff, `ModelTelescopesTest.lambdaBeforeLevels]
      else if root == `ModelTelescopesTest.actualSpine then [`Lean4Lean.VEnv.Model.obs_mkApps_of_wrap, `Lean4Lean.VEnv.Model.ElCls.eq_of_mem, `ModelTelescopesTest.betaMember, `ModelTelescopesTest.betaObserved, `ModelTelescopesTest.lambdaObserved]
      else if root == `ModelTelescopesTest.spineTyped then [`ModelTelescopesTest.lambdaTyped, `ModelTelescopesTest.betaEquality]
      else if root == `ModelTelescopesTest.recoveredHead then [`Lean4Lean.VEnv.Model.wrap_of_obs_mkApps, `ModelTelescopesTest.actualSpine]
      else []
    unless required.all visited.contains do
      throwError "model-telescope proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelTelescopesAudit
