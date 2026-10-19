import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Sound
import Lean.Util.CollectAxioms

namespace ModelSpinesTest
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

theorem piTypeSD : SD VEnv.empty 0 [] [] piType piType
    (.sort (.imax three (.imax two two))) :=
  SD.forallE .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) innerPiSD

theorem lambdaSD : SD VEnv.empty 0 [] [] lambdaTerm lambdaTerm piType :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) innerPiSD innerPiSD
    (SD.lamDF .empty (by trivial) (by trivial) (by trivial) domainSD bodySD bodySD
      (SD.bvar .zero (by trivial) bodySD) (SD.bvar .zero (by trivial) bodySD))
    (SD.lamDF .empty (by trivial) (by trivial) (by trivial) domainSD bodySD bodySD
      (SD.bvar .zero (by trivial) bodySD) (SD.bvar .zero (by trivial) bodySD))

theorem lambdaHTS : HTS VEnv.empty 0 [] [] lambdaTerm piType :=
  (sound_no_rules .empty (by trivial) VEnv.LE.rfl (fun _ h => h.elim) lambdaSD.1).2.1

theorem piTypeHTS : HTS VEnv.empty 0 [] [] piType (.sort (.imax three (.imax two two))) :=
  (sound_no_rules .empty (by trivial) VEnv.LE.rfl (fun _ h => h.elim) piTypeSD.1).2.1

theorem derivedPiSoundness : PiSD VEnv.empty 0 [] [] doms endType :=
  piTypeHTS.piSD

theorem extendedTyped : Ctx.SubstEq VEnv.empty 0 [] σ2 σ2 doms.reverse ∧
    TV VEnv.empty 0 [] doms.reverse σ2 S2 :=
  telescopeKeys.typed .empty (by trivial) derivedPiSoundness.doms .nil TV.empty

-- Nonreflexive conversion of the telescope's supplied type.
def typeLevel : VLevel := .imax three (.imax two two)
def delayedPi : VExpr := .app (.lam (.sort typeLevel) (.bvar 0)) piType

theorem delayStrong : VEnv.empty.IsDefEqStrong 0 [] delayedPi piType (.sort typeLevel) :=
  .beta (by trivial) (by trivial)
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)
    (.bvar .zero (by trivial) (.sortDF (by trivial) (by trivial) rfl)) piTypeSD.1
    (.sortDF (by trivial) (by trivial) rfl) piTypeSD.1

theorem convertedLambdaStrong : VEnv.empty.IsDefEqStrong 0 [] lambdaTerm lambdaTerm delayedPi :=
  .defeqDF (by trivial) delayStrong.symm lambdaSD.1

theorem convertedLambdaSound : SoundAt VEnv.empty 0 [] [] lambdaTerm lambdaTerm delayedPi ∧
    HTS VEnv.empty 0 [] [] lambdaTerm delayedPi := by
  have h := sound_no_rules (Δ := []) .empty (by trivial) VEnv.LE.rfl (fun _ h => h.elim) convertedLambdaStrong
  exact ⟨h.1, h.2.1⟩

theorem lambdaThroughConversion : ∃ T', HTS VEnv.empty 0 [] doms.reverse (.bvar 0) T' ∧
    DomsSD VEnv.empty 0 [] [] doms ∧
    ∃ τc, (∀ τ ∈ τc, Obs VEnv.empty 0 [] σ2 S2 T' τ) ∧
      TypedOb VEnv.empty 0 [] (vcls VEnv.empty 0 [] σ2 (.bvar 0) T') tag τc := by
  obtain ⟨τs, hτs, htyped⟩ :=
    (convertedLambdaSound.1 .id .id .empty .nil TV.empty TV.empty).2.2.1 _ lambdaObserved
  exact convertedLambdaSound.2.lamSpine .empty (by trivial) rfl .nil TV.empty
    telescopeKeys hτs htyped

theorem distinctPiTypes : delayedPi ≠ piType := by intro h; cases h

-- A checked declaration with an actual dependent constant type and no equations.
def constName : Name := Name.mkSimple "DependentSpine"
def constValue : VConstVal := ⟨⟨0, piType⟩, constName⟩
def constEnv : VEnv := {
  constants n := if constName = n then some constValue.toVConstant else none
  defeqs _ := False }

theorem constEnvWF : constEnv.WF :=
  ⟨_, .decl (.axiom (ci := constValue) ⟨_, piTypeSD.1.defeq⟩ rfl) .empty⟩

theorem emptyLE : VEnv.empty ≤ constEnv := by
  refine ⟨?_, ?_⟩
  · intro c ci h; cases h
  · intro df h; exact h.elim

theorem noRules : ∀ df, ¬ constEnv.defeqs df := fun _ h => h

theorem constLookup : constEnv.constants constName = some constValue.toVConstant := by
  simp [constEnv]

theorem constantStrong : constEnv.IsDefEqStrong 0 [] (.const constName []) (.const constName []) piType :=
  .constDF constLookup nofun nofun rfl .nil (by trivial)
    (piTypeSD.1.mono emptyLE) (piTypeSD.1.mono emptyLE)

theorem betaStrong : VEnv.empty.IsDefEqStrong 0 Γ betaType (.sort one) (.sort two) :=
  .beta (by trivial) (by trivial)
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)
    (.bvar .zero (by trivial) (.sortDF (by trivial) (by trivial) rfl))
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)
    (.sortDF (by trivial) (by trivial) rfl)

theorem betaReflStrong : VEnv.empty.IsDefEqStrong 0 Γ betaType betaType (.sort two) :=
  betaStrong.trans betaStrong.symm

theorem resultPiStrong : VEnv.empty.IsDefEqStrong 0 Γ
    (.forallE betaType betaType) (.forallE betaType betaType) (.sort (.imax two two)) :=
  .forallEDF (by trivial) (by trivial) betaReflStrong betaReflStrong betaReflStrong

theorem firstApplicationStrong : constEnv.IsDefEqStrong 0 []
    (.app (.const constName []) betaType) (.app (.const constName []) betaType)
    (.forallE betaType betaType) :=
  .appDF (by trivial) (by trivial)
    (.sortDF (by trivial) (by trivial) rfl) (innerPiSD.1.mono emptyLE) constantStrong
    (betaReflStrong.mono emptyLE) (resultPiStrong.mono emptyLE)

def source : VExpr := .mkApps (.const constName []) [betaType, .sort .zero]

theorem sourceAtBeta : constEnv.IsDefEqStrong 0 [] source source betaType :=
  .appDF (by trivial) (by trivial) (betaReflStrong.mono emptyLE) (betaReflStrong.mono emptyLE)
    firstApplicationStrong
    (.defeqDF (by trivial) (betaStrong.symm.mono emptyLE) (.sortDF (by trivial) (by trivial) rfl))
    (betaReflStrong.mono emptyLE)

theorem sourceStrong : constEnv.IsDefEqStrong 0 [] source source (.sort one) :=
  .defeqDF (by trivial) (betaStrong.mono emptyLE) sourceAtBeta

theorem sourceSound : SoundAt constEnv 0 [] [] source source (.sort one) ∧
    HTS constEnv 0 [] [] source (.sort one) := by
  have h := sound_no_rules (Δ := []) constEnvWF.ordered (by trivial) VEnv.LE.rfl noRules sourceStrong
  exact ⟨h.1, h.2.1⟩

theorem betaObserved : Obs constEnv 0 [] .id .empty betaType typeTag := by
  have s := sound_no_rules (Δ := []) constEnvWF.ordered (by trivial) emptyLE
    (fun _ h => h.elim) (betaStrong (Γ := []))
  obtain ⟨o, ho, l⟩ := (s.1 .id .id .empty .nil TV.empty TV.empty).2.1 typeTag .sort
  cases l.sort_inv
  exact ho

def demands : List (List Ob) := [[typeTag, typeTag], [tag]]

theorem demandedArguments : List.Forall₂ (fun K a => ∀ x ∈ K, Obs constEnv 0 [] .id .empty a x)
    demands [betaType, .sort .zero] := by
  refine .cons ?_ (.cons ?_ .nil)
  · intro x hx
    have : x = typeTag := by simpa using hx
    subst x
    exact betaObserved
  · intro x hx; cases List.mem_singleton.1 hx; exact .sort

-- All three substantive parts of the spine result remain exposed.
theorem extracted : ∃ info : List (Key × VExpr),
    List.Forall₂ (KeyData constEnv 0 [] [] .id .empty) info [betaType, .sort .zero] ∧
    List.Forall₂ (fun K (ka : Key × VExpr) => ∀ x ∈ K, x ∈ ka.1.2.2) demands info ∧
    (∀ o, TypedOb constEnv 0 [] (vcls constEnv 0 [] .id source (.sort one)) o [typeTag] →
      ∃ τ₀, (∀ τ ∈ τ₀, Obs constEnv 0 [] .id .empty piType τ) ∧
        TypedOb constEnv 0 [] (ElCls constEnv 0 [] (TyCls constEnv 0 [] piType) (.const constName []))
          (wrap (info.map (·.1)) o) τ₀) ∧
    (∀ x, Obs constEnv 0 [] .id .empty piType (piCodChain (info.map (·.1)) x) →
      ∃ x', Obs constEnv 0 [] .id .empty (.sort one) x' ∧ x' ≼ x) ∧
    (∀ pre ka post, info = pre ++ ka :: post → ∀ x,
      Obs constEnv 0 [] .id .empty piType (piCodChain (pre.map (·.1)) (.piDomOb x)) →
      ∃ x', Obs constEnv 0 [] .id .empty ka.2 x' ∧ x' ≼ x) := by
  obtain ⟨ci, info, hci, _, _, hi, hd, P1, P2, dP2⟩ := sourceSound.2.spine constEnvWF.ordered
    (by trivial) rfl (show Ctx.SubstEq constEnv 0 [] .id .id [] from .nil)
    (show TV constEnv 0 [] [] .id .empty from TV.empty) demands demandedArguments
    [typeTag] (fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort)
  cases constLookup.symm.trans hci
  exact ⟨info, hi, hd, P1, P2, dP2⟩

-- P1 is consumed by unwinding its typed result; P2 then recovers the
-- supplied result observation, and dP2 recovers the first actual domain.
theorem spineRoundtrip : ∃ info : List (Key × VExpr),
    List.Forall₂ (KeyData constEnv 0 [] [] .id .empty) info [betaType, .sort .zero] ∧
    List.Forall₂ (fun K (ka : Key × VExpr) => ∀ x ∈ K, x ∈ ka.1.2.2) demands info ∧
    (∃ σ' S', TeleKeys constEnv 0 [] .id .empty doms (info.map (·.1)) σ' S' ∧
      Obs constEnv 0 [] σ' S' endType typeTag) ∧
    Obs constEnv 0 [] .id .empty (.sort one) typeTag ∧
    (∃ ka rest, info = ka :: rest ∧ Obs constEnv 0 [] .id .empty ka.2 (.sort twoF)) := by
  obtain ⟨info, hi, hd, P1, P2, dP2⟩ := extracted
  obtain ⟨τs, hτs, ht⟩ := P1 (.rigid constName [] 2 oneF) (.rigid (.head _))
  have storedHTS : HTS constEnv 0 [] [] piType (.sort typeLevel) :=
    (sound_no_rules constEnvWF.ordered (by trivial) emptyLE
      (fun _ h => h.elim) piTypeSD.1).2.1
  have hlen : (info.map (·.1)).length = doms.length := by
    simpa [doms] using hi.length_eq
  obtain ⟨σ', S', hkeys, τc, cv', hc, hrigid⟩ := tele_unwind constEnvWF.ordered
    (by trivial) storedHTS.piSD (show Ctx.SubstEq constEnv 0 [] .id .id [] from .nil)
    (show TV constEnv 0 [] [] .id .empty from TV.empty) hlen ht hτs
  have hend : Obs constEnv 0 [] σ' S' endType typeTag := by
    cases hrigid with | rigid hm => exact hc _ hm
  obtain ⟨x, hx, hle⟩ := P2 _ (tele_obs hkeys hend)
  cases hle.sort_inv
  cases hi with
  | cons hfirst hrest =>
    obtain ⟨y, hy, yle⟩ := dP2 [] _ _ rfl (.sort twoF) (Obs.piDomOb Obs.sort)
    cases yle.sort_inv
    exact ⟨_, .cons hfirst hrest, hd, ⟨σ', S', hkeys, hend⟩, hx, _, _, rfl, hy⟩

-- Rebuild an actual positive observation with the extracted keys and stored type.
theorem sourceObserved : Obs constEnv 0 [] .id .empty source (.rigid constName [] 2 oneF) := by
  obtain ⟨info, hi, _, P1, _, _⟩ := extracted
  obtain ⟨τs, hτs, ht⟩ := P1 (.rigid constName [] 2 oneF) (.rigid (.head _))
  have mapArgs {info : List (Key × VExpr)} {args : List VExpr}
      (h : List.Forall₂ (KeyData constEnv 0 [] [] .id .empty) info args) :
      List.Forall₂ (fun (k : Key) a =>
        k.2.1 = ElCls constEnv 0 [] k.1 (a.subst .id) ∧
        ∀ x ∈ k.2.2, Obs constEnv 0 [] .id .empty a x) (info.map (·.1)) args := by
    induction h with
    | nil => exact .nil
    | cons h _ ih => exact .cons ⟨h.1, h.2.1⟩ ih
  have args := mapArgs hi
  apply obs_mkApps_of_wrap args
  refine Obs.const (fun df h => (noRules df h).elim) constLookup hτs ht (.inl ⟨oneF, ?_⟩)
  have : (info.map (·.1)).length = 2 := by simpa using hi.length_eq
  rw [this]
  rfl

-- The fallback constructor cannot hide syntax requiring spine or binder inversion.
theorem constantNotFallback : ¬ (∀ c ls args, source ≠ .mkApps (.const c ls) args) := by
  intro h; exact h constName [] [betaType, .sort .zero] rfl

theorem lambdaNotFallback : ¬ (∀ A b, lambdaTerm ≠ .lam A b) := by
  intro h; exact h _ _ rfl

theorem variableNotFallback : ¬ (∀ i, VExpr.bvar 0 ≠ .bvar i) := by
  intro h; exact h 0 rfl

end ModelSpinesTest

namespace ModelSpinesAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.HTS,
    `Lean4Lean.VEnv.Model.DomsSD,
    `Lean4Lean.VEnv.Model.PiSD.doms,
    `Lean4Lean.VEnv.Model.mkApps_const_ne_bvar,
    `Lean4Lean.VEnv.Model.mkApps_const_ne_lam,
    `Lean4Lean.VExpr.mkApps_const_ne_forallE,
    `Lean4Lean.VEnv.Model.HTS.sort',
    `Lean4Lean.VEnv.Model.HTS.beta_lhs,
    `Lean4Lean.VEnv.Model.SoundAt.refl_l,
    `Lean4Lean.VEnv.Model.SoundAt.refl_r,
    `Lean4Lean.VEnv.Model.TeleKeys.typed,
    `Lean4Lean.VEnv.Model.SD.sub,
    `Lean4Lean.VEnv.Model.HTS.bvar_chain,
    `Lean4Lean.VEnv.Model.HTS.forallE_inv,
    `Lean4Lean.VEnv.Model.HTS.piSD,
    `Lean4Lean.VEnv.Model.HTS.lam_inv,
    `Lean4Lean.VEnv.Model.KeyData,
    `Lean4Lean.VEnv.Model.forall₂_append_single,
    `Lean4Lean.VEnv.Model.forall₂_snoc_right,
    `Lean4Lean.VEnv.Model.HeadTy,
    `Lean4Lean.VEnv.Model.HTS.spineH,
    `Lean4Lean.VEnv.Model.HTS.spine,
    `Lean4Lean.VEnv.Model.HTS.lamSpine,
    `Lean4Lean.VEnv.Model.inst_liftN_bvar,
    `Lean4Lean.VEnv.Model.RuleValid,
    `Lean4Lean.VEnv.Model.sound,
    `Lean4Lean.VEnv.Model.sound_no_rules,
    `Lean4Lean.VEnv.Model.HTS.bvar,
    `Lean4Lean.VEnv.Model.HTS.other,
    `Lean4Lean.VEnv.Model.HTS.const,
    `Lean4Lean.VEnv.Model.HTS.app,
    `Lean4Lean.VEnv.Model.HTS.lam,
    `Lean4Lean.VEnv.Model.HTS.forallE,
    `Lean4Lean.VEnv.Model.HTS.conv,
    `Lean4Lean.VEnv.Model.DomsSD.nil,
    `Lean4Lean.VEnv.Model.DomsSD.cons,
    `ModelSpinesTest.one,
    `ModelSpinesTest.two,
    `ModelSpinesTest.three,
    `ModelSpinesTest.altZero,
    `ModelSpinesTest.oneF,
    `ModelSpinesTest.twoF,
    `ModelSpinesTest.tag,
    `ModelSpinesTest.typeTag,
    `ModelSpinesTest.zeroEq,
    `ModelSpinesTest.distinctLevels,
    `ModelSpinesTest.betaType,
    `ModelSpinesTest.betaEquality,
    `ModelSpinesTest.distinctRepresentatives,
    `ModelSpinesTest.D1,
    `ModelSpinesTest.c1,
    `ModelSpinesTest.D2,
    `ModelSpinesTest.c2,
    `ModelSpinesTest.c1Typed,
    `ModelSpinesTest.betaMember,
    `ModelSpinesTest.c2Typed,
    `ModelSpinesTest.sortBacked,
    `ModelSpinesTest.k1,
    `ModelSpinesTest.k2,
    `ModelSpinesTest.keys,
    `ModelSpinesTest.doms,
    `ModelSpinesTest.endType,
    `ModelSpinesTest.piType,
    `ModelSpinesTest.lambdaTerm,
    `ModelSpinesTest.σ1,
    `ModelSpinesTest.σ2,
    `ModelSpinesTest.S1,
    `ModelSpinesTest.S2,
    `ModelSpinesTest.cv,
    `ModelSpinesTest.lambdaTyped,
    `ModelSpinesTest.firstKeyTyped,
    `ModelSpinesTest.secondDomainObserved,
    `ModelSpinesTest.secondKeyTyped,
    `ModelSpinesTest.telescopeKeys,
    `ModelSpinesTest.twoKeys,
    `ModelSpinesTest.lambdaObserved,
    `ModelSpinesTest.telescopeCodomain,
    `ModelSpinesTest.codomainObserved,
    `ModelSpinesTest.wrappedTyped,
    `ModelSpinesTest.domainSD,
    `ModelSpinesTest.bodySD,
    `ModelSpinesTest.innerPiSD,
    `ModelSpinesTest.telescopeSD,
    `ModelSpinesTest.piTypeSD,
    `ModelSpinesTest.lambdaSD,
    `ModelSpinesTest.lambdaHTS,
    `ModelSpinesTest.piTypeHTS,
    `ModelSpinesTest.derivedPiSoundness,
    `ModelSpinesTest.extendedTyped,
    `ModelSpinesTest.typeLevel,
    `ModelSpinesTest.delayedPi,
    `ModelSpinesTest.delayStrong,
    `ModelSpinesTest.convertedLambdaStrong,
    `ModelSpinesTest.convertedLambdaSound,
    `ModelSpinesTest.lambdaThroughConversion,
    `ModelSpinesTest.distinctPiTypes,
    `ModelSpinesTest.constName,
    `ModelSpinesTest.constValue,
    `ModelSpinesTest.constEnv,
    `ModelSpinesTest.constEnvWF,
    `ModelSpinesTest.emptyLE,
    `ModelSpinesTest.noRules,
    `ModelSpinesTest.constLookup,
    `ModelSpinesTest.constantStrong,
    `ModelSpinesTest.betaStrong,
    `ModelSpinesTest.betaReflStrong,
    `ModelSpinesTest.resultPiStrong,
    `ModelSpinesTest.firstApplicationStrong,
    `ModelSpinesTest.source,
    `ModelSpinesTest.sourceAtBeta,
    `ModelSpinesTest.sourceStrong,
    `ModelSpinesTest.sourceSound,
    `ModelSpinesTest.betaObserved,
    `ModelSpinesTest.demands,
    `ModelSpinesTest.demandedArguments,
    `ModelSpinesTest.extracted,
    `ModelSpinesTest.spineRoundtrip,
    `ModelSpinesTest.sourceObserved,
    `ModelSpinesTest.constantNotFallback,
    `ModelSpinesTest.lambdaNotFallback,
    `ModelSpinesTest.variableNotFallback]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.HTS, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.PiSD.doms, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mkApps_const_ne_bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mkApps_const_ne_lam, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.mkApps_const_ne_forallE, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.sort', [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.beta_lhs, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.refl_l, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.refl_r, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.typed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.sub, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.bvar_chain, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.forallE_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.piSD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.lam_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.KeyData, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.forall₂_append_single, []),
    (`Lean4Lean.VEnv.Model.forall₂_snoc_right, []),
    (`Lean4Lean.VEnv.Model.HeadTy, [`propext]),
    (`Lean4Lean.VEnv.Model.HTS.spineH, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.spine, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.lamSpine, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.inst_liftN_bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RuleValid, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.sound, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.sound_no_rules, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.bvar, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.other, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.const, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.app, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.lam, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.forallE, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.conv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.nil, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.cons, [`Quot.sound, `propext]),
    (`ModelSpinesTest.one, []),
    (`ModelSpinesTest.two, []),
    (`ModelSpinesTest.three, []),
    (`ModelSpinesTest.altZero, []),
    (`ModelSpinesTest.oneF, []),
    (`ModelSpinesTest.twoF, []),
    (`ModelSpinesTest.tag, []),
    (`ModelSpinesTest.typeTag, []),
    (`ModelSpinesTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelSpinesTest.distinctLevels, []),
    (`ModelSpinesTest.betaType, []),
    (`ModelSpinesTest.betaEquality, [`propext]),
    (`ModelSpinesTest.distinctRepresentatives, []),
    (`ModelSpinesTest.D1, [`propext]),
    (`ModelSpinesTest.c1, [`propext]),
    (`ModelSpinesTest.D2, [`propext]),
    (`ModelSpinesTest.c2, [`propext]),
    (`ModelSpinesTest.c1Typed, [`propext]),
    (`ModelSpinesTest.betaMember, [`propext]),
    (`ModelSpinesTest.c2Typed, [`propext]),
    (`ModelSpinesTest.sortBacked, [`propext]),
    (`ModelSpinesTest.k1, [`propext]),
    (`ModelSpinesTest.k2, [`propext]),
    (`ModelSpinesTest.keys, [`propext]),
    (`ModelSpinesTest.doms, []),
    (`ModelSpinesTest.endType, []),
    (`ModelSpinesTest.piType, []),
    (`ModelSpinesTest.lambdaTerm, []),
    (`ModelSpinesTest.σ1, []),
    (`ModelSpinesTest.σ2, []),
    (`ModelSpinesTest.S1, []),
    (`ModelSpinesTest.S2, []),
    (`ModelSpinesTest.cv, [`propext]),
    (`ModelSpinesTest.lambdaTyped, [`propext]),
    (`ModelSpinesTest.firstKeyTyped, [`Quot.sound, `propext]),
    (`ModelSpinesTest.secondDomainObserved, [`Quot.sound, `propext]),
    (`ModelSpinesTest.secondKeyTyped, [`Quot.sound, `propext]),
    (`ModelSpinesTest.telescopeKeys, [`Quot.sound, `propext]),
    (`ModelSpinesTest.twoKeys, [`Quot.sound, `propext]),
    (`ModelSpinesTest.lambdaObserved, [`Quot.sound, `propext]),
    (`ModelSpinesTest.telescopeCodomain, [`Quot.sound, `propext]),
    (`ModelSpinesTest.codomainObserved, [`Quot.sound, `propext]),
    (`ModelSpinesTest.wrappedTyped, [`Quot.sound, `propext]),
    (`ModelSpinesTest.domainSD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.bodySD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.telescopeSD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.piTypeSD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.lambdaSD, [`Quot.sound, `propext]),
    (`ModelSpinesTest.lambdaHTS, [`Quot.sound, `propext]),
    (`ModelSpinesTest.piTypeHTS, [`Quot.sound, `propext]),
    (`ModelSpinesTest.derivedPiSoundness, [`Quot.sound, `propext]),
    (`ModelSpinesTest.extendedTyped, [`Quot.sound, `propext]),
    (`ModelSpinesTest.typeLevel, []),
    (`ModelSpinesTest.delayedPi, []),
    (`ModelSpinesTest.delayStrong, [`Quot.sound, `propext]),
    (`ModelSpinesTest.convertedLambdaStrong, [`Quot.sound, `propext]),
    (`ModelSpinesTest.convertedLambdaSound, [`Quot.sound, `propext]),
    (`ModelSpinesTest.lambdaThroughConversion, [`Quot.sound, `propext]),
    (`ModelSpinesTest.distinctPiTypes, []),
    (`ModelSpinesTest.constName, []),
    (`ModelSpinesTest.constValue, []),
    (`ModelSpinesTest.constEnv, [`Quot.sound, `propext]),
    (`ModelSpinesTest.constEnvWF, [`Quot.sound, `propext]),
    (`ModelSpinesTest.emptyLE, [`Quot.sound, `propext]),
    (`ModelSpinesTest.noRules, [`Quot.sound, `propext]),
    (`ModelSpinesTest.constLookup, [`Quot.sound, `propext]),
    (`ModelSpinesTest.constantStrong, [`Quot.sound, `propext]),
    (`ModelSpinesTest.betaStrong, [`propext]),
    (`ModelSpinesTest.betaReflStrong, [`propext]),
    (`ModelSpinesTest.resultPiStrong, [`propext]),
    (`ModelSpinesTest.firstApplicationStrong, [`Quot.sound, `propext]),
    (`ModelSpinesTest.source, []),
    (`ModelSpinesTest.sourceAtBeta, [`Quot.sound, `propext]),
    (`ModelSpinesTest.sourceStrong, [`Quot.sound, `propext]),
    (`ModelSpinesTest.sourceSound, [`Quot.sound, `propext]),
    (`ModelSpinesTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelSpinesTest.demands, []),
    (`ModelSpinesTest.demandedArguments, [`Quot.sound, `propext]),
    (`ModelSpinesTest.extracted, [`Quot.sound, `propext]),
    (`ModelSpinesTest.spineRoundtrip, [`Quot.sound, `propext]),
    (`ModelSpinesTest.sourceObserved, [`Quot.sound, `propext]),
    (`ModelSpinesTest.constantNotFallback, []),
    (`ModelSpinesTest.lambdaNotFallback, []),
    (`ModelSpinesTest.variableNotFallback, [])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-spines manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-spines manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-spines axiom {root}"
    if let some proof := info.value? (allowOpaque := true) then
      if proof.hasSorry then throwError "direct model-spines admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-spines value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-spines dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-spines type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? (allowOpaque := true) then
          if value.hasSorry then throwError "model-spines admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-spines dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-spines traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-spines axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.TeleKeys.typed then [`Lean4Lean.VEnv.Model.TV.cons_cls, `Lean4Lean.VEnv.Ctx.SubstEq.cons, `Lean4Lean.VEnv.Model.TypedElCls.hasType]
      else if root == `Lean4Lean.VEnv.Model.HTS.bvar_chain then [`Lean4Lean.VEnv.TypeChain.tail, `Lean4Lean.VEnv.TypeChain.single]
      else if root == `Lean4Lean.VEnv.Model.HTS.piSD then [`Lean4Lean.VEnv.Model.HTS.forallE_inv, `Lean4Lean.VEnv.Model.PiSD.cons]
      else if root == `Lean4Lean.VEnv.Model.HTS.lam_inv then [`Lean4Lean.VEnv.Model.HTS, `Lean4Lean.VEnv.Model.Ob.Sub.trans, `Lean4Lean.VEnv.TypeChain.tail]
      else if root == `Lean4Lean.VEnv.Model.HTS.spineH then [`Lean4Lean.VEnv.Model.Obs.collect, `Lean4Lean.VEnv.Model.Obs.compact0, `Lean4Lean.VEnv.Model.Backed.close, `Lean4Lean.VEnv.Model.Obs.backed, `Lean4Lean.VEnv.Model.TypedAt.merge, `Lean4Lean.VEnv.Model.pi_list, `Lean4Lean.VEnv.Model.vcls_app, `Lean4Lean.VEnv.Model.vcls_conv, `Lean4Lean.VEnv.Model.Obs.inst_iff, `Lean4Lean.VEnv.Model.SD.sub, `Lean4Lean.VEnv.Model.KeyData, `Lean4Lean.VEnv.Model.HeadTy, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.TypedElCls.of_hasType, `Lean4Lean.VEnv.Model.TV.cons_cls]
      else if root == `Lean4Lean.VEnv.Model.HTS.spine then [`Lean4Lean.VEnv.Model.HTS.spineH, `Lean4Lean.VEnv.Model.HeadTy, `Lean4Lean.VEnv.Model.KeyData]
      else if root == `Lean4Lean.VEnv.Model.HTS.lamSpine then [`Lean4Lean.VEnv.Model.HTS.lam_inv, `Lean4Lean.VEnv.Model.pi_step, `Lean4Lean.VEnv.Model.vcls_beta, `Lean4Lean.VEnv.Model.TV.cons_cls, `Lean4Lean.VEnv.Model.TypedOb.strengthen, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.TypeChain.tyCls_subst_of_ctx]
      else if root == `Lean4Lean.VEnv.Model.sound then [`Lean4Lean.VEnv.Model.RuleValid, `Lean4Lean.VEnv.Model.HTS, `Lean4Lean.VEnv.IsDefEqStrong.rec, `Lean4Lean.VEnv.IsDefEqStrong.mono, `Lean4Lean.VEnv.Model.SoundAt.bvar, `Lean4Lean.VEnv.Model.SoundAt.symm, `Lean4Lean.VEnv.Model.SoundAt.trans, `Lean4Lean.VEnv.Model.SoundAt.sort, `Lean4Lean.VEnv.Model.SoundAt.constDF, `Lean4Lean.VEnv.Model.SoundAt.appDF, `Lean4Lean.VEnv.Model.SoundAt.lamDF, `Lean4Lean.VEnv.Model.SoundAt.forallEDF, `Lean4Lean.VEnv.Model.SoundAt.defeqDF, `Lean4Lean.VEnv.Model.SoundAt.beta, `Lean4Lean.VEnv.Model.SoundAt.eta, `Lean4Lean.VEnv.Model.SoundAt.proofIrrel]
      else if root == `Lean4Lean.VEnv.Model.sound_no_rules then [`Lean4Lean.VEnv.Model.sound, `Lean4Lean.VEnv.Model.RuleValid]
      else if root == `ModelSpinesTest.lambdaHTS then [`Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpinesTest.lambdaSD]
      else if root == `ModelSpinesTest.piTypeHTS then [`Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpinesTest.piTypeSD]
      else if root == `ModelSpinesTest.derivedPiSoundness then [`Lean4Lean.VEnv.Model.HTS.piSD, `ModelSpinesTest.piTypeHTS]
      else if root == `ModelSpinesTest.extendedTyped then [`Lean4Lean.VEnv.Model.TeleKeys.typed, `ModelSpinesTest.derivedPiSoundness, `ModelSpinesTest.telescopeKeys]
      else if root == `ModelSpinesTest.convertedLambdaSound then [`Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpinesTest.convertedLambdaStrong, `ModelSpinesTest.delayStrong]
      else if root == `ModelSpinesTest.lambdaThroughConversion then [`Lean4Lean.VEnv.Model.HTS.lamSpine, `ModelSpinesTest.convertedLambdaSound, `ModelSpinesTest.lambdaObserved, `ModelSpinesTest.telescopeKeys]
      else if root == `ModelSpinesTest.constEnvWF then [`Lean4Lean.VEnv.WF'.decl, `Lean4Lean.VDecl.WF.axiom, `ModelSpinesTest.piTypeSD]
      else if root == `ModelSpinesTest.sourceStrong then [`ModelSpinesTest.sourceAtBeta, `ModelSpinesTest.betaStrong, `Lean4Lean.VEnv.IsDefEqStrong.defeqDF]
      else if root == `ModelSpinesTest.sourceAtBeta then [`ModelSpinesTest.firstApplicationStrong, `ModelSpinesTest.betaStrong, `Lean4Lean.VEnv.IsDefEqStrong.appDF]
      else if root == `ModelSpinesTest.sourceSound then [`Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpinesTest.noRules, `ModelSpinesTest.sourceStrong, `ModelSpinesTest.constEnvWF]
      else if root == `ModelSpinesTest.extracted then [`Lean4Lean.VEnv.Model.HTS.spine, `ModelSpinesTest.sourceSound, `ModelSpinesTest.constLookup, `ModelSpinesTest.demandedArguments]
      else if root == `ModelSpinesTest.spineRoundtrip then [`ModelSpinesTest.extracted, `Lean4Lean.VEnv.Model.tele_unwind, `Lean4Lean.VEnv.Model.tele_obs, `Lean4Lean.VEnv.Model.HTS.piSD, `Lean4Lean.VEnv.Model.sound_no_rules]
      else if root == `ModelSpinesTest.sourceObserved then [`ModelSpinesTest.extracted, `Lean4Lean.VEnv.Model.obs_mkApps_of_wrap, `Lean4Lean.VEnv.Model.Obs.const, `ModelSpinesTest.constLookup, `ModelSpinesTest.noRules]
      else []
    unless required.all visited.contains do
      throwError "model-spines proof bypassed required dependencies in {root}: {repr (required.filter fun name => !visited.contains name)}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelSpinesAudit
