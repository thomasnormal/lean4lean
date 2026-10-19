import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleLemmas
import Lean.Util.CollectAxioms

namespace ModelRuleBindTest
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


-- All bounded observation sets come from the constructive finite selection.
theorem finiteBinderLists : ∃ Lx : Nat → List Ob,
    (∀ x < doms.length, S2 x = listSet (Lx x)) ∧
    tag ∈ Lx 0 ∧ typeTag ∈ Lx 1 := by
  obtain ⟨Lx, h⟩ := telescopeKeys.inner_lists
  refine ⟨Lx, h, ?_, ?_⟩
  · have he := h 0 (by decide)
    change listSet (Lx 0) tag
    rw [← he]
    exact .head _
  · have he := h 1 (by decide)
    change listSet (Lx 1) typeTag
    rw [← he]
    exact .head _

theorem splitDependent : ∃ σ S,
    TeleKeys VEnv.empty 0 [] .id .empty [.sort two] [k1] σ S ∧
    TeleKeys VEnv.empty 0 [] σ S [.bvar 0] [k2] σ2 S2 :=
  telescopeKeys.split (pre := [.sort two]) (kpre := [k1]) rfl

theorem outerAnchor (x : Nat) : σ2 (x + 2) = VExpr.Subst.id x ∧
    S2 (x + 2) = ObSets.empty x := telescopeKeys.outer x

theorem dependentBinderLookup : Lookup doms.reverse 0 (binderTy doms [] 0) :=
  lookup_binderTy (Γ := []) (by decide : 0 < doms.length)

theorem dependentDomainSound : ∃ u,
    HTS VEnv.empty 0 [] [.sort two] (.bvar 0) (.sort u) ∧
    SD VEnv.empty 0 [] [.sort two] (.bvar 0) (.bvar 0) (.sort u) :=
  piTypeHTS.tele_dom (pre := [.sort two]) (post := [])

def canonicalAnchor : VExpr.Subst := (VExpr.Subst.id.cons (.sort one)).cons (.sort .zero)

theorem differentAnchors : canonicalAnchor ≠ σ2 := by
  intro h
  have e := congrFun h 1
  exact distinctRepresentatives e.symm

theorem sameOutside (x : Nat) (hx : doms.reverse.length ≤ x) : canonicalAnchor x = σ2 x := by
  cases x with
  | zero => simp [doms] at hx
  | succ x => cases x with
    | zero => simp [doms] at hx
    | succ x => rfl

-- Head equalities use actual beta reduction, under the progressively related tail.
theorem relatedAnchors : Ctx.SubstEq VEnv.empty 0 [] canonicalAnchor σ2 doms.reverse := by
  apply SubstEq.of_heads_ind extendedTyped.1 sameOutside
  intro x A hx hlookup _
  cases hlookup with
  | zero => exact .sortDF (by trivial) (by trivial) rfl
  | succ hlookup => cases hlookup with
    | zero => exact betaEquality.symm
    | succ hlookup => cases hlookup

theorem soundBinderContext : CtxSD VEnv.empty 0 [] [] doms.reverse := by
  simpa using derivedPiSoundness.doms.ctxSD .nil

theorem transferredValuation : TV VEnv.empty 0 [] doms.reverse canonicalAnchor S2 :=
  extendedTyped.2.transfer .empty (by trivial) soundBinderContext relatedAnchors sameOutside

theorem transferredHeadTyped : TypedAt VEnv.empty 0 []
    (vcls VEnv.empty 0 [] canonicalAnchor (.bvar 0) (binderTy doms [] 0))
    canonicalAnchor S2 (binderTy doms [] 0) tag :=
  transferredValuation.2 0 _ dependentBinderLookup tag (.head _)

-- Obtain a positive rigid observation from the actual Strong derivation.
theorem rigidSpineObserved : Obs constEnv 0 [] .id .empty source (.rigid constName [] 2 oneF) :=
  spine_rigid_obs constEnvWF.ordered (by trivial) sourceSound.2 .nil TV.empty
    (fun df h => (noRules df h).elim)

theorem recoveredSpine : ∃ ks : List Key,
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls constEnv 0 [] k.1 (a.subst .id) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs constEnv 0 [] .id .empty a x' ∧ x' ≼ x)
      ks [betaType, .sort .zero] ∧
    Obs constEnv 0 [] .id .empty (.const constName []) (wrap ks (.rigid constName [] 2 oneF)) :=
  wrap_of_obs_mkApps_le rigidSpineObserved

theorem backedAndCoveredKeys : ∃ info : List (Key × VExpr),
    KeysBacked (info.map (·.1)) ∧
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls constEnv 0 [] k.1 (a.subst .id) ∧
      ∀ x ∈ k.2.2, Obs constEnv 0 [] .id .empty a x)
      (info.map (·.1)) [betaType, .sort .zero] := by
  obtain ⟨info, hi, _⟩ := extracted
  exact ⟨info, KeyData.forall₂_backed hi, KeyData.forall₂_keys hi⟩

-- Constructor inversion retains the actual head, excluding a wrong constructor.
theorem rejectsWrongConstructorHead
    (h : Obs constEnv 0 [] .id .empty source (.ctorHead (Name.mkSimple "Wrong") [] 2)) : False := by
  obtain ⟨ks, _, he⟩ := ctor_spine_inv (fun df h => (noRules df h).elim) h
    (.inl ⟨_, _, _, rfl⟩)
  rcases he with he | ⟨_, _, he⟩ | ⟨_, _, _, _, he⟩
  · exact (by decide : Name.mkSimple "Wrong" ≠ constName) (Ob.ctorHead.inj he).1
  · cases he
  · cases he

theorem patternRoundtrip {ds ds' : List VExpr} {as as' : List VExpr} {a a' : VExpr}
    (h : VExpr.wrapLams ds (.mkApps (.const constName []) (as ++ [a])) =
      VExpr.wrapLams ds' (.mkApps (.const constName []) (as' ++ [a']))) :
    ds = ds' ∧ as = as' ∧ a = a' := by
  obtain ⟨hds, _, _, has, ha⟩ := wrapLams_pat_inj h
  exact ⟨hds, has, ha⟩


namespace QuotControl

def base : VEnv := {
  constants name := if Name.mkSimple "Eq" = name then some eqConst else none
  defeqs _ := False }
def env : VEnv := (base.addQuot).getD .empty

theorem wf : env.WF := by
  have added : VEnv.empty.addConst (Name.mkSimple "Eq") eqConst = some base := rfl
  have equalityWF : base.WF := by
    refine ⟨_, .decl (.axiom (ci := ⟨eqConst, Name.mkSimple "Eq"⟩) ?_ added) .empty⟩
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : base.QuotReady := by simp [QuotReady, base]
  obtain ⟨_, checked⟩ := equalityWF
  exact ⟨_, .decl (.quot ready (show base.addQuot = some env from rfl)) checked⟩

def α : VExpr := .sort .zero
def proposition : VExpr := .forallE (.sort .zero) (.bvar 0)
def relation : VExpr := .lam α (.lam α proposition)
def relationType : VExpr := .forallE α (.forallE α (.sort .zero))

theorem propositionTyped {Γ : List VExpr} : env.HasType 0 Γ proposition (.sort .zero) :=
  .defeqDF (.sortDF (by trivial) (by trivial) VLevel.imax_zero)
    (HasType.forallE (u := one) (v := .zero) (HasType.sort (by trivial)) (.bvar .zero))

theorem relationTyped : env.HasType 0 [] relation relationType :=
  .lamDF (HasType.sort (by trivial)) (.lamDF (HasType.sort (by trivial)) propositionTyped)

def domains : List VExpr := [.sort one,
  .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1]
def result : VExpr := .mkApps (.const ``Quot [one]) [.bvar 2, .bvar 1]
def anchor1 : VExpr.Subst := VExpr.Subst.id.cons α
def anchor2 : VExpr.Subst := anchor1.cons relation
def anchor3 : VExpr.Subst := anchor2.cons proposition
def sets1 : ObSets := ObSets.empty.cons (listSet [])
def sets2 : ObSets := sets1.cons (listSet [])
def sets3 : ObSets := sets2.cons (listSet [])
def domain1 : VExpr → Prop := TyCls env 0 [] (.sort one)
def class1 : VExpr → Prop := ElCls env 0 [] domain1 α
def domain2 : VExpr → Prop := TyCls env 0 [] relationType
def class2 : VExpr → Prop := ElCls env 0 [] domain2 relation
def domain3 : VExpr → Prop := TyCls env 0 [] α
def class3 : VExpr → Prop := ElCls env 0 [] domain3 proposition
def key1 : Key := (domain1, class1, [])
def key2 : Key := (domain2, class2, [])
def key3 : Key := (domain3, class3, [])

theorem class1Typed : TypedElCls env 0 [] domain1 class1 :=
  .of_hasType (.sort (by trivial))
theorem class2Typed : TypedElCls env 0 [] domain2 class2 := .of_hasType relationTyped
theorem class3Typed : TypedElCls env 0 [] domain3 class3 := .of_hasType propositionTyped

theorem constructorKeys : TeleKeys env 0 [] .id .empty domains [key1, key2, key3] anchor3 sets3 :=
  .cons class1Typed ElCls.self nofun (fun _ h => nomatch h)
    (.cons class2Typed ElCls.self nofun (fun _ h => nomatch h)
      (.cons class3Typed ElCls.self nofun (fun _ h => nomatch h) .nil))

theorem familyKeys : TeleKeys env 0 [] .id .empty (domains.take 2) [key1, key2] anchor2 sets2 :=
  .cons class1Typed ElCls.self nofun (fun _ h => nomatch h)
    (.cons class2Typed ElCls.self nofun (fun _ h => nomatch h) .nil)

-- This fixture helper composes the proved single-Pi constructor over actual typed keys.
theorem wrapTyped {σ σ' : VExpr.Subst} {S S' : ObSets} {ds : List VExpr} {ks : List Key}
    {R : VExpr} {τc : List Ob} (h : TeleKeys env 0 [] σ S ds ks σ' S')
    (hR : ∀ τ ∈ τc, Obs env 0 [] σ' S' R τ) :
    ∃ τs, (∀ τ ∈ τs, Obs env 0 [] σ S (.wrapForalls ds R) τ) ∧
      ∀ o, (∀ cv, TypedOb env 0 [] cv o τc) → ∀ cv, TypedOb env 0 [] cv (wrap ks o) τs := by
  induction h generalizing R τc with
  | nil => exact ⟨τc, hR, fun _ h cv => h cv⟩
  | cons hc hy hK hb _ ih =>
    obtain ⟨τc', hR', ht⟩ := ih hR
    obtain ⟨τk, hk, hkt⟩ := TypedAt.merge hK
    obtain ⟨τs, hs, step⟩ := pi_list hc hy hk hkt hb hR'
    exact ⟨τs, hs, fun o ho cv => step cv _ (ht o ho _)⟩

theorem familyRigid : env.Rigid ``Quot := by
  intro df hdf ls he
  have eq : df = quotDefEq := hdf.elim id nofun
  subst eq
  exact (by decide : (``Quot.lift : Name) ≠ ``Quot) (VExpr.const.inj he).1

theorem familyHeadObserved (σ : VExpr.Subst) (S : ObSets) :
    Obs env 0 [] σ S (.const ``Quot [one])
      (wrap [key1, key2] (.rigid ``Quot [oneF] 2 oneF)) := by
  obtain ⟨τs, hs, ht⟩ := wrapTyped (R := .sort one) (τc := [typeTag]) familyKeys
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort)
  exact .const familyRigid (addQuot_quot (show base.addQuot = some env from rfl))
    hs (ht _ (fun _ => .rigid (.head _)) _) (.inl ⟨oneF, rfl⟩)

theorem resultObserved : Obs env 0 [] anchor3 sets3 result (.rigid ``Quot [oneF] 2 oneF) :=
  obs_mkApps_of_wrap (keys := [key1, key2])
    (.cons ⟨rfl, nofun⟩ (.cons ⟨rfl, nofun⟩ .nil)) (familyHeadObserved _ _)

theorem family : CtorFam env ``Quot.mk ``Quot :=
  ⟨quotMkConst, [.sort (.param 0),
    .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)), .bvar 1], [.param 0],
    [.bvar 2, .bvar 1], addQuot_quotMk (show base.addQuot = some env from rfl), by rfl⟩

theorem installed : IsInstalledCtor env ``Quot.mk :=
  ⟨quotDefEq, addQuot_defeq (show base.addQuot = some env from rfl), quotConstructorMajor⟩

theorem constructorHeadObserved : Obs env 0 [] .id .empty
    (.mkApps (.const ``Quot.mk [one]) [α, relation, proposition]) (.ctorHead ``Quot.mk [oneF] 3) := by
  obtain ⟨τs, hs, ht⟩ := wrapTyped (τc := [.rigid ``Quot [oneF] 2 oneF]) constructorKeys
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact resultObserved)
  have head : Obs env 0 [] .id .empty (.const ``Quot.mk [one])
      (wrap [key1, key2, key3] (.ctorHead ``Quot.mk [oneF] 3)) := by
    refine .ctor installed (addQuot_quotMk (show base.addQuot = some env from rfl))
      hs (ht _ (fun _ => .ctorHead ⟨``Quot, [oneF], 2, oneF, .head _, family, ?_⟩) _) (.inl rfl) ?_
    · intro e; have impossible : 1 = 0 := congrFun e []; cases impossible
    · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact fun _ h => nomatch h
  exact obs_mkApps_of_wrap (keys := [key1, key2, key3]) (.cons ⟨rfl, nofun⟩
    (.cons ⟨rfl, nofun⟩ (.cons ⟨rfl, nofun⟩ .nil))) head

theorem constructorInverted : ∃ ks : List Key, ks.length = 3 ∧
    List.Forall₂ (fun (k : Key) a => k.2.1 = ElCls env 0 [] k.1 (a.subst .id) ∧
      ∀ x ∈ k.2.2, ∃ x', Obs env 0 [] .id .empty a x' ∧ x' ≼ x)
      ks [α, relation, proposition] ∧
    CtorEnd ``Quot.mk [oneF] ks (.ctorHead ``Quot.mk [oneF] 3) := by
  obtain ⟨ks, hk, he⟩ := ctor_spine_inv (wf.installed_constructor_rigid installed)
    constructorHeadObserved (.inl ⟨_, _, _, rfl⟩)
  exact ⟨ks, hk.length_eq, hk, he⟩

theorem constructorTyped : env.HasType 0 []
    (.mkApps (.const ``Quot.mk [one]) [α, relation, proposition])
    (.mkApps (.const ``Quot [one]) [α, relation]) :=
  HasType.app (HasType.app (HasType.app
    (HasType.const (addQuot_quotMk (show base.addQuot = some env from rfl))
      (by simp [one, VLevel.WF]) rfl) (HasType.sort (by trivial))) relationTyped) propositionTyped

theorem constructorFieldObserved : Obs env 0 [] .id .empty
    (.mkApps (.const ``Quot.mk [one]) [α, relation, proposition]) (.ctorArg 2 class3) := by
  obtain ⟨τs, hs, ht⟩ := wrapTyped (τc := [.rigid ``Quot [oneF] 2 oneF]) constructorKeys
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact resultObserved)
  have head : Obs env 0 [] .id .empty (.const ``Quot.mk [one])
      (wrap [key1, key2, key3] (.ctorArg 2 class3)) := by
    refine .ctor installed (addQuot_quotMk (show base.addQuot = some env from rfl))
      hs (ht _ (fun _ => .ctorArg ⟨``Quot, [oneF], 2, oneF, .head _, family, ?_⟩) _)
      (.inr (.inl ⟨2, by decide, rfl⟩)) ?_
    · intro e; have impossible : 1 = 0 := congrFun e []; cases impossible
    · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact fun _ h => nomatch h
  exact obs_mkApps_of_wrap (keys := [key1, key2, key3]) (.cons ⟨rfl, nofun⟩
    (.cons ⟨rfl, nofun⟩ (.cons ⟨rfl, nofun⟩ .nil))) head

theorem constructorFieldRecovered : ∃ ks : List Key, ks.length = 3 ∧
    ∃ h : 2 < ks.length, (ks[2]).2.1 = class3 := by
  obtain ⟨ks, hk, he⟩ := ctor_spine_inv (wf.installed_constructor_rigid installed)
    constructorFieldObserved (.inr (.inl ⟨_, _, rfl⟩))
  refine ⟨ks, hk.length_eq, ?_⟩
  rcases he with he | ⟨i, hi, he⟩ | ⟨_, _, _, _, he⟩
  · cases he
  · obtain ⟨rfl, he⟩ := Ob.ctorArg.inj he
    exact ⟨hi, he.symm⟩
  · cases he

end QuotControl

end ModelRuleBindTest

namespace ModelRuleBindAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.forall₂_zip,
    `Lean4Lean.VEnv.Model.mkApps_const_inj,
    `Lean4Lean.VEnv.Model.wrapLams_pat_inj,
    `Lean4Lean.VEnv.Model.wrapLams_inj_len,
    `Lean4Lean.VEnv.Model.lookup_append,
    `Lean4Lean.VEnv.Model.lookup_binderTy,
    `Lean4Lean.VEnv.Model.TeleKeys.split,
    `Lean4Lean.VEnv.Model.HTS.tele_dom,
    `Lean4Lean.VEnv.Model.subst_eta,
    `Lean4Lean.VEnv.Model.ObSets.tail,
    `Lean4Lean.VEnv.Model.obSets_eta,
    `Lean4Lean.VEnv.Model.Obs.lift_iff_tail,
    `Lean4Lean.VEnv.Model.TypedAt.lift_iff_tail,
    `Lean4Lean.VEnv.Model.TV.tail,
    `Lean4Lean.VEnv.Model.CtxSD,
    `Lean4Lean.VEnv.Model.DomsSD.ctxSD,
    `Lean4Lean.VEnv.Model.TV.transfer,
    `Lean4Lean.VEnv.Model.SubstEq.of_heads_ind,
    `Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le,
    `Lean4Lean.VEnv.Model.wrap_inj_len,
    `Lean4Lean.VEnv.Model.CtorEnd.notApp,
    `Lean4Lean.VEnv.Model.ctor_spine_inv,
    `Lean4Lean.VEnv.Model.instL_wrapLams,
    `Lean4Lean.VEnv.Model.KeyData.forall₂_keys,
    `Lean4Lean.VEnv.Model.KeyData.forall₂_backed,
    `Lean4Lean.VEnv.Model.forall₂_nil_lists,
    `Lean4Lean.VEnv.Model.TeleKeys.outer,
    `Lean4Lean.VEnv.Model.TeleKeys.inner,
    `Lean4Lean.VEnv.Model.TeleKeys.inner_lists,
    `Lean4Lean.VEnv.Model.spine_rigid_obs,
    `Lean4Lean.VEnv.Model.CtxSD.nil,
    `Lean4Lean.VEnv.Model.CtxSD.cons,
    `ModelRuleBindTest.one,
    `ModelRuleBindTest.two,
    `ModelRuleBindTest.three,
    `ModelRuleBindTest.altZero,
    `ModelRuleBindTest.oneF,
    `ModelRuleBindTest.twoF,
    `ModelRuleBindTest.tag,
    `ModelRuleBindTest.typeTag,
    `ModelRuleBindTest.zeroEq,
    `ModelRuleBindTest.distinctLevels,
    `ModelRuleBindTest.betaType,
    `ModelRuleBindTest.betaEquality,
    `ModelRuleBindTest.distinctRepresentatives,
    `ModelRuleBindTest.D1,
    `ModelRuleBindTest.c1,
    `ModelRuleBindTest.D2,
    `ModelRuleBindTest.c2,
    `ModelRuleBindTest.c1Typed,
    `ModelRuleBindTest.betaMember,
    `ModelRuleBindTest.c2Typed,
    `ModelRuleBindTest.sortBacked,
    `ModelRuleBindTest.k1,
    `ModelRuleBindTest.k2,
    `ModelRuleBindTest.keys,
    `ModelRuleBindTest.doms,
    `ModelRuleBindTest.endType,
    `ModelRuleBindTest.piType,
    `ModelRuleBindTest.lambdaTerm,
    `ModelRuleBindTest.σ1,
    `ModelRuleBindTest.σ2,
    `ModelRuleBindTest.S1,
    `ModelRuleBindTest.S2,
    `ModelRuleBindTest.cv,
    `ModelRuleBindTest.lambdaTyped,
    `ModelRuleBindTest.firstKeyTyped,
    `ModelRuleBindTest.secondDomainObserved,
    `ModelRuleBindTest.secondKeyTyped,
    `ModelRuleBindTest.telescopeKeys,
    `ModelRuleBindTest.twoKeys,
    `ModelRuleBindTest.lambdaObserved,
    `ModelRuleBindTest.telescopeCodomain,
    `ModelRuleBindTest.codomainObserved,
    `ModelRuleBindTest.wrappedTyped,
    `ModelRuleBindTest.domainSD,
    `ModelRuleBindTest.bodySD,
    `ModelRuleBindTest.innerPiSD,
    `ModelRuleBindTest.telescopeSD,
    `ModelRuleBindTest.piTypeSD,
    `ModelRuleBindTest.lambdaSD,
    `ModelRuleBindTest.lambdaHTS,
    `ModelRuleBindTest.piTypeHTS,
    `ModelRuleBindTest.derivedPiSoundness,
    `ModelRuleBindTest.extendedTyped,
    `ModelRuleBindTest.typeLevel,
    `ModelRuleBindTest.delayedPi,
    `ModelRuleBindTest.delayStrong,
    `ModelRuleBindTest.convertedLambdaStrong,
    `ModelRuleBindTest.convertedLambdaSound,
    `ModelRuleBindTest.lambdaThroughConversion,
    `ModelRuleBindTest.distinctPiTypes,
    `ModelRuleBindTest.constName,
    `ModelRuleBindTest.constValue,
    `ModelRuleBindTest.constEnv,
    `ModelRuleBindTest.constEnvWF,
    `ModelRuleBindTest.emptyLE,
    `ModelRuleBindTest.noRules,
    `ModelRuleBindTest.constLookup,
    `ModelRuleBindTest.constantStrong,
    `ModelRuleBindTest.betaStrong,
    `ModelRuleBindTest.betaReflStrong,
    `ModelRuleBindTest.resultPiStrong,
    `ModelRuleBindTest.firstApplicationStrong,
    `ModelRuleBindTest.source,
    `ModelRuleBindTest.sourceAtBeta,
    `ModelRuleBindTest.sourceStrong,
    `ModelRuleBindTest.sourceSound,
    `ModelRuleBindTest.betaObserved,
    `ModelRuleBindTest.demands,
    `ModelRuleBindTest.demandedArguments,
    `ModelRuleBindTest.extracted,
    `ModelRuleBindTest.spineRoundtrip,
    `ModelRuleBindTest.sourceObserved,
    `ModelRuleBindTest.finiteBinderLists,
    `ModelRuleBindTest.splitDependent,
    `ModelRuleBindTest.outerAnchor,
    `ModelRuleBindTest.dependentBinderLookup,
    `ModelRuleBindTest.dependentDomainSound,
    `ModelRuleBindTest.canonicalAnchor,
    `ModelRuleBindTest.differentAnchors,
    `ModelRuleBindTest.sameOutside,
    `ModelRuleBindTest.relatedAnchors,
    `ModelRuleBindTest.soundBinderContext,
    `ModelRuleBindTest.transferredValuation,
    `ModelRuleBindTest.transferredHeadTyped,
    `ModelRuleBindTest.rigidSpineObserved,
    `ModelRuleBindTest.recoveredSpine,
    `ModelRuleBindTest.backedAndCoveredKeys,
    `ModelRuleBindTest.rejectsWrongConstructorHead,
    `ModelRuleBindTest.patternRoundtrip,
    `ModelRuleBindTest.QuotControl.base,
    `ModelRuleBindTest.QuotControl.env,
    `ModelRuleBindTest.QuotControl.wf,
    `ModelRuleBindTest.QuotControl.α,
    `ModelRuleBindTest.QuotControl.proposition,
    `ModelRuleBindTest.QuotControl.relation,
    `ModelRuleBindTest.QuotControl.relationType,
    `ModelRuleBindTest.QuotControl.propositionTyped,
    `ModelRuleBindTest.QuotControl.relationTyped,
    `ModelRuleBindTest.QuotControl.domains,
    `ModelRuleBindTest.QuotControl.result,
    `ModelRuleBindTest.QuotControl.anchor1,
    `ModelRuleBindTest.QuotControl.anchor2,
    `ModelRuleBindTest.QuotControl.anchor3,
    `ModelRuleBindTest.QuotControl.sets1,
    `ModelRuleBindTest.QuotControl.sets2,
    `ModelRuleBindTest.QuotControl.sets3,
    `ModelRuleBindTest.QuotControl.domain1,
    `ModelRuleBindTest.QuotControl.class1,
    `ModelRuleBindTest.QuotControl.domain2,
    `ModelRuleBindTest.QuotControl.class2,
    `ModelRuleBindTest.QuotControl.domain3,
    `ModelRuleBindTest.QuotControl.class3,
    `ModelRuleBindTest.QuotControl.key1,
    `ModelRuleBindTest.QuotControl.key2,
    `ModelRuleBindTest.QuotControl.key3,
    `ModelRuleBindTest.QuotControl.class1Typed,
    `ModelRuleBindTest.QuotControl.class2Typed,
    `ModelRuleBindTest.QuotControl.class3Typed,
    `ModelRuleBindTest.QuotControl.constructorKeys,
    `ModelRuleBindTest.QuotControl.familyKeys,
    `ModelRuleBindTest.QuotControl.wrapTyped,
    `ModelRuleBindTest.QuotControl.familyRigid,
    `ModelRuleBindTest.QuotControl.familyHeadObserved,
    `ModelRuleBindTest.QuotControl.resultObserved,
    `ModelRuleBindTest.QuotControl.family,
    `ModelRuleBindTest.QuotControl.installed,
    `ModelRuleBindTest.QuotControl.constructorHeadObserved,
    `ModelRuleBindTest.QuotControl.constructorInverted,
    `ModelRuleBindTest.QuotControl.constructorTyped,
    `ModelRuleBindTest.QuotControl.constructorFieldObserved,
    `ModelRuleBindTest.QuotControl.constructorFieldRecovered]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.forall₂_zip, []),
    (`Lean4Lean.VEnv.Model.mkApps_const_inj, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrapLams_pat_inj, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrapLams_inj_len, []),
    (`Lean4Lean.VEnv.Model.lookup_append, [`propext]),
    (`Lean4Lean.VEnv.Model.lookup_binderTy, [`propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.split, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.tele_dom, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.subst_eta, [`Quot.sound]),
    (`Lean4Lean.VEnv.Model.ObSets.tail, []),
    (`Lean4Lean.VEnv.Model.obSets_eta, [`Quot.sound]),
    (`Lean4Lean.VEnv.Model.Obs.lift_iff_tail, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedAt.lift_iff_tail, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.tail, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.CtxSD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.ctxSD, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.transfer, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SubstEq.of_heads_ind, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrap_inj_len, [`propext]),
    (`Lean4Lean.VEnv.Model.CtorEnd.notApp, [`propext]),
    (`Lean4Lean.VEnv.Model.ctor_spine_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.instL_wrapLams, [`propext]),
    (`Lean4Lean.VEnv.Model.KeyData.forall₂_keys, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.KeyData.forall₂_backed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.forall₂_nil_lists, []),
    (`Lean4Lean.VEnv.Model.TeleKeys.outer, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.inner, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.inner_lists, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.spine_rigid_obs, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.CtxSD.nil, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.CtxSD.cons, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.one, []),
    (`ModelRuleBindTest.two, []),
    (`ModelRuleBindTest.three, []),
    (`ModelRuleBindTest.altZero, []),
    (`ModelRuleBindTest.oneF, []),
    (`ModelRuleBindTest.twoF, []),
    (`ModelRuleBindTest.tag, []),
    (`ModelRuleBindTest.typeTag, []),
    (`ModelRuleBindTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.distinctLevels, []),
    (`ModelRuleBindTest.betaType, []),
    (`ModelRuleBindTest.betaEquality, [`propext]),
    (`ModelRuleBindTest.distinctRepresentatives, []),
    (`ModelRuleBindTest.D1, [`propext]),
    (`ModelRuleBindTest.c1, [`propext]),
    (`ModelRuleBindTest.D2, [`propext]),
    (`ModelRuleBindTest.c2, [`propext]),
    (`ModelRuleBindTest.c1Typed, [`propext]),
    (`ModelRuleBindTest.betaMember, [`propext]),
    (`ModelRuleBindTest.c2Typed, [`propext]),
    (`ModelRuleBindTest.sortBacked, [`propext]),
    (`ModelRuleBindTest.k1, [`propext]),
    (`ModelRuleBindTest.k2, [`propext]),
    (`ModelRuleBindTest.keys, [`propext]),
    (`ModelRuleBindTest.doms, []),
    (`ModelRuleBindTest.endType, []),
    (`ModelRuleBindTest.piType, []),
    (`ModelRuleBindTest.lambdaTerm, []),
    (`ModelRuleBindTest.σ1, []),
    (`ModelRuleBindTest.σ2, []),
    (`ModelRuleBindTest.S1, []),
    (`ModelRuleBindTest.S2, []),
    (`ModelRuleBindTest.cv, [`propext]),
    (`ModelRuleBindTest.lambdaTyped, [`propext]),
    (`ModelRuleBindTest.firstKeyTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.secondDomainObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.secondKeyTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.telescopeKeys, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.twoKeys, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.lambdaObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.telescopeCodomain, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.codomainObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.wrappedTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.domainSD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.bodySD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.telescopeSD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.piTypeSD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.lambdaSD, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.lambdaHTS, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.piTypeHTS, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.derivedPiSoundness, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.extendedTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.typeLevel, []),
    (`ModelRuleBindTest.delayedPi, []),
    (`ModelRuleBindTest.delayStrong, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.convertedLambdaStrong, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.convertedLambdaSound, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.lambdaThroughConversion, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.distinctPiTypes, []),
    (`ModelRuleBindTest.constName, []),
    (`ModelRuleBindTest.constValue, []),
    (`ModelRuleBindTest.constEnv, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.constEnvWF, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.emptyLE, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.noRules, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.constLookup, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.constantStrong, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.betaStrong, [`propext]),
    (`ModelRuleBindTest.betaReflStrong, [`propext]),
    (`ModelRuleBindTest.resultPiStrong, [`propext]),
    (`ModelRuleBindTest.firstApplicationStrong, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.source, []),
    (`ModelRuleBindTest.sourceAtBeta, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.sourceStrong, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.sourceSound, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.demands, []),
    (`ModelRuleBindTest.demandedArguments, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.extracted, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.spineRoundtrip, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.sourceObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.finiteBinderLists, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.splitDependent, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.outerAnchor, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.dependentBinderLookup, [`propext]),
    (`ModelRuleBindTest.dependentDomainSound, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.canonicalAnchor, []),
    (`ModelRuleBindTest.differentAnchors, []),
    (`ModelRuleBindTest.sameOutside, [`propext]),
    (`ModelRuleBindTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.soundBinderContext, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.transferredValuation, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.transferredHeadTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.rigidSpineObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.recoveredSpine, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.backedAndCoveredKeys, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.rejectsWrongConstructorHead, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.patternRoundtrip, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.base, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.env, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.wf, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.α, []),
    (`ModelRuleBindTest.QuotControl.proposition, []),
    (`ModelRuleBindTest.QuotControl.relation, []),
    (`ModelRuleBindTest.QuotControl.relationType, []),
    (`ModelRuleBindTest.QuotControl.propositionTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.relationTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.domains, []),
    (`ModelRuleBindTest.QuotControl.result, []),
    (`ModelRuleBindTest.QuotControl.anchor1, []),
    (`ModelRuleBindTest.QuotControl.anchor2, []),
    (`ModelRuleBindTest.QuotControl.anchor3, []),
    (`ModelRuleBindTest.QuotControl.sets1, []),
    (`ModelRuleBindTest.QuotControl.sets2, []),
    (`ModelRuleBindTest.QuotControl.sets3, []),
    (`ModelRuleBindTest.QuotControl.domain1, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class1, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.domain2, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class2, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.domain3, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class3, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.key1, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.key2, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.key3, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class1Typed, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class2Typed, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.class3Typed, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorKeys, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.familyKeys, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.wrapTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.familyRigid, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.familyHeadObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.resultObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.family, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.installed, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorHeadObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorInverted, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorTyped, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorFieldObserved, [`Quot.sound, `propext]),
    (`ModelRuleBindTest.QuotControl.constructorFieldRecovered, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-rulebind manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-rulebind manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-rulebind axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-rulebind admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-rulebind value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-rulebind dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-rulebind type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-rulebind admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-rulebind dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-rulebind traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-rulebind axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.mkApps_const_inj then [`List.eq_nil_or_concat, `Lean4Lean.VExpr.mkApps_snoc]
      else if root == `Lean4Lean.VEnv.Model.wrapLams_pat_inj then [`Lean4Lean.VEnv.Model.mkApps_const_inj]
      else if root == `Lean4Lean.VEnv.Model.lookup_binderTy then [`Lean4Lean.VEnv.Model.lookup_append, `Lean4Lean.VExpr.instL_liftN]
      else if root == `Lean4Lean.VEnv.Model.TeleKeys.split then [`Lean4Lean.VEnv.Model.TeleKeys.cons]
      else if root == `Lean4Lean.VEnv.Model.HTS.tele_dom then [`Lean4Lean.VEnv.Model.HTS.forallE_inv]
      else if root == `Lean4Lean.VEnv.Model.TV.tail then [`Lean4Lean.VEnv.Model.TypedAt.lift_iff_tail, `Lean4Lean.VEnv.Model.vcls_tail]
      else if root == `Lean4Lean.VEnv.Model.DomsSD.ctxSD then [`Lean4Lean.VEnv.Model.CtxSD.cons]
      else if root == `Lean4Lean.VEnv.Model.TV.transfer then [`Lean4Lean.VEnv.Model.CtxSD, `Lean4Lean.VEnv.Model.vcls_substEq, `Lean4Lean.VEnv.Model.TypedAt.mono_le, `Lean4Lean.VEnv.Model.SubstEq.symm]
      else if root == `Lean4Lean.VEnv.Model.SubstEq.of_heads_ind then [`Lean4Lean.VEnv.Ctx.SubstEq.cons, `Lean4Lean.VExpr.lift_subst]
      else if root == `Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le then [`Lean4Lean.VEnv.Model.Obs.app_iff]
      else if root == `Lean4Lean.VEnv.Model.ctor_spine_inv then [`Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le, `Lean4Lean.VEnv.Model.wrap_inj, `Lean4Lean.VEnv.Model.CtorEnd.notApp, `Lean4Lean.VEnv.Model.wrapLams_mkApps_head, `Lean4Lean.VEnv.Model.Obs.ctor]
      else if root == `Lean4Lean.VEnv.Model.KeyData.forall₂_backed then [`Lean4Lean.VEnv.Model.KeyData, `Lean4Lean.VEnv.Model.KeysBacked]
      else if root == `Lean4Lean.VEnv.Model.TeleKeys.inner_lists then [`Lean4Lean.VEnv.Model.exists_fin_function, `Lean4Lean.VEnv.Model.TeleKeys.inner]
      else if root == `Lean4Lean.VEnv.Model.spine_rigid_obs then [`Lean4Lean.VEnv.Model.HTS.spine, `Lean4Lean.VEnv.Model.KeyData.forall₂_keys, `Lean4Lean.VEnv.Model.obs_mkApps_of_wrap, `Lean4Lean.VEnv.Model.Obs.const]
      else if root == `ModelRuleBindTest.finiteBinderLists then [`Lean4Lean.VEnv.Model.TeleKeys.inner_lists, `ModelRuleBindTest.telescopeKeys]
      else if root == `ModelRuleBindTest.splitDependent then [`Lean4Lean.VEnv.Model.TeleKeys.split, `ModelRuleBindTest.telescopeKeys]
      else if root == `ModelRuleBindTest.outerAnchor then [`Lean4Lean.VEnv.Model.TeleKeys.outer, `ModelRuleBindTest.telescopeKeys]
      else if root == `ModelRuleBindTest.dependentBinderLookup then [`Lean4Lean.VEnv.Model.lookup_binderTy]
      else if root == `ModelRuleBindTest.dependentDomainSound then [`Lean4Lean.VEnv.Model.HTS.tele_dom, `ModelRuleBindTest.piTypeHTS]
      else if root == `ModelRuleBindTest.relatedAnchors then [`Lean4Lean.VEnv.Model.SubstEq.of_heads_ind, `ModelRuleBindTest.extendedTyped, `ModelRuleBindTest.betaEquality]
      else if root == `ModelRuleBindTest.soundBinderContext then [`Lean4Lean.VEnv.Model.DomsSD.ctxSD, `ModelRuleBindTest.derivedPiSoundness]
      else if root == `ModelRuleBindTest.transferredValuation then [`Lean4Lean.VEnv.Model.TV.transfer, `ModelRuleBindTest.relatedAnchors, `ModelRuleBindTest.soundBinderContext]
      else if root == `ModelRuleBindTest.transferredHeadTyped then [`ModelRuleBindTest.transferredValuation, `ModelRuleBindTest.dependentBinderLookup]
      else if root == `ModelRuleBindTest.rigidSpineObserved then [`Lean4Lean.VEnv.Model.spine_rigid_obs, `ModelRuleBindTest.sourceSound]
      else if root == `ModelRuleBindTest.recoveredSpine then [`Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le, `ModelRuleBindTest.rigidSpineObserved]
      else if root == `ModelRuleBindTest.backedAndCoveredKeys then [`Lean4Lean.VEnv.Model.KeyData.forall₂_keys, `Lean4Lean.VEnv.Model.KeyData.forall₂_backed, `ModelRuleBindTest.extracted]
      else if root == `ModelRuleBindTest.rejectsWrongConstructorHead then [`Lean4Lean.VEnv.Model.ctor_spine_inv, `ModelRuleBindTest.noRules]
      else if root == `ModelRuleBindTest.patternRoundtrip then [`Lean4Lean.VEnv.Model.wrapLams_pat_inj]
      else if root == `ModelRuleBindTest.QuotControl.wf then [`Lean4Lean.VDecl.WF.axiom, `Lean4Lean.VDecl.WF.quot, `Lean4Lean.VEnv.WF'.decl]
      else if root == `ModelRuleBindTest.QuotControl.constructorKeys then [`Lean4Lean.VEnv.Model.TeleKeys.cons, `ModelRuleBindTest.QuotControl.class1Typed, `ModelRuleBindTest.QuotControl.class2Typed, `ModelRuleBindTest.QuotControl.class3Typed]
      else if root == `ModelRuleBindTest.QuotControl.wrapTyped then [`Lean4Lean.VEnv.Model.pi_list, `Lean4Lean.VEnv.Model.TypedAt.merge]
      else if root == `ModelRuleBindTest.QuotControl.familyHeadObserved then [`ModelRuleBindTest.QuotControl.familyKeys, `ModelRuleBindTest.QuotControl.familyRigid, `ModelRuleBindTest.QuotControl.wrapTyped, `Lean4Lean.VEnv.Model.Obs.const, `Lean4Lean.VEnv.addQuot_quot]
      else if root == `ModelRuleBindTest.QuotControl.installed then [`Lean4Lean.VEnv.addQuot_defeq, `Lean4Lean.VEnv.Model.quotConstructorMajor]
      else if root == `ModelRuleBindTest.QuotControl.constructorHeadObserved then [`Lean4Lean.VEnv.Model.Obs.ctor, `Lean4Lean.VEnv.Model.TypedOb.ctorHead, `ModelRuleBindTest.QuotControl.installed, `ModelRuleBindTest.QuotControl.constructorKeys, `ModelRuleBindTest.QuotControl.resultObserved, `ModelRuleBindTest.QuotControl.family]
      else if root == `ModelRuleBindTest.QuotControl.constructorTyped then [`Lean4Lean.VEnv.HasType.app, `Lean4Lean.VEnv.HasType.const, `ModelRuleBindTest.QuotControl.relationTyped, `ModelRuleBindTest.QuotControl.propositionTyped]
      else if root == `ModelRuleBindTest.QuotControl.constructorInverted then [`Lean4Lean.VEnv.Model.ctor_spine_inv, `ModelRuleBindTest.QuotControl.constructorHeadObserved, `Lean4Lean.VEnv.WF.installed_constructor_rigid, `ModelRuleBindTest.QuotControl.wf]
      else if root == `ModelRuleBindTest.QuotControl.constructorFieldObserved then [`Lean4Lean.VEnv.Model.Obs.ctor, `Lean4Lean.VEnv.Model.TypedOb.ctorArg, `ModelRuleBindTest.QuotControl.installed, `ModelRuleBindTest.QuotControl.constructorKeys, `ModelRuleBindTest.QuotControl.resultObserved, `ModelRuleBindTest.QuotControl.family]
      else if root == `ModelRuleBindTest.QuotControl.constructorFieldRecovered then [`Lean4Lean.VEnv.Model.ctor_spine_inv, `ModelRuleBindTest.QuotControl.constructorFieldObserved, `Lean4Lean.VEnv.WF.installed_constructor_rigid, `ModelRuleBindTest.QuotControl.wf]
      else []
    unless required.all visited.contains do
      throwError "model-rulebind proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelRuleBindAudit
