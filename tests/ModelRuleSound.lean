import Lean4Lean.Theory.Typing.HeadInjectivity.Model.RuleSound
import Lean.Util.CollectAxioms

namespace ModelRuleSoundTest
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

-- Actual history supplies the equation identity, including both constructor and proof modes.
theorem quotientRegistered : env.defeqs quotDefEq :=
  addQuot_defeq (show base.addQuot = some env from rfl)

theorem quotientHeadUnique {df : VDefEq} {ls : List VLevel} (hdf : env.defeqs df)
    (hh : df.lhs.stripLams.appHead = .const ``Quot.lift ls) : df = quotDefEq :=
  Model.RewriteMetadata.quot_head_unique wf.rewriteMetadata quotientRegistered hdf hh

def lambdaDomains : VExpr → List VExpr
  | .lam A b => A :: lambdaDomains b
  | _ => []

theorem actualPatternClassified : quotDefEq = quotDefEq :=
  Model.RewriteMetadata.pattern_equation wf.rewriteMetadata quotientRegistered
    (show quotDefEq.lhs = .wrapLams (lambdaDomains quotDefEq.lhs) (.mkApps (.const ``Quot.lift [.param 0, .param 1])
      ([.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1] ++
       [.mkApps (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]])) from rfl)

theorem allConstructorDemandsObserved : ∀ o ∈ ctorObs ``Quot.mk [oneF] [key1, key2, key3],
    Obs env 0 [] .id .empty
      (.mkApps (.const ``Quot.mk [one]) [α, relation, proposition]) o := by
  intro o ho
  have hend := ctorObs_end ho
  rcases hend with rfl | ⟨i, hi, rfl⟩ | ⟨i, hi, k, hk, rfl⟩
  · exact constructorHeadObserved
  · obtain ⟨τs, hs, ht⟩ := wrapTyped (τc := [.rigid ``Quot [oneF] 2 oneF]) constructorKeys
      (fun τ hτ => by cases List.mem_singleton.1 hτ; exact resultObserved)
    have head : Obs env 0 [] .id .empty (.const ``Quot.mk [one])
        (wrap [key1, key2, key3] (.ctorArg i ([key1, key2, key3][i]).2.1)) := by
      refine .ctor installed (addQuot_quotMk (show base.addQuot = some env from rfl)) hs
        (ht _ (fun _ => .ctorArg ⟨``Quot, [oneF], 2, oneF, .head _, family, ?_⟩) _)
        (.inr (.inl ⟨i, hi, rfl⟩)) ?_
      · intro e; have impossible : 1 = 0 := congrFun e []; cases impossible
      · intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> exact fun _ h => nomatch h
    exact obs_mkApps_of_wrap (keys := [key1, key2, key3]) (.cons ⟨rfl, nofun⟩
      (.cons ⟨rfl, nofun⟩ (.cons ⟨rfl, nofun⟩ .nil))) head
  · have hempty : ∀ k ∈ [key1, key2, key3], k.2.2 = [] := by
      intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> rfl
    rw [hempty _ (List.getElem_mem hi)] at hk
    cases hk

end QuotControl

theorem firstDuplicateOccurrence : ∃ i : Nat,
    ([VExpr.sort one, .bvar 0, .bvar 0] : List VExpr)[i]? = some (.bvar 0) ∧
    ∀ j < i, ([VExpr.sort one, .bvar 0, .bvar 0] : List VExpr)[j]? ≠ some (.bvar 0) :=
  first_bvar_occurrence 0 (.tail _ (.head _))

theorem firstDuplicateIsOne : ∃ i : Nat, i = 1 ∧
    ([VExpr.sort one, .bvar 0, .bvar 0] : List VExpr)[i]? = some (.bvar 0) := by
  obtain ⟨i, hi, hf⟩ := firstDuplicateOccurrence
  cases i with
  | zero => cases hi
  | succ i => cases i with
    | zero => exact ⟨1, rfl, hi⟩
    | succ i => exact (hf 1 (by omega) rfl).elim

theorem missingVariableDecision : @decide (VExpr.bvar 1 ∈ [.bvar 0, .sort one])
    (bvar_mem_decidable 1 [.bvar 0, .sort one]) = false := rfl

theorem finiteConstructorDemands : .ctorHead constName [] keys.length ∈ ctorObs constName [] keys ∧
    .ctorArg 1 k2.2.1 ∈ ctorObs constName [] keys ∧
    .ctorArgOb 1 [k1] tag ∈ ctorObs constName [] keys :=
  ⟨mem_ctorObs_head, mem_ctorObs_arg (by decide), mem_ctorObs_argOb (by decide) (.head _)⟩

namespace BindingControl

def domains : List VExpr := [.sort one]
def anchor : VExpr.Subst := VExpr.Subst.id.cons (.sort .zero)
def sets : ObSets := ObSets.empty.cons (listSet [tag])
def D : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort one)
def c : VExpr → Prop := ElCls VEnv.empty 0 [] D (.sort .zero)
def key : Key := (D, c, [tag])
def demands : Nat → List Ob := fun _ => [tag]

theorem anchorTyped : Ctx.SubstEq VEnv.empty 0 [] anchor anchor domains.reverse :=
  .cons .nil (HasType.sort (by trivial)) (HasType.sort (by trivial))

theorem variableStrong : VEnv.empty.IsDefEqStrong 0 [.sort one] (.bvar 0) (.bvar 0) (.sort one) :=
  .bvar .zero (by trivial) (.sortDF (by trivial) (by trivial) rfl)

theorem variableSound : SoundAt VEnv.empty 0 [] [.sort one] (.bvar 0) (.bvar 0) (.sort one) ∧
    HTS VEnv.empty 0 [] [.sort one] (.bvar 0) (.sort one) := by
  have h := sound_no_rules (Δ := []) Ordered.empty (by trivial) VEnv.LE.rfl (fun _ h => h) variableStrong
  exact ⟨h.1, h.2.1⟩

theorem actualKeyData : KeyData VEnv.empty 0 [] domains.reverse anchor sets (key, .sort one) (.bvar 0) :=
  ⟨rfl, fun _ h => .bvar h, rfl, variableSound.2,
    ⟨variableStrong, variableSound.1⟩, sortBacked zeroF⟩

theorem keyDemands : List.Forall₂ (fun K (ka : Key × VExpr) => ∀ y ∈ K, y ∈ ka.1.2.2)
    (([VExpr.bvar 0].map (·.instL [])).map (argDemand 1 demands)) [(key, .sort one)] :=
  .cons (fun _ h => h) .nil

theorem leadingVariableBound : ∃ k : Key, ([key] : List Key)[0]? = some k ∧
    TypedElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] ((binderTy domains [] 0).subst anchor)) k.2.1 ∧
    k.2.1 (anchor 0) ∧ sets 0 = listSet k.2.2 := by
  exact bind_lead Ordered.empty (by trivial) anchorTyped (fun x hx => by
    obtain rfl : x = 0 := by simpa [domains] using hx
    rfl) (show 0 < domains.length by decide) (.cons actualKeyData .nil) keyDemands rfl

theorem fieldVariableBound : ∃ cl,
    .ctorArg 0 cl ∈ ctorObs constName [] [key] ∧
    TypedElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] ((binderTy domains [] 0).subst anchor)) cl ∧
    cl (anchor 0) ∧ ∀ k ∈ [tag], .ctorArgOb 0 [] k ∈ ctorObs constName [] [key] := by
  exact bind_field (doms := domains) (ls := []) (Lx := demands)
    (c := constName) (ℓs := []) Ordered.empty (by trivial) anchorTyped
    (show 0 < domains.length by decide) (.cons actualKeyData .nil) keyDemands rfl

end BindingControl

end ModelRuleSoundTest

namespace ModelRuleSoundAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VExpr.instL_mkApps,
    `Lean4Lean.VEnv.Model.forall₂_getElem_exists,
    `Lean4Lean.VExpr.instL_wrapForalls,
    `Lean4Lean.VExpr.wrapForalls_append,
    `Lean4Lean.VEnv.Model.bvar_eq_decidable,
    `Lean4Lean.VEnv.Model.bvar_mem_decidable,
    `Lean4Lean.VEnv.Model.natIndex,
    `Lean4Lean.VEnv.Model.nat_getElem?_index,
    `Lean4Lean.VEnv.Model.first_bvar_occurrence,
    `Lean4Lean.VEnv.Model.Obs.const_iff,
    `Lean4Lean.VEnv.Model.DomsSD.left,
    `Lean4Lean.VEnv.Model.TypeChain.tyCls_subst,
    `Lean4Lean.VEnv.Model.ctorObs,
    `Lean4Lean.VEnv.Model.ctorObs_end,
    `Lean4Lean.VEnv.Model.mem_ctorObs_head,
    `Lean4Lean.VEnv.Model.mem_ctorObs_arg,
    `Lean4Lean.VEnv.Model.mem_ctorObs_argOb,
    `Lean4Lean.VEnv.Model.pat_instL,
    `Lean4Lean.VEnv.Model.argDemand,
    `Lean4Lean.VEnv.Model.argDemand_ok,
    `Lean4Lean.VEnv.Model.closedN_wrapLams,
    `Lean4Lean.VEnv.Model.binderTy_closed,
    `Lean4Lean.VEnv.Model.HTS.wrapLams_body,
    `Lean4Lean.VEnv.Model.liftN_subst_shift,
    `Lean4Lean.VEnv.Model.wrap_le,
    `Lean4Lean.VEnv.Model.SubstEq.entry_typed,
    `Lean4Lean.VEnv.Model.bvar_dom_cls,
    `Lean4Lean.VEnv.Model.major_indicator_gen,
    `Lean4Lean.VEnv.Model.bind_lead,
    `Lean4Lean.VEnv.Model.bind_field,
    `Lean4Lean.VEnv.Model.pat_rhs_sub_head,
    `Lean4Lean.VEnv.Model.pat_rhs_sub,
    `Lean4Lean.VEnv.Model.pat_lhs_sub,
    `Lean4Lean.VEnv.Model.sound_pat,
    `Lean4Lean.VEnv.Model.RewriteMetadata.pattern_equation,
    `Lean4Lean.VEnv.Model.RewriteMetadata.quot_head_unique,
    `ModelRuleSoundTest.one,
    `ModelRuleSoundTest.two,
    `ModelRuleSoundTest.three,
    `ModelRuleSoundTest.altZero,
    `ModelRuleSoundTest.oneF,
    `ModelRuleSoundTest.twoF,
    `ModelRuleSoundTest.tag,
    `ModelRuleSoundTest.typeTag,
    `ModelRuleSoundTest.zeroEq,
    `ModelRuleSoundTest.distinctLevels,
    `ModelRuleSoundTest.betaType,
    `ModelRuleSoundTest.betaEquality,
    `ModelRuleSoundTest.distinctRepresentatives,
    `ModelRuleSoundTest.D1,
    `ModelRuleSoundTest.c1,
    `ModelRuleSoundTest.D2,
    `ModelRuleSoundTest.c2,
    `ModelRuleSoundTest.c1Typed,
    `ModelRuleSoundTest.betaMember,
    `ModelRuleSoundTest.c2Typed,
    `ModelRuleSoundTest.sortBacked,
    `ModelRuleSoundTest.k1,
    `ModelRuleSoundTest.k2,
    `ModelRuleSoundTest.keys,
    `ModelRuleSoundTest.doms,
    `ModelRuleSoundTest.endType,
    `ModelRuleSoundTest.piType,
    `ModelRuleSoundTest.lambdaTerm,
    `ModelRuleSoundTest.σ1,
    `ModelRuleSoundTest.σ2,
    `ModelRuleSoundTest.S1,
    `ModelRuleSoundTest.S2,
    `ModelRuleSoundTest.cv,
    `ModelRuleSoundTest.lambdaTyped,
    `ModelRuleSoundTest.firstKeyTyped,
    `ModelRuleSoundTest.secondDomainObserved,
    `ModelRuleSoundTest.secondKeyTyped,
    `ModelRuleSoundTest.telescopeKeys,
    `ModelRuleSoundTest.twoKeys,
    `ModelRuleSoundTest.lambdaObserved,
    `ModelRuleSoundTest.telescopeCodomain,
    `ModelRuleSoundTest.codomainObserved,
    `ModelRuleSoundTest.wrappedTyped,
    `ModelRuleSoundTest.domainSD,
    `ModelRuleSoundTest.bodySD,
    `ModelRuleSoundTest.innerPiSD,
    `ModelRuleSoundTest.telescopeSD,
    `ModelRuleSoundTest.piTypeSD,
    `ModelRuleSoundTest.lambdaSD,
    `ModelRuleSoundTest.lambdaHTS,
    `ModelRuleSoundTest.piTypeHTS,
    `ModelRuleSoundTest.derivedPiSoundness,
    `ModelRuleSoundTest.extendedTyped,
    `ModelRuleSoundTest.typeLevel,
    `ModelRuleSoundTest.delayedPi,
    `ModelRuleSoundTest.delayStrong,
    `ModelRuleSoundTest.convertedLambdaStrong,
    `ModelRuleSoundTest.convertedLambdaSound,
    `ModelRuleSoundTest.lambdaThroughConversion,
    `ModelRuleSoundTest.distinctPiTypes,
    `ModelRuleSoundTest.constName,
    `ModelRuleSoundTest.constValue,
    `ModelRuleSoundTest.constEnv,
    `ModelRuleSoundTest.constEnvWF,
    `ModelRuleSoundTest.emptyLE,
    `ModelRuleSoundTest.noRules,
    `ModelRuleSoundTest.constLookup,
    `ModelRuleSoundTest.constantStrong,
    `ModelRuleSoundTest.betaStrong,
    `ModelRuleSoundTest.betaReflStrong,
    `ModelRuleSoundTest.resultPiStrong,
    `ModelRuleSoundTest.firstApplicationStrong,
    `ModelRuleSoundTest.source,
    `ModelRuleSoundTest.sourceAtBeta,
    `ModelRuleSoundTest.sourceStrong,
    `ModelRuleSoundTest.sourceSound,
    `ModelRuleSoundTest.betaObserved,
    `ModelRuleSoundTest.demands,
    `ModelRuleSoundTest.demandedArguments,
    `ModelRuleSoundTest.extracted,
    `ModelRuleSoundTest.spineRoundtrip,
    `ModelRuleSoundTest.sourceObserved,
    `ModelRuleSoundTest.finiteBinderLists,
    `ModelRuleSoundTest.splitDependent,
    `ModelRuleSoundTest.outerAnchor,
    `ModelRuleSoundTest.dependentBinderLookup,
    `ModelRuleSoundTest.dependentDomainSound,
    `ModelRuleSoundTest.canonicalAnchor,
    `ModelRuleSoundTest.differentAnchors,
    `ModelRuleSoundTest.sameOutside,
    `ModelRuleSoundTest.relatedAnchors,
    `ModelRuleSoundTest.soundBinderContext,
    `ModelRuleSoundTest.transferredValuation,
    `ModelRuleSoundTest.transferredHeadTyped,
    `ModelRuleSoundTest.rigidSpineObserved,
    `ModelRuleSoundTest.recoveredSpine,
    `ModelRuleSoundTest.backedAndCoveredKeys,
    `ModelRuleSoundTest.rejectsWrongConstructorHead,
    `ModelRuleSoundTest.patternRoundtrip,
    `ModelRuleSoundTest.QuotControl.base,
    `ModelRuleSoundTest.QuotControl.env,
    `ModelRuleSoundTest.QuotControl.wf,
    `ModelRuleSoundTest.QuotControl.α,
    `ModelRuleSoundTest.QuotControl.proposition,
    `ModelRuleSoundTest.QuotControl.relation,
    `ModelRuleSoundTest.QuotControl.relationType,
    `ModelRuleSoundTest.QuotControl.propositionTyped,
    `ModelRuleSoundTest.QuotControl.relationTyped,
    `ModelRuleSoundTest.QuotControl.domains,
    `ModelRuleSoundTest.QuotControl.result,
    `ModelRuleSoundTest.QuotControl.anchor1,
    `ModelRuleSoundTest.QuotControl.anchor2,
    `ModelRuleSoundTest.QuotControl.anchor3,
    `ModelRuleSoundTest.QuotControl.sets1,
    `ModelRuleSoundTest.QuotControl.sets2,
    `ModelRuleSoundTest.QuotControl.sets3,
    `ModelRuleSoundTest.QuotControl.domain1,
    `ModelRuleSoundTest.QuotControl.class1,
    `ModelRuleSoundTest.QuotControl.domain2,
    `ModelRuleSoundTest.QuotControl.class2,
    `ModelRuleSoundTest.QuotControl.domain3,
    `ModelRuleSoundTest.QuotControl.class3,
    `ModelRuleSoundTest.QuotControl.key1,
    `ModelRuleSoundTest.QuotControl.key2,
    `ModelRuleSoundTest.QuotControl.key3,
    `ModelRuleSoundTest.QuotControl.class1Typed,
    `ModelRuleSoundTest.QuotControl.class2Typed,
    `ModelRuleSoundTest.QuotControl.class3Typed,
    `ModelRuleSoundTest.QuotControl.constructorKeys,
    `ModelRuleSoundTest.QuotControl.familyKeys,
    `ModelRuleSoundTest.QuotControl.wrapTyped,
    `ModelRuleSoundTest.QuotControl.familyRigid,
    `ModelRuleSoundTest.QuotControl.familyHeadObserved,
    `ModelRuleSoundTest.QuotControl.resultObserved,
    `ModelRuleSoundTest.QuotControl.family,
    `ModelRuleSoundTest.QuotControl.installed,
    `ModelRuleSoundTest.QuotControl.constructorHeadObserved,
    `ModelRuleSoundTest.QuotControl.constructorInverted,
    `ModelRuleSoundTest.QuotControl.constructorTyped,
    `ModelRuleSoundTest.QuotControl.constructorFieldObserved,
    `ModelRuleSoundTest.QuotControl.constructorFieldRecovered,
    `ModelRuleSoundTest.QuotControl.quotientRegistered,
    `ModelRuleSoundTest.QuotControl.quotientHeadUnique,
    `ModelRuleSoundTest.QuotControl.lambdaDomains,
    `ModelRuleSoundTest.QuotControl.actualPatternClassified,
    `ModelRuleSoundTest.QuotControl.allConstructorDemandsObserved,
    `ModelRuleSoundTest.firstDuplicateOccurrence,
    `ModelRuleSoundTest.firstDuplicateIsOne,
    `ModelRuleSoundTest.missingVariableDecision,
    `ModelRuleSoundTest.finiteConstructorDemands,
    `ModelRuleSoundTest.BindingControl.domains,
    `ModelRuleSoundTest.BindingControl.anchor,
    `ModelRuleSoundTest.BindingControl.sets,
    `ModelRuleSoundTest.BindingControl.D,
    `ModelRuleSoundTest.BindingControl.c,
    `ModelRuleSoundTest.BindingControl.key,
    `ModelRuleSoundTest.BindingControl.demands,
    `ModelRuleSoundTest.BindingControl.anchorTyped,
    `ModelRuleSoundTest.BindingControl.variableStrong,
    `ModelRuleSoundTest.BindingControl.variableSound,
    `ModelRuleSoundTest.BindingControl.actualKeyData,
    `ModelRuleSoundTest.BindingControl.keyDemands,
    `ModelRuleSoundTest.BindingControl.leadingVariableBound,
    `ModelRuleSoundTest.BindingControl.fieldVariableBound]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VExpr.instL_mkApps, [`propext]),
    (`Lean4Lean.VEnv.Model.forall₂_getElem_exists, [`propext]),
    (`Lean4Lean.VExpr.instL_wrapForalls, [`propext]),
    (`Lean4Lean.VExpr.wrapForalls_append, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.bvar_eq_decidable, []),
    (`Lean4Lean.VEnv.Model.bvar_mem_decidable, [`propext]),
    (`Lean4Lean.VEnv.Model.natIndex, []),
    (`Lean4Lean.VEnv.Model.nat_getElem?_index, [`propext]),
    (`Lean4Lean.VEnv.Model.first_bvar_occurrence, [`propext]),
    (`Lean4Lean.VEnv.Model.Obs.const_iff, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.left, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypeChain.tyCls_subst, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.ctorObs, [`propext]),
    (`Lean4Lean.VEnv.Model.ctorObs_end, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mem_ctorObs_head, [`propext]),
    (`Lean4Lean.VEnv.Model.mem_ctorObs_arg, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.mem_ctorObs_argOb, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pat_instL, [`propext]),
    (`Lean4Lean.VEnv.Model.argDemand, [`propext]),
    (`Lean4Lean.VEnv.Model.argDemand_ok, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.closedN_wrapLams, [`propext]),
    (`Lean4Lean.VEnv.Model.binderTy_closed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.wrapLams_body, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.liftN_subst_shift, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrap_le, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SubstEq.entry_typed, [`propext]),
    (`Lean4Lean.VEnv.Model.bvar_dom_cls, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.major_indicator_gen, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.bind_lead, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.bind_field, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pat_rhs_sub_head, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pat_rhs_sub, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.pat_lhs_sub, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.sound_pat, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RewriteMetadata.pattern_equation, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RewriteMetadata.quot_head_unique, [`propext]),
    (`ModelRuleSoundTest.one, []),
    (`ModelRuleSoundTest.two, []),
    (`ModelRuleSoundTest.three, []),
    (`ModelRuleSoundTest.altZero, []),
    (`ModelRuleSoundTest.oneF, []),
    (`ModelRuleSoundTest.twoF, []),
    (`ModelRuleSoundTest.tag, []),
    (`ModelRuleSoundTest.typeTag, []),
    (`ModelRuleSoundTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.distinctLevels, []),
    (`ModelRuleSoundTest.betaType, []),
    (`ModelRuleSoundTest.betaEquality, [`propext]),
    (`ModelRuleSoundTest.distinctRepresentatives, []),
    (`ModelRuleSoundTest.D1, [`propext]),
    (`ModelRuleSoundTest.c1, [`propext]),
    (`ModelRuleSoundTest.D2, [`propext]),
    (`ModelRuleSoundTest.c2, [`propext]),
    (`ModelRuleSoundTest.c1Typed, [`propext]),
    (`ModelRuleSoundTest.betaMember, [`propext]),
    (`ModelRuleSoundTest.c2Typed, [`propext]),
    (`ModelRuleSoundTest.sortBacked, [`propext]),
    (`ModelRuleSoundTest.k1, [`propext]),
    (`ModelRuleSoundTest.k2, [`propext]),
    (`ModelRuleSoundTest.keys, [`propext]),
    (`ModelRuleSoundTest.doms, []),
    (`ModelRuleSoundTest.endType, []),
    (`ModelRuleSoundTest.piType, []),
    (`ModelRuleSoundTest.lambdaTerm, []),
    (`ModelRuleSoundTest.σ1, []),
    (`ModelRuleSoundTest.σ2, []),
    (`ModelRuleSoundTest.S1, []),
    (`ModelRuleSoundTest.S2, []),
    (`ModelRuleSoundTest.cv, [`propext]),
    (`ModelRuleSoundTest.lambdaTyped, [`propext]),
    (`ModelRuleSoundTest.firstKeyTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.secondDomainObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.secondKeyTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.telescopeKeys, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.twoKeys, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.lambdaObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.telescopeCodomain, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.codomainObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.wrappedTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.domainSD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.bodySD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.telescopeSD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.piTypeSD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.lambdaSD, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.lambdaHTS, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.piTypeHTS, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.derivedPiSoundness, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.extendedTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.typeLevel, []),
    (`ModelRuleSoundTest.delayedPi, []),
    (`ModelRuleSoundTest.delayStrong, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.convertedLambdaStrong, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.convertedLambdaSound, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.lambdaThroughConversion, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.distinctPiTypes, []),
    (`ModelRuleSoundTest.constName, []),
    (`ModelRuleSoundTest.constValue, []),
    (`ModelRuleSoundTest.constEnv, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.constEnvWF, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.emptyLE, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.noRules, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.constLookup, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.constantStrong, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.betaStrong, [`propext]),
    (`ModelRuleSoundTest.betaReflStrong, [`propext]),
    (`ModelRuleSoundTest.resultPiStrong, [`propext]),
    (`ModelRuleSoundTest.firstApplicationStrong, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.source, []),
    (`ModelRuleSoundTest.sourceAtBeta, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.sourceStrong, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.sourceSound, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.demands, []),
    (`ModelRuleSoundTest.demandedArguments, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.extracted, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.spineRoundtrip, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.sourceObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.finiteBinderLists, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.splitDependent, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.outerAnchor, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.dependentBinderLookup, [`propext]),
    (`ModelRuleSoundTest.dependentDomainSound, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.canonicalAnchor, []),
    (`ModelRuleSoundTest.differentAnchors, []),
    (`ModelRuleSoundTest.sameOutside, [`propext]),
    (`ModelRuleSoundTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.soundBinderContext, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.transferredValuation, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.transferredHeadTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.rigidSpineObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.recoveredSpine, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.backedAndCoveredKeys, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.rejectsWrongConstructorHead, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.patternRoundtrip, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.base, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.env, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.wf, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.α, []),
    (`ModelRuleSoundTest.QuotControl.proposition, []),
    (`ModelRuleSoundTest.QuotControl.relation, []),
    (`ModelRuleSoundTest.QuotControl.relationType, []),
    (`ModelRuleSoundTest.QuotControl.propositionTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.relationTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.domains, []),
    (`ModelRuleSoundTest.QuotControl.result, []),
    (`ModelRuleSoundTest.QuotControl.anchor1, []),
    (`ModelRuleSoundTest.QuotControl.anchor2, []),
    (`ModelRuleSoundTest.QuotControl.anchor3, []),
    (`ModelRuleSoundTest.QuotControl.sets1, []),
    (`ModelRuleSoundTest.QuotControl.sets2, []),
    (`ModelRuleSoundTest.QuotControl.sets3, []),
    (`ModelRuleSoundTest.QuotControl.domain1, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class1, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.domain2, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class2, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.domain3, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class3, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.key1, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.key2, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.key3, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class1Typed, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class2Typed, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.class3Typed, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorKeys, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.familyKeys, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.wrapTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.familyRigid, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.familyHeadObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.resultObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.family, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.installed, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorHeadObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorInverted, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorTyped, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorFieldObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.constructorFieldRecovered, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.quotientRegistered, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.quotientHeadUnique, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.lambdaDomains, [`propext]),
    (`ModelRuleSoundTest.QuotControl.actualPatternClassified, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.QuotControl.allConstructorDemandsObserved, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.firstDuplicateOccurrence, [`propext]),
    (`ModelRuleSoundTest.firstDuplicateIsOne, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.missingVariableDecision, [`propext]),
    (`ModelRuleSoundTest.finiteConstructorDemands, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.BindingControl.domains, []),
    (`ModelRuleSoundTest.BindingControl.anchor, []),
    (`ModelRuleSoundTest.BindingControl.sets, []),
    (`ModelRuleSoundTest.BindingControl.D, [`propext]),
    (`ModelRuleSoundTest.BindingControl.c, [`propext]),
    (`ModelRuleSoundTest.BindingControl.key, [`propext]),
    (`ModelRuleSoundTest.BindingControl.demands, []),
    (`ModelRuleSoundTest.BindingControl.anchorTyped, [`propext]),
    (`ModelRuleSoundTest.BindingControl.variableStrong, [`propext]),
    (`ModelRuleSoundTest.BindingControl.variableSound, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.BindingControl.actualKeyData, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.BindingControl.keyDemands, [`propext]),
    (`ModelRuleSoundTest.BindingControl.leadingVariableBound, [`Quot.sound, `propext]),
    (`ModelRuleSoundTest.BindingControl.fieldVariableBound, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-rulesound manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-rulesound manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-rulesound axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-rulesound admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-rulesound value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-rulesound dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-rulesound type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-rulesound admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-rulesound dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-rulesound traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-rulesound axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.Obs.const_iff then [`Lean4Lean.VEnv.Model.Obs.rule, `Lean4Lean.VEnv.Model.Obs.ctor, `Lean4Lean.VEnv.Model.Obs.delta, `Lean4Lean.VEnv.Model.Obs.const, `Lean4Lean.VEnv.Model.RuleBind]
      else if root == `Lean4Lean.VEnv.Model.nat_getElem?_index then [`Lean4Lean.VEnv.Model.natIndex]
      else if root == `Lean4Lean.VEnv.Model.bvar_mem_decidable then [`Lean4Lean.VEnv.Model.bvar_eq_decidable]
      else if root == `Lean4Lean.VEnv.Model.first_bvar_occurrence then [`Lean4Lean.VEnv.Model.bvar_eq_decidable]
      else if root == `Lean4Lean.VEnv.Model.major_indicator_gen then [`Lean4Lean.VEnv.Model.tele_unwind, `Lean4Lean.VEnv.Model.HTS.tele_dom, `Lean4Lean.VEnv.Model.spine_rigid_obs, `Lean4Lean.VEnv.Model.tele_obs]
      else if root == `Lean4Lean.VEnv.Model.bind_lead then [`Lean4Lean.VEnv.Model.lookup_binderTy, `Lean4Lean.VEnv.Model.bvar_dom_cls, `Lean4Lean.VEnv.Model.KeyData, `Lean4Lean.VEnv.Model.forall₂_getElem_exists]
      else if root == `Lean4Lean.VEnv.Model.bind_field then [`Lean4Lean.VEnv.Model.lookup_binderTy, `Lean4Lean.VEnv.Model.bvar_dom_cls, `Lean4Lean.VEnv.Model.mem_ctorObs_arg, `Lean4Lean.VEnv.Model.mem_ctorObs_argOb]
      else if root == `Lean4Lean.VEnv.Model.pat_rhs_sub_head then [`Lean4Lean.VEnv.Model.TeleKeys.inner_lists, `Lean4Lean.VEnv.Model.HTS.spineH, `Lean4Lean.VEnv.Model.HTS.lamSpine, `Lean4Lean.VEnv.Model.major_indicator_gen, `Lean4Lean.VEnv.Model.bind_lead, `Lean4Lean.VEnv.Model.bind_field, `Lean4Lean.VEnv.Model.ctorObs_end, `Lean4Lean.VEnv.Model.Obs.ctor, `Lean4Lean.VEnv.QuotPropReduction.zeroLike_iff, `Lean4Lean.VEnv.Model.nat_getElem?_index, `Lean4Lean.VEnv.Model.bvar_mem_decidable, `Lean4Lean.VEnv.Model.first_bvar_occurrence]
      else if root == `Lean4Lean.VEnv.Model.pat_rhs_sub then [`Lean4Lean.VEnv.Model.pat_rhs_sub_head, `Lean4Lean.VEnv.Model.Obs.rule, `Lean4Lean.VEnv.Model.pat_instL, `Lean4Lean.VEnv.Model.HeadTy]
      else if root == `Lean4Lean.VEnv.Model.pat_lhs_sub then [`Lean4Lean.VEnv.Model.Obs.const_iff, `Lean4Lean.VEnv.Model.ctor_spine_inv, `Lean4Lean.VEnv.Model.wrapLams_pat_inj, `Lean4Lean.VEnv.Model.SubstEq.of_heads_ind, `Lean4Lean.VEnv.Model.TV.transfer, `Lean4Lean.VEnv.Model.DomsSD.ctxSD, `Lean4Lean.VEnv.Model.TypedElCls.defeq, `Lean4Lean.VEnv.IsDefEq.proofIrrel, `Lean4Lean.VEnv.Model.Obs.mono_le]
      else if root == `Lean4Lean.VEnv.Model.sound_pat then [`Lean4Lean.VEnv.Model.pat_lhs_sub, `Lean4Lean.VEnv.Model.pat_rhs_sub, `Lean4Lean.VEnv.Model.Obs.closed_iff_id]
      else if root == `Lean4Lean.VEnv.Model.RewriteMetadata.pattern_equation then [`Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VEnv.Model.wrapLams_mkApps_ne_const]
      else if root == `Lean4Lean.VEnv.Model.RewriteMetadata.quot_head_unique then [`Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VEnv.RewriteMetadata.quotientNames]
      else if root == `ModelRuleSoundTest.QuotControl.quotientHeadUnique then [`Lean4Lean.VEnv.Model.RewriteMetadata.quot_head_unique, `Lean4Lean.VEnv.WF.rewriteMetadata, `ModelRuleSoundTest.QuotControl.quotientRegistered]
      else if root == `ModelRuleSoundTest.QuotControl.actualPatternClassified then [`Lean4Lean.VEnv.Model.RewriteMetadata.pattern_equation, `ModelRuleSoundTest.QuotControl.quotientRegistered]
      else if root == `ModelRuleSoundTest.QuotControl.allConstructorDemandsObserved then [`Lean4Lean.VEnv.Model.ctorObs_end, `Lean4Lean.VEnv.Model.Obs.ctor, `ModelRuleSoundTest.QuotControl.constructorKeys, `ModelRuleSoundTest.QuotControl.resultObserved]
      else if root == `ModelRuleSoundTest.firstDuplicateIsOne then [`Lean4Lean.VEnv.Model.first_bvar_occurrence]
      else if root == `ModelRuleSoundTest.missingVariableDecision then [`Lean4Lean.VEnv.Model.bvar_mem_decidable]
      else if root == `ModelRuleSoundTest.finiteConstructorDemands then [`Lean4Lean.VEnv.Model.mem_ctorObs_argOb, `Lean4Lean.VEnv.Model.mem_ctorObs_arg, `Lean4Lean.VEnv.Model.mem_ctorObs_head]
      else if root == `ModelRuleSoundTest.BindingControl.actualKeyData then [`ModelRuleSoundTest.BindingControl.variableStrong, `Lean4Lean.VEnv.Model.sound_no_rules, `Lean4Lean.VEnv.Model.KeyData]
      else if root == `ModelRuleSoundTest.BindingControl.leadingVariableBound then [`Lean4Lean.VEnv.Model.bind_lead, `ModelRuleSoundTest.BindingControl.actualKeyData, `ModelRuleSoundTest.BindingControl.anchorTyped]
      else if root == `ModelRuleSoundTest.BindingControl.fieldVariableBound then [`Lean4Lean.VEnv.Model.bind_field, `ModelRuleSoundTest.BindingControl.actualKeyData, `Lean4Lean.VEnv.Model.mem_ctorObs_argOb, `ModelRuleSoundTest.BindingControl.anchorTyped]
      else []
    unless required.all visited.contains do
      throwError "model-rulesound proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelRuleSoundAudit
