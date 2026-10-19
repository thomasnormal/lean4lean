import Lean4Lean.Theory.Typing.HeadInjectivity.Model.TeleWind
import Lean.Util.CollectAxioms

namespace ModelSpineTeleTest
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

-- Reverse transfer consumes the actual conversion of sourceAtBeta to sourceStrong.
theorem reverseResult : ∃ ks : List Key,
    ChainArgs constEnv 0 [] .id .empty ks [betaType, .sort .zero] ∧
    ks.length = 2 ∧ Obs constEnv 0 [] .id .empty piType (piCodChain ks typeTag) := by
  obtain ⟨Th, As, hTh, _, hlen, _, hrev⟩ :=
    sourceSound.2.spineRev constEnvWF.ordered (by trivial) rfl ⟨constName, [], rfl⟩ .nil TV.empty
  obtain ⟨_, _, ci, he, hci, _, rfl⟩ := hTh
  cases he
  cases constLookup.symm.trans hci
  obtain ⟨ks, o, hk, ho, hl⟩ := hrev typeTag Obs.sort
  cases hl.sort_inv
  exact ⟨ks, hk, hk.length, ho⟩

-- Each actual argument retains its Strong typing and its domain-class/type observations.
theorem reverseDependentDomain : ∃ A,
    SD constEnv 0 [] [] (.sort .zero) (.sort .zero) A ∧
    (∃ ks, ChainArgs constEnv 0 [] .id .empty ks [betaType] ∧
      Obs constEnv 0 [] .id .empty piType
        (piCodChain ks (.piDom (TyCls constEnv 0 [] (A.subst .id))))) ∧
    ∀ x, Obs constEnv 0 [] .id .empty A x →
      ∃ ks x', ChainArgs constEnv 0 [] .id .empty ks [betaType] ∧
        Obs constEnv 0 [] .id .empty piType (piCodChain ks (.piDomOb x')) ∧ x' ≼ x := by
  obtain ⟨Th, As, hTh, _, hlen, hdom, _⟩ :=
    sourceSound.2.spineRev constEnvWF.ordered (by trivial) rfl ⟨constName, [], rfl⟩ .nil TV.empty
  obtain ⟨_, _, ci, he, hci, _, rfl⟩ := hTh
  cases he
  cases constLookup.symm.trans hci
  have hi : 1 < As.length := by simp at hlen; omega
  exact ⟨As[1], hdom 1 As[1] (.sort .zero) (List.getElem?_eq_getElem hi) rfl⟩

theorem storedPiSD : PiSD constEnv 0 [] [] doms endType :=
  (sound_no_rules constEnvWF.ordered (by trivial) emptyLE
    (fun _ h => h.elim) piTypeSD.1).2.1.piSD

def arguments : List VExpr := [betaType, .sort .zero]
def argumentAnchor : VExpr.Subst := VExpr.argSubst arguments
def argumentSets : ObSets := argSets constEnv 0 [] .id .empty arguments

theorem argumentsTyped : Ctx.SubstEq constEnv 0 [] argumentAnchor argumentAnchor doms.reverse ∧
    TV constEnv 0 [] doms.reverse argumentAnchor argumentSets :=
  spine_tele constEnvWF.ordered (by trivial) sourceSound.2 .nil TV.empty constLookup (Dw := doms) (Rw := endType)
    (fun o h => ⟨o, h, .refl⟩) storedPiSD (by decide)

theorem prefixTyped : Ctx.SubstEq constEnv 0 [] (VExpr.argSubst [betaType])
    (VExpr.argSubst [betaType]) [.sort two] ∧
    TV constEnv 0 [] [.sort two] (VExpr.argSubst [betaType])
      (argSets constEnv 0 [] .id .empty [betaType]) :=
  spine_tele_prefix constEnvWF.ordered (by trivial) sourceSound.2 .nil TV.empty constLookup (Dw := doms) (Rw := endType)
    (fun o h => ⟨o, h, .refl⟩) storedPiSD (by decide) 1 (by decide)

theorem partialSpineTyped : Ctx.SubstEq constEnv 0 [] (VExpr.argSubst [betaType])
    (VExpr.argSubst [betaType]) [.sort two] ∧
    TV constEnv 0 [] [.sort two] (VExpr.argSubst [betaType])
      (argSets constEnv 0 [] .id .empty [betaType]) := by
  have H := sound_no_rules (Δ := []) constEnvWF.ordered (by trivial) VEnv.LE.rfl noRules firstApplicationStrong
  exact spine_tele (ls := []) (args := [betaType]) constEnvWF.ordered (by trivial) H.2.1 .nil TV.empty constLookup (Dw := doms) (Rw := endType)
    (fun o h => ⟨o, h, .refl⟩) storedPiSD (by decide)

theorem domainsClosed (i : Nat) (hi : i < doms.length) : (doms[i]).ClosedN i := by
  cases i with
  | zero => trivial
  | succ i => cases i with
    | zero => exact Nat.zero_lt_succ 0
    | succ i => change i + 1 + 1 < 2 at hi; exfalso; omega

-- Only the inner argument is demanded explicitly; its dependent type will force an earlier demand.
def innerDemand : List (List Ob) := [[], [tag]]

theorem demandCovered (i : Nat) (Fi : List Ob) (hi : innerDemand[i]? = some Fi)
    (o : Ob) (ho : o ∈ Fi) : argumentSets (doms.length - 1 - i) o := by
  cases i with
  | zero => cases hi; cases ho
  | succ i => cases i with
    | zero => cases hi; cases List.mem_singleton.1 ho; exact Obs.sort
    | succ i => simp [innerDemand] at hi

-- The full result retains original demand, backing, dependent classes and a pointwise subset.
theorem finiteDependentKeys : ∃ (ks : List Key) (S' : ObSets),
    TeleKeys constEnv 0 [] .id .empty doms ks argumentAnchor S' ∧ ks.length = doms.length ∧
    (∀ m k, ks[doms.length - 1 - m]? = some k → m < doms.length → ∀ o, S' m o ↔ o ∈ k.2.2) ∧
    ∀ i k, ks[i]? = some k →
      (∀ Fi, innerDemand[i]? = some Fi → ∀ y ∈ Fi, y ∈ k.2.2) ∧
      (∀ y ∈ k.2.2, argumentSets (doms.length - 1 - i) y) ∧
      ∃ a A, arguments[i]? = some a ∧ doms[i]? = some A ∧
        k.2.1 = ElCls constEnv 0 [] (TyCls constEnv 0 []
          (A.subst (VExpr.argSubst (arguments.take i)))) a :=
  tele_compact (D := doms) (as := arguments) domainsClosed rfl argumentsTyped.1 argumentsTyped.2 innerDemand rfl demandCovered

-- A nonempty first key is discovered from typing the inner demand, despite F[0] = [].
theorem discoversDependentDemand : ∃ (k₁ k₂ : Key) (S' : ObSets),
    TeleKeys constEnv 0 [] .id .empty doms [k₁, k₂] argumentAnchor S' ∧
    typeTag ∈ k₁.2.2 ∧ tag ∈ k₂.2.2 := by
  obtain ⟨ks, S', hT, hlen, hsets, hk⟩ := finiteDependentKeys
  cases ks with
  | nil => cases hlen
  | cons k₁ ks => cases ks with
    | nil => cases hlen
    | cons k₂ rest =>
      have hr : rest = [] := List.length_eq_zero_iff.1 (Nat.succ.inj (Nat.succ.inj hlen))
      subst hr
      have htag := (hk 1 _ rfl).1 [tag] rfl tag (.head _)
      refine ⟨k₁, k₂, S', hT, ?_, htag⟩
      generalize hv : argumentAnchor = v at hT
      clear hv
      cases hT with
      | cons hc₁ hy₁ hK₁ hb₁ hT => cases hT with
        | cons hc₂ hy₂ hK₂ hb₂ hT => cases hT with
          | nil =>
            obtain ⟨τs, hτ, hty⟩ := hK₂ tag htag
            cases hty with
            | sort hm => exact Obs.bvar_iff.1 (hτ _ hm)

theorem finiteLambdaObservation : ∃ ks,
    Obs constEnv 0 [] .id .empty lambdaTerm (wrap ks tag) ∧
    ∃ k₁ k₂, ks = [k₁, k₂] ∧ typeTag ∈ k₁.2.2 ∧ tag ∈ k₂.2.2 := by
  obtain ⟨k₁, k₂, S', hT, hfirst, hlast⟩ := discoversDependentDemand
  have hout : S' 0 = listSet k₂.2.2 := by
    have hcopy := hT
    generalize hv : argumentAnchor = v at hcopy
    clear hv
    cases hcopy with | cons _ _ _ _ hT => cases hT with | cons _ _ _ _ hT => cases hT; rfl
  refine ⟨[k₁, k₂], Obs.wrapLams_iff.2 ⟨_, _, _, _, hT, rfl, .bvar ?_⟩,
    k₁, k₂, rfl, hfirst, hlast⟩
  rw [hout]; exact hlast

-- Compact all free observation sets of a term while retaining a positive outer-variable observation.
def openTerm : VExpr := .forallE (.bvar 1) (.bvar 1)
def openObservation : Ob := .piDomOb typeTag

theorem openTermObserved : Obs VEnv.empty 0 [] σ2 S2 openTerm openObservation :=
  .piDomOb (.bvar (.head _))

theorem allVariableCompact : ∃ (G : List (List Ob)) (K : List Ob), G.length = 2 ∧
    G[1]? = some K ∧ typeTag ∈ K ∧ Obs VEnv.empty 0 [] σ2 (fillS .empty G) openTerm openObservation := by
  obtain ⟨G, hlen, hsub, hG⟩ := Obs.compact_all
    (show openTerm.ClosedN 2 from ⟨(by decide : 1 < 2), (by decide : 1 < 3)⟩)
    (τs := [openObservation]) (fun τ hτ => by cases List.mem_singleton.1 hτ; exact openTermObserved)
  have hobs : Obs VEnv.empty 0 [] σ2 (fillS .empty G) openTerm openObservation :=
    hG _ (fun m hm y hy => by simp only [fillS, dif_pos hm]; exact hy) _ (.head _)
  have hm : 1 < G.length := by omega
  have hpositive := Obs.bvar_iff.1 (Obs.piDomOb_mem hobs)
  change fillS .empty G 1 typeTag at hpositive
  rw [fillS, dif_pos hm] at hpositive
  exact ⟨G, G[1], hlen, List.getElem?_eq_getElem hm, hpositive, hobs⟩

-- A typed telescope may choose a different representative from the one in its anchor.
theorem representativeReplacement : Ctx.SubstEq VEnv.empty 0 [] σ2
    (VExpr.argSubst [.sort one, .sort .zero]) doms.reverse :=
  telescopeKeys.substEq .empty (by trivial) derivedPiSoundness.doms .nil
    (.cons ElCls.self (.cons ElCls.self .nil))

theorem keyObservationCoverage : ∀ m o, extS .empty keys m o →
    ∃ o', argSets VEnv.empty 0 [] .id .empty [.sort one, .sort .zero] m o' ∧ o' ≼ o := by
  apply extS_cover
  refine .cons ?_ (.cons ?_ .nil)
  · intro y hy
    cases List.mem_singleton.1 hy
    exact ⟨typeTag, .sort, .refl⟩
  · intro y hy
    cases List.mem_singleton.1 hy
    exact ⟨tag, .sort, .refl⟩

-- Winding consumes actual head typing and returns typing at the class of the actual application.
theorem windFiniteHead : ∃ ks,
    Obs constEnv 0 [] .id .empty (.const constName [])
      (wrap ks (.rigid constName [] 2 oneF)) ∧
    ∃ k₁ k₂, ks = [k₁, k₂] ∧ typeTag ∈ k₁.2.2 ∧ tag ∈ k₂.2.2 := by
  obtain ⟨k₁, k₂, S', hT, hfirst, hlast⟩ := discoversDependentDemand
  obtain ⟨ys, he, hlen, hmembers, happ, wind⟩ :=
    tele_wind (R := endType) constEnvWF.ordered (by trivial) hT (.const constName [])
      constantStrong.defeq.hasType.1
  have heq : arguments = ys := argSubst_inj hlen.symm he
  subst ys
  have hR : Obs constEnv 0 [] argumentAnchor S' endType typeTag := by
    generalize hv : argumentAnchor = v at hT
    clear hv
    cases hT with
    | cons _ _ _ _ hT => cases hT with | cons _ _ _ _ hT => cases hT; exact .bvar hfirst
  obtain ⟨τ₀, hτ₀, ht⟩ := wind (.rigid constName [] 2 oneF) [typeTag]
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact hR) (.rigid (.head _))
  exact ⟨[k₁, k₂], .const (fun df h => (noRules df h).elim) constLookup
    hτ₀ ht (.inl ⟨oneF, rfl⟩), k₁, k₂, rfl, hfirst, hlast⟩

end ModelSpineTeleTest


namespace ModelSpineTeleAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.ChainArgs,
    `Lean4Lean.VEnv.Model.ChainArgs.append,
    `Lean4Lean.VEnv.Model.ChainArgs.length,
    `Lean4Lean.VEnv.Model.HTS.spineRev,
    `Lean4Lean.VExpr.argSubst,
    `Lean4Lean.VExpr.argSubst_append_one,
    `Lean4Lean.VExpr.foldl_cons_apply,
    `Lean4Lean.VExpr.argSubst_lt,
    `Lean4Lean.List.exists_snoc_of_length_succ,
    `Lean4Lean.VEnv.Model.fillS,
    `Lean4Lean.VEnv.Model.Obs.compact_all,
    `Lean4Lean.VEnv.Model.TV.cons_inv,
    `Lean4Lean.VEnv.Model.TeleKeys.snoc,
    `Lean4Lean.VEnv.Model.tele_compact_aux,
    `Lean4Lean.VEnv.Model.tele_compact,
    `Lean4Lean.VEnv.Model.argSets,
    `Lean4Lean.VEnv.Model.argSets_snoc,
    `Lean4Lean.VEnv.Model.extS,
    `Lean4Lean.VEnv.Model.extS_snoc,
    `Lean4Lean.VExpr.argSubst_ge,
    `Lean4Lean.VEnv.Model.Le.piCodChain_inv,
    `Lean4Lean.VEnv.Model.tele_split,
    `Lean4Lean.VEnv.Model.TeleKeys.substEq,
    `Lean4Lean.VEnv.Model.DomsSD.take_getElem,
    `Lean4Lean.VEnv.Model.DomsSD.take,
    `Lean4Lean.VEnv.Model.TV.cons_set,
    `Lean4Lean.VEnv.Model.forall₂_comp_cover,
    `Lean4Lean.VEnv.Model.List.reverseRecOn,
    `Lean4Lean.VEnv.Model.forall₂_snoc_inv,
    `Lean4Lean.VEnv.Model.extS_cover,
    `Lean4Lean.VEnv.Model.forall₂_cls,
    `Lean4Lean.VEnv.Model.spine_tele_prefix,
    `Lean4Lean.VEnv.Model.spine_tele,
    `Lean4Lean.VEnv.Model.argSubst_inj,
    `Lean4Lean.VEnv.Model.typed_wrap_rigid,
    `Lean4Lean.VEnv.Model.Ob.Le.piCodChain_sort_inv,
    `Lean4Lean.VEnv.Model.obs_wrapForalls_sort,
    `Lean4Lean.VEnv.Model.appCls_eq,
    `Lean4Lean.VEnv.Model.tele_wind,
    `ModelSpineTeleTest.one,
    `ModelSpineTeleTest.two,
    `ModelSpineTeleTest.three,
    `ModelSpineTeleTest.altZero,
    `ModelSpineTeleTest.oneF,
    `ModelSpineTeleTest.twoF,
    `ModelSpineTeleTest.tag,
    `ModelSpineTeleTest.typeTag,
    `ModelSpineTeleTest.zeroEq,
    `ModelSpineTeleTest.distinctLevels,
    `ModelSpineTeleTest.betaType,
    `ModelSpineTeleTest.betaEquality,
    `ModelSpineTeleTest.distinctRepresentatives,
    `ModelSpineTeleTest.D1,
    `ModelSpineTeleTest.c1,
    `ModelSpineTeleTest.D2,
    `ModelSpineTeleTest.c2,
    `ModelSpineTeleTest.c1Typed,
    `ModelSpineTeleTest.betaMember,
    `ModelSpineTeleTest.c2Typed,
    `ModelSpineTeleTest.sortBacked,
    `ModelSpineTeleTest.k1,
    `ModelSpineTeleTest.k2,
    `ModelSpineTeleTest.keys,
    `ModelSpineTeleTest.doms,
    `ModelSpineTeleTest.endType,
    `ModelSpineTeleTest.piType,
    `ModelSpineTeleTest.lambdaTerm,
    `ModelSpineTeleTest.σ1,
    `ModelSpineTeleTest.σ2,
    `ModelSpineTeleTest.S1,
    `ModelSpineTeleTest.S2,
    `ModelSpineTeleTest.cv,
    `ModelSpineTeleTest.lambdaTyped,
    `ModelSpineTeleTest.firstKeyTyped,
    `ModelSpineTeleTest.secondDomainObserved,
    `ModelSpineTeleTest.secondKeyTyped,
    `ModelSpineTeleTest.telescopeKeys,
    `ModelSpineTeleTest.twoKeys,
    `ModelSpineTeleTest.lambdaObserved,
    `ModelSpineTeleTest.telescopeCodomain,
    `ModelSpineTeleTest.codomainObserved,
    `ModelSpineTeleTest.wrappedTyped,
    `ModelSpineTeleTest.domainSD,
    `ModelSpineTeleTest.bodySD,
    `ModelSpineTeleTest.innerPiSD,
    `ModelSpineTeleTest.telescopeSD,
    `ModelSpineTeleTest.piTypeSD,
    `ModelSpineTeleTest.lambdaSD,
    `ModelSpineTeleTest.lambdaHTS,
    `ModelSpineTeleTest.piTypeHTS,
    `ModelSpineTeleTest.derivedPiSoundness,
    `ModelSpineTeleTest.extendedTyped,
    `ModelSpineTeleTest.typeLevel,
    `ModelSpineTeleTest.delayedPi,
    `ModelSpineTeleTest.delayStrong,
    `ModelSpineTeleTest.convertedLambdaStrong,
    `ModelSpineTeleTest.convertedLambdaSound,
    `ModelSpineTeleTest.lambdaThroughConversion,
    `ModelSpineTeleTest.distinctPiTypes,
    `ModelSpineTeleTest.constName,
    `ModelSpineTeleTest.constValue,
    `ModelSpineTeleTest.constEnv,
    `ModelSpineTeleTest.constEnvWF,
    `ModelSpineTeleTest.emptyLE,
    `ModelSpineTeleTest.noRules,
    `ModelSpineTeleTest.constLookup,
    `ModelSpineTeleTest.constantStrong,
    `ModelSpineTeleTest.betaStrong,
    `ModelSpineTeleTest.betaReflStrong,
    `ModelSpineTeleTest.resultPiStrong,
    `ModelSpineTeleTest.firstApplicationStrong,
    `ModelSpineTeleTest.source,
    `ModelSpineTeleTest.sourceAtBeta,
    `ModelSpineTeleTest.sourceStrong,
    `ModelSpineTeleTest.sourceSound,
    `ModelSpineTeleTest.betaObserved,
    `ModelSpineTeleTest.reverseResult,
    `ModelSpineTeleTest.reverseDependentDomain,
    `ModelSpineTeleTest.storedPiSD,
    `ModelSpineTeleTest.arguments,
    `ModelSpineTeleTest.argumentAnchor,
    `ModelSpineTeleTest.argumentSets,
    `ModelSpineTeleTest.argumentsTyped,
    `ModelSpineTeleTest.prefixTyped,
    `ModelSpineTeleTest.partialSpineTyped,
    `ModelSpineTeleTest.domainsClosed,
    `ModelSpineTeleTest.innerDemand,
    `ModelSpineTeleTest.demandCovered,
    `ModelSpineTeleTest.finiteDependentKeys,
    `ModelSpineTeleTest.discoversDependentDemand,
    `ModelSpineTeleTest.finiteLambdaObservation,
    `ModelSpineTeleTest.openTerm,
    `ModelSpineTeleTest.openObservation,
    `ModelSpineTeleTest.openTermObserved,
    `ModelSpineTeleTest.allVariableCompact,
    `ModelSpineTeleTest.representativeReplacement,
    `ModelSpineTeleTest.keyObservationCoverage,
    `ModelSpineTeleTest.windFiniteHead]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.ChainArgs, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.ChainArgs.append, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.ChainArgs.length, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.HTS.spineRev, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.argSubst, []),
    (`Lean4Lean.VExpr.argSubst_append_one, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.foldl_cons_apply, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.argSubst_lt, [`Quot.sound, `propext]),
    (`Lean4Lean.List.exists_snoc_of_length_succ, [`propext]),
    (`Lean4Lean.VEnv.Model.fillS, []),
    (`Lean4Lean.VEnv.Model.Obs.compact_all, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.cons_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.snoc, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_compact_aux, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_compact, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.argSets, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.argSets_snoc, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.extS, []),
    (`Lean4Lean.VEnv.Model.extS_snoc, [`Quot.sound, `propext]),
    (`Lean4Lean.VExpr.argSubst_ge, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Le.piCodChain_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_split, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TeleKeys.substEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.take_getElem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.DomsSD.take, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TV.cons_set, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.forall₂_comp_cover, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.List.reverseRecOn, [`propext]),
    (`Lean4Lean.VEnv.Model.forall₂_snoc_inv, []),
    (`Lean4Lean.VEnv.Model.extS_cover, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.forall₂_cls, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.spine_tele_prefix, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.spine_tele, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.argSubst_inj, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.typed_wrap_rigid, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.Ob.Le.piCodChain_sort_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.obs_wrapForalls_sort, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.appCls_eq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.tele_wind, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.one, []),
    (`ModelSpineTeleTest.two, []),
    (`ModelSpineTeleTest.three, []),
    (`ModelSpineTeleTest.altZero, []),
    (`ModelSpineTeleTest.oneF, []),
    (`ModelSpineTeleTest.twoF, []),
    (`ModelSpineTeleTest.tag, []),
    (`ModelSpineTeleTest.typeTag, []),
    (`ModelSpineTeleTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.distinctLevels, []),
    (`ModelSpineTeleTest.betaType, []),
    (`ModelSpineTeleTest.betaEquality, [`propext]),
    (`ModelSpineTeleTest.distinctRepresentatives, []),
    (`ModelSpineTeleTest.D1, [`propext]),
    (`ModelSpineTeleTest.c1, [`propext]),
    (`ModelSpineTeleTest.D2, [`propext]),
    (`ModelSpineTeleTest.c2, [`propext]),
    (`ModelSpineTeleTest.c1Typed, [`propext]),
    (`ModelSpineTeleTest.betaMember, [`propext]),
    (`ModelSpineTeleTest.c2Typed, [`propext]),
    (`ModelSpineTeleTest.sortBacked, [`propext]),
    (`ModelSpineTeleTest.k1, [`propext]),
    (`ModelSpineTeleTest.k2, [`propext]),
    (`ModelSpineTeleTest.keys, [`propext]),
    (`ModelSpineTeleTest.doms, []),
    (`ModelSpineTeleTest.endType, []),
    (`ModelSpineTeleTest.piType, []),
    (`ModelSpineTeleTest.lambdaTerm, []),
    (`ModelSpineTeleTest.σ1, []),
    (`ModelSpineTeleTest.σ2, []),
    (`ModelSpineTeleTest.S1, []),
    (`ModelSpineTeleTest.S2, []),
    (`ModelSpineTeleTest.cv, [`propext]),
    (`ModelSpineTeleTest.lambdaTyped, [`propext]),
    (`ModelSpineTeleTest.firstKeyTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.secondDomainObserved, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.secondKeyTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.telescopeKeys, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.twoKeys, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.lambdaObserved, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.telescopeCodomain, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.codomainObserved, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.wrappedTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.domainSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.bodySD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.telescopeSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.piTypeSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.lambdaSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.lambdaHTS, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.piTypeHTS, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.derivedPiSoundness, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.extendedTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.typeLevel, []),
    (`ModelSpineTeleTest.delayedPi, []),
    (`ModelSpineTeleTest.delayStrong, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.convertedLambdaStrong, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.convertedLambdaSound, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.lambdaThroughConversion, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.distinctPiTypes, []),
    (`ModelSpineTeleTest.constName, []),
    (`ModelSpineTeleTest.constValue, []),
    (`ModelSpineTeleTest.constEnv, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.constEnvWF, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.emptyLE, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.noRules, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.constLookup, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.constantStrong, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.betaStrong, [`propext]),
    (`ModelSpineTeleTest.betaReflStrong, [`propext]),
    (`ModelSpineTeleTest.resultPiStrong, [`propext]),
    (`ModelSpineTeleTest.firstApplicationStrong, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.source, []),
    (`ModelSpineTeleTest.sourceAtBeta, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.sourceStrong, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.sourceSound, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.reverseResult, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.reverseDependentDomain, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.storedPiSD, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.arguments, []),
    (`ModelSpineTeleTest.argumentAnchor, []),
    (`ModelSpineTeleTest.argumentSets, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.argumentsTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.prefixTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.partialSpineTyped, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.domainsClosed, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.innerDemand, []),
    (`ModelSpineTeleTest.demandCovered, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.finiteDependentKeys, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.discoversDependentDemand, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.finiteLambdaObservation, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.openTerm, []),
    (`ModelSpineTeleTest.openObservation, []),
    (`ModelSpineTeleTest.openTermObserved, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.allVariableCompact, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.representativeReplacement, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.keyObservationCoverage, [`Quot.sound, `propext]),
    (`ModelSpineTeleTest.windFiniteHead, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-spinetele manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-spinetele manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-spinetele axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-spinetele admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-spinetele value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-spinetele dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-spinetele type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-spinetele admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-spinetele dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-spinetele traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-spinetele axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.HTS.spineRev then [`Lean4Lean.VEnv.Model.HTS, `Lean4Lean.VEnv.Model.SD.sub, `Lean4Lean.VEnv.Model.Obs.compact0B, `Lean4Lean.VEnv.Model.TypedAt.merge, `Lean4Lean.VEnv.Model.ChainArgs.append, `Lean4Lean.VEnv.Model.HeadTy]
      else if root == `Lean4Lean.List.exists_snoc_of_length_succ then [`List.eq_nil_or_concat]
      else if root == `Lean4Lean.VExpr.argSubst_lt then [`Lean4Lean.VExpr.foldl_cons_apply]
      else if root == `Lean4Lean.VEnv.Model.Obs.compact_all then [`Lean4Lean.VEnv.Model.Obs.collect, `Lean4Lean.VEnv.Model.Obs.compact, `Lean4Lean.VEnv.Model.Obs.closed_iff, `Lean4Lean.VEnv.Model.fillS]
      else if root == `Lean4Lean.VEnv.Model.TV.cons_inv then [`Lean4Lean.VEnv.Model.Obs.lift_cons_iff, `Lean4Lean.VEnv.Model.vcls_bvar_zero, `Lean4Lean.VEnv.Model.vcls_bvar_succ]
      else if root == `Lean4Lean.VEnv.Model.TeleKeys.snoc then [`Lean4Lean.VEnv.Model.TeleKeys.cons]
      else if root == `Lean4Lean.VEnv.Model.tele_compact_aux then [`Lean4Lean.VEnv.Model.Backed.close, `Lean4Lean.VEnv.Model.TypedAt.merge, `Lean4Lean.VEnv.Model.Obs.compact_all, `Lean4Lean.VEnv.Model.TeleKeys.snoc, `Lean4Lean.VEnv.Model.TV.cons_inv, `Lean4Lean.VExpr.argSubst_append_one, `Lean4Lean.List.exists_snoc_of_length_succ]
      else if root == `Lean4Lean.VEnv.Model.tele_compact then [`Lean4Lean.VEnv.Model.tele_compact_aux]
      else if root == `Lean4Lean.VEnv.Model.Le.piCodChain_inv then [`Lean4Lean.VEnv.Model.Ob.Le.piCodOb_inv]
      else if root == `Lean4Lean.VEnv.Model.tele_split then [`Lean4Lean.VEnv.Model.Obs.piCodOb_mem, `Lean4Lean.VEnv.Model.Obs.piCodOb_backed, `Lean4Lean.VEnv.Model.TeleKeys.cons, `Lean4Lean.VEnv.Model.extS]
      else if root == `Lean4Lean.VEnv.Model.TeleKeys.substEq then [`Lean4Lean.VEnv.Model.DomsSD, `Lean4Lean.VEnv.Model.TypedElCls.defeq, `Lean4Lean.VEnv.Ctx.SubstEq.cons]
      else if root == `Lean4Lean.VEnv.Model.extS_cover then [`Lean4Lean.VEnv.Model.forall₂_snoc_inv, `Lean4Lean.VEnv.Model.List.reverseRecOn, `Lean4Lean.VEnv.Model.argSets_snoc]
      else if root == `Lean4Lean.VEnv.Model.spine_tele_prefix then [`Lean4Lean.VEnv.Model.HTS.spineRev, `Lean4Lean.VEnv.Model.TeleKeys.substEq, `Lean4Lean.VEnv.Model.TV.transfer, `Lean4Lean.VEnv.Model.DomsSD.ctxSD, `Lean4Lean.VEnv.Model.tele_split, `Lean4Lean.VEnv.Model.extS_cover, `Lean4Lean.VEnv.Model.TyCls.defeq_rev, `Lean4Lean.VEnv.Model.DomsSD.take_getElem, `Lean4Lean.VEnv.Model.TV.cons_set]
      else if root == `Lean4Lean.VEnv.Model.spine_tele then [`Lean4Lean.VEnv.Model.spine_tele_prefix]
      else if root == `Lean4Lean.VEnv.Model.argSubst_inj then [`Lean4Lean.VExpr.argSubst_lt, `List.ext_getElem]
      else if root == `Lean4Lean.VEnv.Model.typed_wrap_rigid then [`Lean4Lean.VEnv.Model.TypedOb.app, `Lean4Lean.VEnv.Model.TypedOb.rigid]
      else if root == `Lean4Lean.VEnv.Model.Ob.Le.piCodChain_sort_inv then [`Lean4Lean.VEnv.Model.Ob.Le.piCodOb_inv]
      else if root == `Lean4Lean.VEnv.Model.obs_wrapForalls_sort then [`Lean4Lean.VEnv.Model.Obs.piCodOb_mem, `Lean4Lean.VEnv.Model.Obs.sort_mem]
      else if root == `Lean4Lean.VEnv.Model.appCls_eq then [`Lean4Lean.VEnv.Model.ElCls.collapse, `Lean4Lean.VEnv.Model.ElCls.eq_of_defeq, `Lean4Lean.VEnv.IsDefEq.appDF]
      else if root == `Lean4Lean.VEnv.Model.tele_wind then [`Lean4Lean.VEnv.Model.pi_list, `Lean4Lean.VEnv.Model.TypedAt.merge, `Lean4Lean.VEnv.Model.appCls_eq, `Lean4Lean.VEnv.Model.TypedElCls.hasType, `Lean4Lean.VExpr.subst_lift_inst]
      else if root == `ModelSpineTeleTest.reverseResult then [`Lean4Lean.VEnv.Model.HTS.spineRev, `ModelSpineTeleTest.sourceSound, `ModelSpineTeleTest.sourceAtBeta, `Lean4Lean.VEnv.Model.Ob.Le.sort_inv]
      else if root == `ModelSpineTeleTest.reverseDependentDomain then [`Lean4Lean.VEnv.Model.HTS.spineRev, `ModelSpineTeleTest.sourceSound, `Lean4Lean.VEnv.Model.SD]
      else if root == `ModelSpineTeleTest.storedPiSD then [`Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpineTeleTest.piTypeSD, `Lean4Lean.VEnv.Model.HTS.piSD]
      else if root == `ModelSpineTeleTest.argumentsTyped then [`Lean4Lean.VEnv.Model.spine_tele, `ModelSpineTeleTest.sourceSound, `ModelSpineTeleTest.storedPiSD, `ModelSpineTeleTest.constLookup]
      else if root == `ModelSpineTeleTest.prefixTyped then [`Lean4Lean.VEnv.Model.spine_tele_prefix, `ModelSpineTeleTest.sourceSound, `ModelSpineTeleTest.storedPiSD]
      else if root == `ModelSpineTeleTest.partialSpineTyped then [`Lean4Lean.VEnv.Model.spine_tele, `Lean4Lean.VEnv.Model.sound_no_rules, `ModelSpineTeleTest.firstApplicationStrong, `ModelSpineTeleTest.storedPiSD]
      else if root == `ModelSpineTeleTest.finiteDependentKeys then [`Lean4Lean.VEnv.Model.tele_compact, `ModelSpineTeleTest.argumentsTyped, `ModelSpineTeleTest.domainsClosed, `ModelSpineTeleTest.demandCovered]
      else if root == `ModelSpineTeleTest.discoversDependentDemand then [`ModelSpineTeleTest.finiteDependentKeys, `Lean4Lean.VEnv.Model.Obs.bvar_iff, `Lean4Lean.VEnv.Model.TypedOb.sort]
      else if root == `ModelSpineTeleTest.finiteLambdaObservation then [`ModelSpineTeleTest.discoversDependentDemand, `Lean4Lean.VEnv.Model.Obs.wrapLams_iff]
      else if root == `ModelSpineTeleTest.allVariableCompact then [`Lean4Lean.VEnv.Model.Obs.compact_all, `ModelSpineTeleTest.openTermObserved, `Lean4Lean.VEnv.Model.fillS, `Lean4Lean.VEnv.Model.Obs.piDomOb_mem]
      else if root == `ModelSpineTeleTest.representativeReplacement then [`Lean4Lean.VEnv.Model.TeleKeys.substEq, `ModelSpineTeleTest.telescopeKeys, `ModelSpineTeleTest.derivedPiSoundness]
      else if root == `ModelSpineTeleTest.keyObservationCoverage then [`Lean4Lean.VEnv.Model.extS_cover]
      else if root == `ModelSpineTeleTest.windFiniteHead then [`Lean4Lean.VEnv.Model.tele_wind, `Lean4Lean.VEnv.Model.argSubst_inj, `ModelSpineTeleTest.constantStrong, `ModelSpineTeleTest.discoversDependentDemand, `Lean4Lean.VEnv.Model.Obs.const]
      else []
    unless required.all visited.contains do
      throwError "model-spinetele proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelSpineTeleAudit
