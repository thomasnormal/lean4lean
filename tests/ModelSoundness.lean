import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ExprSound
import Lean.Util.CollectAxioms

namespace ModelSoundnessTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open scoped Lean4Lean.VEnv.Model

def one : VLevel := .succ .zero
def two : VLevel := .succ one
def three : VLevel := .succ two
def altZero : VLevel := .max .zero .zero
def tag : Ob := .sort (fun _ => 0)
def typeTag : Ob := .sort (fun _ => 1)
def betaType : VExpr := .app (.lam (.sort two) (.bvar 0)) (.sort one)

theorem zeroEq : VLevel.zero ≈ altZero :=
  VLevel.equiv_def.2 fun _ => by simp [altZero, VLevel.eval]

theorem betaSD : SD VEnv.empty 0 [] Γ betaType (.sort one) (.sort two) :=
  SD.beta .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)
    (SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl))
    (SD.sort (by trivial) (by trivial) rfl)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)

theorem betaRefl : SD VEnv.empty 0 [] Γ betaType betaType (.sort two) :=
  betaSD.trans .empty (by trivial) (betaSD.symm .empty (by trivial))

theorem distinctBeta : betaType ≠ VExpr.sort one := by intro h; cases h

def innerPi : VExpr := .forallE (.bvar 0) (.bvar 1)
def dependentFunction : VExpr := .lam (.sort two) (.lam (.bvar 0) (.bvar 0))
def dependentType : VExpr := .forallE (.sort two) innerPi

theorem domainSD : SD VEnv.empty 0 [] [.sort two] (.bvar 0) (.bvar 0) (.sort two) :=
  SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl)

theorem codomainSD : SD VEnv.empty 0 [] [.bvar 0, .sort two] (.bvar 1) (.bvar 1) (.sort two) :=
  SD.bvar (.succ .zero) (by trivial) (SD.sort (by trivial) (by trivial) rfl)

theorem variableSD : SD VEnv.empty 0 [] [.bvar 0, .sort two] (.bvar 0) (.bvar 0) (.bvar 1) :=
  SD.bvar .zero (by trivial) codomainSD

theorem innerPiSD : SD VEnv.empty 0 [] [.sort two] innerPi innerPi (.sort (.imax two two)) :=
  SD.forallE .empty (by trivial) (by trivial) (by trivial) domainSD codomainSD

theorem innerLambdaSD : SD VEnv.empty 0 [] [.sort two]
    (.lam (.bvar 0) (.bvar 0)) (.lam (.bvar 0) (.bvar 0)) innerPi :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial)
    domainSD codomainSD codomainSD variableSD variableSD

theorem dependentFunctionSD : SD VEnv.empty 0 [] []
    dependentFunction dependentFunction dependentType :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) innerPiSD innerPiSD innerLambdaSD innerLambdaSD

theorem dependentResultSD : SD VEnv.empty 0 [] []
    (innerPi.inst betaType) (innerPi.inst (.sort one)) (.sort (.imax two two)) :=
  SD.forallEDF .empty (by trivial) (by trivial) (by trivial) betaSD betaSD betaSD

theorem dependentApplicationSD : SD VEnv.empty 0 [] []
    (.app dependentFunction betaType) (.app dependentFunction (.sort one)) (innerPi.inst betaType) :=
  SD.appDF .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) innerPiSD dependentFunctionSD betaSD dependentResultSD

theorem instantiatedFunctionSD : SD VEnv.empty 0 [] []
    (.lam betaType (.bvar 0)) (.lam betaType (.bvar 0)) (innerPi.inst betaType) :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial) betaRefl betaRefl betaRefl
    (SD.bvar .zero (by trivial) betaRefl) (SD.bvar .zero (by trivial) betaRefl)

theorem dependentBetaSD : SD VEnv.empty 0 [] []
    (.app dependentFunction betaType) (.lam betaType (.bvar 0)) (innerPi.inst betaType) :=
  SD.beta .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) innerPiSD innerLambdaSD betaRefl
    (SD.forallE .empty (by trivial) (by trivial) (by trivial) betaRefl betaRefl) instantiatedFunctionSD

-- Binder domains differ by actual beta equality.
theorem changedDomainSD : SD VEnv.empty 0 [] []
    (.lam betaType (.sort .zero)) (.lam (.sort one) (.sort .zero))
    (.forallE betaType (.sort one)) :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial) betaSD
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)

-- Conversion changes the supplied type using a proved nonreflexive equality.
theorem convertedSortSD : SD VEnv.empty 0 [] Γ (.sort .zero) (.sort .zero) betaType :=
  SD.defeqDF .empty (by trivial) (by trivial) (betaSD.symm .empty (by trivial))
    (SD.sort (by trivial) (by trivial) rfl)

theorem identitySD : SD VEnv.empty 0 [] Γ
    (.lam (.sort one) (.bvar 0)) (.lam (.sort one) (.bvar 0)) (.forallE (.sort one) (.sort one)) :=
  SD.lamDF .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)
    (SD.sort (by trivial) (by trivial) rfl)
    (SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl))
    (SD.bvar .zero (by trivial) (SD.sort (by trivial) (by trivial) rfl))

def identity : VExpr := .lam (.sort one) (.bvar 0)
def etaIdentity : VExpr := .lam (.sort one) (.app identity.lift (.bvar 0))

theorem etaSD : SD VEnv.empty 0 [] [] etaIdentity identity (.forallE (.sort one) (.sort one)) :=
  SD.eta .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)
    (SD.sort (by trivial) (by trivial) rfl) identitySD identitySD
    (SD.sort (by trivial) (by trivial) rfl)

def argD : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort one)
def argC : VExpr → Prop := ElCls VEnv.empty 0 [] argD (.sort .zero)

theorem argTyped : TypedElCls VEnv.empty 0 [] argD argC :=
  .of_hasType (HasType.sort (by trivial))

theorem sortBacked (l : List Nat → Nat) : Backed (listSet [.sort l]) := by
  intro o ho w hw
  cases List.mem_singleton.1 ho
  cases hw

theorem duplicateBacked : Backed (listSet [tag, tag]) := by
  intro o ho w hw
  have : o = tag := by simpa [listSet] using ho
  subst o
  cases hw

theorem identityObserved : Obs VEnv.empty 0 [] .id .empty identity (.app argD argC [tag] tag) :=
  .lam (τs := [typeTag]) (x := .sort .zero) argTyped
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort)
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort (.head _))
    (sortBacked _) ElCls.self (.bvar (.head _))

theorem etaDuplicateObserved : Obs VEnv.empty 0 [] .id .empty etaIdentity
    (.app argD argC [tag, tag] tag) := by
  refine .lam (τs := [typeTag]) (x := .sort .zero) argTyped ?_ ?_ duplicateBacked ElCls.self ?_
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort
  · intro k hk
    have : k = tag := by simpa using hk
    subst k
    exact .sort (.head _)
  · exact .app (Obs.lift_cons_iff.2 identityObserved) rfl (K' := [tag])
      (fun k hk => .bvar (by cases List.mem_singleton.1 hk; exact .head _)) Covers.refl

theorem etaDuplicateTyped : TypedAt VEnv.empty 0 []
    (vcls VEnv.empty 0 [] .id etaIdentity (.forallE (.sort one) (.sort one)))
    .id .empty (.forallE (.sort one) (.sort one)) (.app argD argC [tag, tag] tag) :=
  (etaSD.2 .id .id .empty .nil TV.empty TV.empty).2.2.1 _ etaDuplicateObserved

theorem etaForward : ∃ o, Obs VEnv.empty 0 [] .id .empty identity o ∧
    o ≼ .app argD argC [tag, tag] tag :=
  (etaSD.2 .id .id .empty .nil TV.empty TV.empty).1 _ etaDuplicateObserved

theorem etaBackward : ∃ o, Obs VEnv.empty 0 [] .id .empty etaIdentity o ∧
    o ≼ .app argD argC [tag] tag :=
  (etaSD.2 .id .id .empty .nil TV.empty TV.empty).2.1 _ identityObserved

theorem betaBackward : ∃ o, Obs VEnv.empty 0 [] .id .empty betaType o ∧ o ≼ typeTag :=
  (betaSD.2 .id .id .empty .nil TV.empty TV.empty).2.1 _ .sort

theorem emptyBodyDemandImpossible : ¬ Obs VEnv.empty 0 [] σ ObSets.empty (.bvar 0) typeTag := by
  intro h
  exact Obs.bvar_iff.1 h

-- The same observation sets are typed at syntactically different anchors.
def σleft : VExpr.Subst := VExpr.Subst.id.cons betaType
def σright : VExpr.Subst := VExpr.Subst.id.cons (.sort one)
def anchorSets : ObSets := ObSets.empty.cons (listSet [typeTag])

theorem relatedAnchors : Ctx.SubstEq VEnv.empty 0 [] σleft σright [.sort two] :=
  .cons .nil (HasType.sort (by trivial)) betaSD.1.defeq

theorem leftValuation : TV VEnv.empty 0 [] [.sort two] σleft anchorSets :=
  TV.empty.cons (sortBacked _) fun k hk => by
    cases List.mem_singleton.1 hk
    exact ⟨[.sort (fun _ => 2)], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort,
      .sort (.head _)⟩

theorem rightValuation : TV VEnv.empty 0 [] [.sort two] σright anchorSets :=
  TV.empty.cons (sortBacked _) fun k hk => by
    cases List.mem_singleton.1 hk
    exact ⟨[.sort (fun _ => 2)], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort,
      .sort (.head _)⟩

theorem innerLambdaObserved : Obs VEnv.empty 0 [] σleft anchorSets (.lam (.bvar 0) (.bvar 0))
    (.app (TyCls VEnv.empty 0 [] betaType)
      (ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] betaType) (.sort .zero)) [tag] tag) := by
  refine .lam (τs := [typeTag]) (x := .sort .zero)
    (TypedElCls.of_hasType (show VEnv.empty.HasType 0 [] (.sort .zero) betaType from
      convertedSortSD.1.defeq)) ?_ ?_ (sortBacked _) ElCls.self (.bvar (.head _))
  · intro τ hτ; exact .bvar hτ
  · intro k hk; cases List.mem_singleton.1 hk; exact .sort (.head _)

theorem lambdaAcrossAnchors : ∃ o, Obs VEnv.empty 0 [] σright anchorSets
    (.lam (.bvar 0) (.bvar 0)) o ∧
    o ≼ .app (TyCls VEnv.empty 0 [] betaType)
      (ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] betaType) (.sort .zero)) [tag] tag :=
  (innerLambdaSD.2 σleft σright anchorSets relatedAnchors leftValuation rightValuation).1 _
    innerLambdaObserved

-- Distinct neutral proofs in a real dependent context.
def proofContext : List VExpr := [.bvar 1, .bvar 0, .sort .zero]

theorem propositionSD : SD VEnv.empty 0 [] proofContext (.bvar 2) (.bvar 2) (.sort .zero) :=
  SD.bvar (.succ (.succ .zero)) (by trivial) (SD.sort (by trivial) (by trivial) rfl)

theorem firstProofSD : SD VEnv.empty 0 [] proofContext (.bvar 1) (.bvar 1) (.bvar 2) :=
  SD.bvar (.succ .zero) (by trivial) propositionSD

theorem secondProofSD : SD VEnv.empty 0 [] proofContext (.bvar 0) (.bvar 0) (.bvar 2) :=
  SD.bvar .zero (by trivial) propositionSD

theorem distinctProofsSD : SD VEnv.empty 0 [] proofContext (.bvar 1) (.bvar 0) (.bvar 2) :=
  SD.proofIrrel .empty (by trivial) propositionSD firstProofSD secondProofSD

-- A stored checked polymorphic delta definition supplies the constant case.
def polyName : Name := Name.mkSimple "SoundUniverse"
def polyValue : VDefVal := ⟨⟨⟨1, .sort (.succ (.param 0))⟩, polyName⟩, .sort (.param 0)⟩
def polyBase : VEnv := {
  constants n := if polyName = n then some polyValue.toVConstant else none
  defeqs _ := False }
def polyEnv : VEnv := polyBase.addDefEq polyValue.toDefEq

theorem polyWF : polyEnv.WF := by
  refine ⟨_, .decl (.def (ci := polyValue) ?_ ?_) .empty⟩
  · exact .sort (by decide)
  · rfl

theorem polyLookup : polyEnv.constants polyName = some polyValue.toVConstant := by
  simp [polyEnv, VEnv.addDefEq, polyBase]

theorem polySD : SD polyEnv 0 [] Γ (.const polyName [.zero]) (.const polyName [altZero])
    (.sort one) :=
  SD.constDF polyWF.ordered (by trivial) polyLookup
    (by simp [VLevel.WF]) (by simp [VLevel.WF, altZero]) rfl (.cons zeroEq .nil) (by trivial)
    (SD.sort (by trivial) (by change (VLevel.succ altZero).WF 0; simp [VLevel.WF, altZero])
      (VLevel.succ_congr zeroEq))
    (SD.sort (by trivial) (by change (VLevel.succ altZero).WF 0; simp [VLevel.WF, altZero])
      (VLevel.succ_congr zeroEq))

theorem polyObserved : Obs polyEnv 0 [] .id .empty (.const polyName [.zero]) tag := by
  refine .delta (df := polyValue.toDefEq) (ci := polyValue.toVConstant) (τs := [typeTag])
    (.inl rfl) rfl polyLookup ?_ (.sort (.head _)) .sort
  intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort

theorem polySoundTransfer : ∃ o, Obs polyEnv 0 [] .id .empty (.const polyName [altZero]) o ∧ o ≼ tag :=
  (polySD.2 .id .id .empty .nil TV.empty TV.empty).1 _ polyObserved

theorem betaObserved : Obs VEnv.empty 0 [] .id .empty betaType typeTag := by
  obtain ⟨o, ho, l⟩ := betaBackward
  cases l.sort_inv
  exact ho

def universeD : VExpr → Prop := TyCls VEnv.empty 0 [] (.sort two)
def universeC : VExpr → Prop := ElCls VEnv.empty 0 [] universeD (.sort one)

theorem universeClassTyped : TypedElCls VEnv.empty 0 [] universeD universeC :=
  .of_hasType (HasType.sort (by trivial))

theorem betaMember : universeC betaType :=
  ElCls.mem_of_defeq betaSD.1.defeq.symm

def dependentObservation : Ob :=
  .app (TyCls VEnv.empty 0 [] betaType)
    (ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] betaType) (.sort .zero)) [tag] tag

theorem dependentFunctionObserved : Obs VEnv.empty 0 [] .id .empty dependentFunction
    (.app universeD universeC [typeTag] dependentObservation) :=
  .lam (τs := [.sort (fun _ => 2)]) (x := betaType) universeClassTyped
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort)
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort (.head _))
    (sortBacked _) betaMember innerLambdaObserved

theorem dependentApplicationObserved : Obs VEnv.empty 0 [] .id .empty
    (.app dependentFunction betaType) dependentObservation :=
  .app dependentFunctionObserved (ElCls.eq_of_mem betaMember).symm
    (K' := [typeTag]) (fun k hk => by cases List.mem_singleton.1 hk; exact betaObserved)
    Covers.refl

theorem dependentApplicationTyped : TypedAt VEnv.empty 0 []
    (vcls VEnv.empty 0 [] .id (.app dependentFunction betaType) (innerPi.inst betaType))
    .id .empty (innerPi.inst betaType) dependentObservation :=
  (dependentApplicationSD.2 .id .id .empty .nil TV.empty TV.empty).2.2.1 _
    dependentApplicationObserved

theorem dependentRightTypedAtOriginal : ∃ o,
    Obs VEnv.empty 0 [] .id .empty (.app dependentFunction (.sort one)) o ∧
    TypedAt VEnv.empty 0 []
      (vcls VEnv.empty 0 [] .id (.app dependentFunction (.sort one)) (innerPi.inst betaType))
      .id .empty (innerPi.inst betaType) o ∧ o ≼ dependentObservation := by
  have sound := dependentApplicationSD.2 .id .id .empty .nil TV.empty TV.empty
  obtain ⟨o, ho, l⟩ := sound.1 _ dependentApplicationObserved
  exact ⟨o, ho, sound.2.2.2 o ho, l⟩

theorem distinctDependentResults : innerPi.inst betaType ≠ innerPi.inst (.sort one) := by
  intro h
  change VExpr.forallE betaType betaType = .forallE (.sort one) (.sort one) at h
  exact distinctBeta (VExpr.forallE.inj h).1

theorem instantiatedLambdaObserved : Obs VEnv.empty 0 [] .id .empty
    (.lam betaType (.bvar 0)) dependentObservation :=
  .lam (τs := [typeTag]) (x := .sort .zero)
    (TypedElCls.of_hasType (show VEnv.empty.HasType 0 [] (.sort .zero) betaType from
      convertedSortSD.1.defeq))
    (fun τ hτ => by cases List.mem_singleton.1 hτ; exact betaObserved)
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort (.head _))
    (sortBacked _) ElCls.self (.bvar (.head _))

theorem dependentBetaForward : ∃ o, Obs VEnv.empty 0 [] .id .empty
    (.lam betaType (.bvar 0)) o ∧ o ≼ dependentObservation :=
  (dependentBetaSD.2 .id .id .empty .nil TV.empty TV.empty).1 _ dependentApplicationObserved

theorem dependentBetaBackward : ∃ o, Obs VEnv.empty 0 [] .id .empty
    (.app dependentFunction betaType) o ∧ o ≼ dependentObservation :=
  (dependentBetaSD.2 .id .id .empty .nil TV.empty TV.empty).2.1 _ instantiatedLambdaObserved

theorem proofContextWF : OnCtx proofContext (VEnv.empty.IsType 0) :=
  ⟨⟨⟨trivial, _, HasType.sort (by trivial)⟩, _, HasType.bvar .zero⟩,
    _, HasType.bvar (.succ .zero)⟩

theorem distinctProofVariables : VExpr.bvar 0 ≠ .bvar 1 := by
  intro h
  cases h

-- Function and argument both change in one actual application comparison.
theorem bothChangedSD : SD VEnv.empty 0 [] []
    (.app etaIdentity (.sort .zero)) (.app identity (.sort altZero)) (.sort one) :=
  SD.appDF .empty (by trivial) (by trivial) (by trivial)
    (SD.sort (by trivial) (by trivial) rfl) (SD.sort (by trivial) (by trivial) rfl)
    etaSD (SD.sort (by trivial) (by simp [VLevel.WF, altZero]) zeroEq)
    (SD.sort (by trivial) (by trivial) rfl)

theorem bothChangedObserved : Obs VEnv.empty 0 [] .id .empty
    (.app etaIdentity (.sort .zero)) tag :=
  .app etaDuplicateObserved rfl (K' := [tag])
    (fun k hk => by cases List.mem_singleton.1 hk; exact .sort)
    (Covers.of_subset fun k hk => by simpa using hk)

theorem bothChangedRightTyped : ∃ o,
    Obs VEnv.empty 0 [] .id .empty (.app identity (.sort altZero)) o ∧
    TypedAt VEnv.empty 0 []
      (vcls VEnv.empty 0 [] .id (.app identity (.sort altZero)) (.sort one))
      .id .empty (.sort one) o ∧ o ≼ tag := by
  have sound := bothChangedSD.2 .id .id .empty .nil TV.empty TV.empty
  obtain ⟨o, ho, l⟩ := sound.1 _ bothChangedObserved
  exact ⟨o, ho, sound.2.2.2 o ho, l⟩

end ModelSoundnessTest

namespace ModelSoundnessAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.TypedElCls.eq_of_mem,
    `Lean4Lean.VEnv.Model.typed_pi_app,
    `Lean4Lean.VEnv.Model.TypedOb.app_enlarge,
    `Lean4Lean.VEnv.Model.lam_typed,
    `Lean4Lean.VEnv.Model.app_typed,
    `Lean4Lean.VEnv.Model.SoundAt.appDF,
    `Lean4Lean.VEnv.Model.SoundAt.lamDF,
    `Lean4Lean.VEnv.Model.SoundAt.defeqDF,
    `Lean4Lean.VEnv.Model.SoundAt.beta,
    `Lean4Lean.VEnv.Model.SoundAt.eta,
    `Lean4Lean.VEnv.Model.SoundAt.proofIrrel,
    `Lean4Lean.VEnv.Model.SoundAt.constDF,
    `Lean4Lean.VEnv.Model.SD.symm,
    `Lean4Lean.VEnv.Model.SD.trans,
    `Lean4Lean.VEnv.Model.SD.appDF,
    `Lean4Lean.VEnv.Model.SD.lamDF,
    `Lean4Lean.VEnv.Model.SD.forallEDF,
    `Lean4Lean.VEnv.Model.SD.defeqDF,
    `Lean4Lean.VEnv.Model.SD.beta,
    `Lean4Lean.VEnv.Model.SD.eta,
    `Lean4Lean.VEnv.Model.SD.proofIrrel,
    `Lean4Lean.VEnv.Model.SD.constDF,
    `ModelSoundnessTest.one,
    `ModelSoundnessTest.two,
    `ModelSoundnessTest.three,
    `ModelSoundnessTest.altZero,
    `ModelSoundnessTest.tag,
    `ModelSoundnessTest.typeTag,
    `ModelSoundnessTest.betaType,
    `ModelSoundnessTest.zeroEq,
    `ModelSoundnessTest.betaSD,
    `ModelSoundnessTest.betaRefl,
    `ModelSoundnessTest.distinctBeta,
    `ModelSoundnessTest.innerPi,
    `ModelSoundnessTest.dependentFunction,
    `ModelSoundnessTest.dependentType,
    `ModelSoundnessTest.domainSD,
    `ModelSoundnessTest.codomainSD,
    `ModelSoundnessTest.variableSD,
    `ModelSoundnessTest.innerPiSD,
    `ModelSoundnessTest.innerLambdaSD,
    `ModelSoundnessTest.dependentFunctionSD,
    `ModelSoundnessTest.dependentResultSD,
    `ModelSoundnessTest.dependentApplicationSD,
    `ModelSoundnessTest.instantiatedFunctionSD,
    `ModelSoundnessTest.dependentBetaSD,
    `ModelSoundnessTest.changedDomainSD,
    `ModelSoundnessTest.convertedSortSD,
    `ModelSoundnessTest.identitySD,
    `ModelSoundnessTest.identity,
    `ModelSoundnessTest.etaIdentity,
    `ModelSoundnessTest.etaSD,
    `ModelSoundnessTest.argD,
    `ModelSoundnessTest.argC,
    `ModelSoundnessTest.argTyped,
    `ModelSoundnessTest.sortBacked,
    `ModelSoundnessTest.duplicateBacked,
    `ModelSoundnessTest.identityObserved,
    `ModelSoundnessTest.etaDuplicateObserved,
    `ModelSoundnessTest.etaDuplicateTyped,
    `ModelSoundnessTest.etaForward,
    `ModelSoundnessTest.etaBackward,
    `ModelSoundnessTest.betaBackward,
    `ModelSoundnessTest.emptyBodyDemandImpossible,
    `ModelSoundnessTest.σleft,
    `ModelSoundnessTest.σright,
    `ModelSoundnessTest.anchorSets,
    `ModelSoundnessTest.relatedAnchors,
    `ModelSoundnessTest.leftValuation,
    `ModelSoundnessTest.rightValuation,
    `ModelSoundnessTest.innerLambdaObserved,
    `ModelSoundnessTest.lambdaAcrossAnchors,
    `ModelSoundnessTest.proofContext,
    `ModelSoundnessTest.propositionSD,
    `ModelSoundnessTest.firstProofSD,
    `ModelSoundnessTest.secondProofSD,
    `ModelSoundnessTest.distinctProofsSD,
    `ModelSoundnessTest.polyName,
    `ModelSoundnessTest.polyValue,
    `ModelSoundnessTest.polyBase,
    `ModelSoundnessTest.polyEnv,
    `ModelSoundnessTest.polyWF,
    `ModelSoundnessTest.polyLookup,
    `ModelSoundnessTest.polySD,
    `ModelSoundnessTest.polyObserved,
    `ModelSoundnessTest.polySoundTransfer,
    `ModelSoundnessTest.betaObserved,
    `ModelSoundnessTest.universeD,
    `ModelSoundnessTest.universeC,
    `ModelSoundnessTest.universeClassTyped,
    `ModelSoundnessTest.betaMember,
    `ModelSoundnessTest.dependentObservation,
    `ModelSoundnessTest.dependentFunctionObserved,
    `ModelSoundnessTest.dependentApplicationObserved,
    `ModelSoundnessTest.dependentApplicationTyped,
    `ModelSoundnessTest.dependentRightTypedAtOriginal,
    `ModelSoundnessTest.distinctDependentResults,
    `ModelSoundnessTest.instantiatedLambdaObserved,
    `ModelSoundnessTest.dependentBetaForward,
    `ModelSoundnessTest.dependentBetaBackward,
    `ModelSoundnessTest.proofContextWF,
    `ModelSoundnessTest.distinctProofVariables,
    `ModelSoundnessTest.bothChangedSD,
    `ModelSoundnessTest.bothChangedObserved,
    `ModelSoundnessTest.bothChangedRightTyped]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.TypedElCls.eq_of_mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.typed_pi_app, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedOb.app_enlarge, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.lam_typed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.app_typed, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.appDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.lamDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.defeqDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.beta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.eta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.proofIrrel, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SoundAt.constDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.symm, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.trans, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.appDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.lamDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.forallEDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.defeqDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.beta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.eta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.proofIrrel, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SD.constDF, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.one, []),
    (`ModelSoundnessTest.two, []),
    (`ModelSoundnessTest.three, []),
    (`ModelSoundnessTest.altZero, []),
    (`ModelSoundnessTest.tag, []),
    (`ModelSoundnessTest.typeTag, []),
    (`ModelSoundnessTest.betaType, []),
    (`ModelSoundnessTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.betaSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.betaRefl, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.distinctBeta, []),
    (`ModelSoundnessTest.innerPi, []),
    (`ModelSoundnessTest.dependentFunction, []),
    (`ModelSoundnessTest.dependentType, []),
    (`ModelSoundnessTest.domainSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.codomainSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.variableSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.innerPiSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.innerLambdaSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentFunctionSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentResultSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentApplicationSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.instantiatedFunctionSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentBetaSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.changedDomainSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.convertedSortSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.identitySD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.identity, []),
    (`ModelSoundnessTest.etaIdentity, []),
    (`ModelSoundnessTest.etaSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.argD, [`propext]),
    (`ModelSoundnessTest.argC, [`propext]),
    (`ModelSoundnessTest.argTyped, [`propext]),
    (`ModelSoundnessTest.sortBacked, [`propext]),
    (`ModelSoundnessTest.duplicateBacked, [`propext]),
    (`ModelSoundnessTest.identityObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.etaDuplicateObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.etaDuplicateTyped, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.etaForward, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.etaBackward, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.betaBackward, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.emptyBodyDemandImpossible, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.σleft, []),
    (`ModelSoundnessTest.σright, []),
    (`ModelSoundnessTest.anchorSets, []),
    (`ModelSoundnessTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.leftValuation, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.rightValuation, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.innerLambdaObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.lambdaAcrossAnchors, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.proofContext, []),
    (`ModelSoundnessTest.propositionSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.firstProofSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.secondProofSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.distinctProofsSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polyName, []),
    (`ModelSoundnessTest.polyValue, []),
    (`ModelSoundnessTest.polyBase, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polyEnv, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polyWF, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polyLookup, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polySD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polyObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.polySoundTransfer, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.betaObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.universeD, [`propext]),
    (`ModelSoundnessTest.universeC, [`propext]),
    (`ModelSoundnessTest.universeClassTyped, [`propext]),
    (`ModelSoundnessTest.betaMember, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentObservation, [`propext]),
    (`ModelSoundnessTest.dependentFunctionObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentApplicationObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentApplicationTyped, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentRightTypedAtOriginal, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.distinctDependentResults, []),
    (`ModelSoundnessTest.instantiatedLambdaObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentBetaForward, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.dependentBetaBackward, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.proofContextWF, [`propext]),
    (`ModelSoundnessTest.distinctProofVariables, []),
    (`ModelSoundnessTest.bothChangedSD, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.bothChangedObserved, [`Quot.sound, `propext]),
    (`ModelSoundnessTest.bothChangedRightTyped, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-soundness manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-soundness manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-soundness axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-soundness admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-soundness value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-soundness dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-soundness type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-soundness admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-soundness dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-soundness traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-soundness axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.TypedElCls.eq_of_mem then [`Lean4Lean.VEnv.Model.TypedElCls.mem]
      else if root == `Lean4Lean.VEnv.Model.typed_pi_app then [`Lean4Lean.VEnv.Model.TypedOb, `Lean4Lean.VEnv.Model.Obs]
      else if root == `Lean4Lean.VEnv.Model.TypedOb.app_enlarge then [`Lean4Lean.VEnv.Model.TypedOb.app, `Lean4Lean.VEnv.Model.Covers.trans]
      else if root == `Lean4Lean.VEnv.Model.lam_typed then [`Lean4Lean.VEnv.Model.pi_list, `Lean4Lean.VEnv.Model.vcls_beta, `Lean4Lean.VEnv.Model.TypedAt.merge]
      else if root == `Lean4Lean.VEnv.Model.app_typed then [`Lean4Lean.VEnv.Model.vcls_app, `Lean4Lean.VEnv.Model.TypedElCls.defeq, `Lean4Lean.VEnv.Model.Obs.inst_iff, `Lean4Lean.VEnv.Model.Obs.mono_le, `Lean4Lean.VEnv.Model.TV.cons_cls, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.TypedOb.strengthen]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.appDF then [`Lean4Lean.VEnv.Model.app_typed, `Lean4Lean.VEnv.Model.ElCls.eq_of_defeq, `Lean4Lean.VEnv.Model.exists_list_cover, `Lean4Lean.VEnv.Model.vcls_conv, `Lean4Lean.VEnv.Model.TypedAt.mono_le, `Lean4Lean.VEnv.Model.Ob.Le.app_inv]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.lamDF then [`Lean4Lean.VEnv.Model.keys_transfer, `Lean4Lean.VEnv.Model.keys_transfer_symm, `Lean4Lean.VEnv.Model.lam_typed, `Lean4Lean.VEnv.Model.vcls_defeq, `Lean4Lean.VEnv.Model.TV.cons_cls]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.defeqDF then [`Lean4Lean.VEnv.Model.vcls_conv, `Lean4Lean.VEnv.Model.TypedAt.mono_le]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.beta then [`Lean4Lean.VEnv.Model.Obs.compact0B, `Lean4Lean.VEnv.Model.Obs.backed, `Lean4Lean.VEnv.Model.Obs.inst_iff, `Lean4Lean.VEnv.Model.Obs.mono_le, `Lean4Lean.VEnv.Model.TypedElCls.hasType, `Lean4Lean.VEnv.Model.lam_typed, `Lean4Lean.VEnv.Model.app_typed, `Lean4Lean.VEnv.Model.TV.cons_cls, `Lean4Lean.VEnv.Model.exists_list_cover]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.eta then [`Lean4Lean.VEnv.Model.typed_pi_app, `Lean4Lean.VEnv.Model.TypedOb.app_enlarge, `Lean4Lean.VEnv.Model.TypedElCls.eq_of_mem, `Lean4Lean.VEnv.Model.vcls_defeq, `Lean4Lean.VEnv.Model.Obs.lift_cons_iff, `Lean4Lean.VEnv.IsDefEq.eta]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.proofIrrel then [`Lean4Lean.VEnv.Model.TypedOb.not_prop, `Lean4Lean.VEnv.Model.typedAt_sort_iff]
      else if root == `Lean4Lean.VEnv.Model.SoundAt.constDF then [`Lean4Lean.VEnv.Model.Obs.const_levels, `Lean4Lean.VEnv.Model.Obs.const_typed, `Lean4Lean.VEnv.Model.TypedAt.lvEq, `Lean4Lean.VEnv.Model.vcls_closed, `Lean4Lean.VEnv.Model.TyCls.eq_of_lvEq]
      else if root == `ModelSoundnessTest.betaSD then [`Lean4Lean.VEnv.Model.SD.beta, `Lean4Lean.VEnv.Model.SoundAt.beta, `Lean4Lean.VEnv.IsDefEqStrong.beta]
      else if root == `ModelSoundnessTest.dependentApplicationSD then [`Lean4Lean.VEnv.Model.SD.appDF, `ModelSoundnessTest.dependentResultSD, `ModelSoundnessTest.dependentFunctionSD, `ModelSoundnessTest.betaSD]
      else if root == `ModelSoundnessTest.dependentResultSD then [`Lean4Lean.VEnv.Model.SD.forallEDF, `ModelSoundnessTest.betaSD]
      else if root == `ModelSoundnessTest.dependentApplicationTyped then [`Lean4Lean.VEnv.Model.app_typed, `ModelSoundnessTest.dependentApplicationSD, `ModelSoundnessTest.dependentApplicationObserved]
      else if root == `ModelSoundnessTest.dependentRightTypedAtOriginal then [`Lean4Lean.VEnv.Model.SoundAt.appDF, `ModelSoundnessTest.dependentApplicationSD, `ModelSoundnessTest.dependentApplicationObserved, `ModelSoundnessTest.dependentResultSD]
      else if root == `ModelSoundnessTest.dependentBetaBackward then [`Lean4Lean.VEnv.Model.Obs.compact0B, `Lean4Lean.VEnv.Model.SoundAt.beta, `ModelSoundnessTest.dependentBetaSD, `ModelSoundnessTest.instantiatedLambdaObserved]
      else if root == `ModelSoundnessTest.dependentBetaForward then [`Lean4Lean.VEnv.Model.SoundAt.beta, `ModelSoundnessTest.dependentApplicationObserved, `ModelSoundnessTest.dependentBetaSD]
      else if root == `ModelSoundnessTest.etaDuplicateTyped then [`Lean4Lean.VEnv.Model.TypedOb.app_enlarge, `ModelSoundnessTest.etaDuplicateObserved, `ModelSoundnessTest.etaSD]
      else if root == `ModelSoundnessTest.etaBackward then [`Lean4Lean.VEnv.Model.typed_pi_app, `ModelSoundnessTest.identityObserved, `ModelSoundnessTest.etaSD]
      else if root == `ModelSoundnessTest.etaForward then [`Lean4Lean.VEnv.Model.SoundAt.eta, `ModelSoundnessTest.etaDuplicateObserved, `ModelSoundnessTest.etaSD]
      else if root == `ModelSoundnessTest.lambdaAcrossAnchors then [`Lean4Lean.VEnv.Model.SoundAt.lamDF, `ModelSoundnessTest.relatedAnchors, `ModelSoundnessTest.leftValuation, `ModelSoundnessTest.rightValuation, `ModelSoundnessTest.innerLambdaObserved]
      else if root == `ModelSoundnessTest.relatedAnchors then [`ModelSoundnessTest.betaSD, `Lean4Lean.VEnv.Ctx.SubstEq.cons]
      else if root == `ModelSoundnessTest.changedDomainSD then [`Lean4Lean.VEnv.Model.SD.lamDF, `ModelSoundnessTest.betaSD]
      else if root == `ModelSoundnessTest.convertedSortSD then [`Lean4Lean.VEnv.Model.SD.defeqDF, `ModelSoundnessTest.betaSD]
      else if root == `ModelSoundnessTest.distinctProofsSD then [`Lean4Lean.VEnv.Model.SD.proofIrrel, `ModelSoundnessTest.propositionSD, `ModelSoundnessTest.firstProofSD, `ModelSoundnessTest.secondProofSD]
      else if root == `ModelSoundnessTest.polySD then [`Lean4Lean.VEnv.Model.SD.constDF, `ModelSoundnessTest.polyWF, `ModelSoundnessTest.polyLookup, `ModelSoundnessTest.zeroEq]
      else if root == `ModelSoundnessTest.polySoundTransfer then [`Lean4Lean.VEnv.Model.Obs.const_levels, `ModelSoundnessTest.polySD, `ModelSoundnessTest.polyObserved]
      else if root == `ModelSoundnessTest.bothChangedRightTyped then [`Lean4Lean.VEnv.Model.SoundAt.appDF, `ModelSoundnessTest.bothChangedSD, `ModelSoundnessTest.etaSD, `ModelSoundnessTest.zeroEq, `ModelSoundnessTest.bothChangedObserved]
      else if root == `Lean4Lean.VEnv.Model.SD.symm then [`Lean4Lean.VEnv.Model.SoundAt.symm, `Lean4Lean.VEnv.IsDefEqStrong.symm]
      else if root == `Lean4Lean.VEnv.Model.SD.trans then [`Lean4Lean.VEnv.Model.SoundAt.trans, `Lean4Lean.VEnv.IsDefEqStrong.trans]
      else if root == `Lean4Lean.VEnv.Model.SD.appDF then [`Lean4Lean.VEnv.Model.SoundAt.appDF, `Lean4Lean.VEnv.IsDefEqStrong.appDF]
      else if root == `Lean4Lean.VEnv.Model.SD.lamDF then [`Lean4Lean.VEnv.Model.SoundAt.lamDF, `Lean4Lean.VEnv.IsDefEqStrong.lamDF]
      else if root == `Lean4Lean.VEnv.Model.SD.forallEDF then [`Lean4Lean.VEnv.Model.SoundAt.forallEDF, `Lean4Lean.VEnv.IsDefEqStrong.forallEDF]
      else if root == `Lean4Lean.VEnv.Model.SD.defeqDF then [`Lean4Lean.VEnv.Model.SoundAt.defeqDF, `Lean4Lean.VEnv.IsDefEqStrong.defeqDF]
      else if root == `Lean4Lean.VEnv.Model.SD.beta then [`Lean4Lean.VEnv.Model.SoundAt.beta, `Lean4Lean.VEnv.IsDefEqStrong.beta]
      else if root == `Lean4Lean.VEnv.Model.SD.eta then [`Lean4Lean.VEnv.Model.SoundAt.eta, `Lean4Lean.VEnv.IsDefEqStrong.eta]
      else if root == `Lean4Lean.VEnv.Model.SD.proofIrrel then [`Lean4Lean.VEnv.Model.SoundAt.proofIrrel, `Lean4Lean.VEnv.IsDefEqStrong.proofIrrel]
      else if root == `Lean4Lean.VEnv.Model.SD.constDF then [`Lean4Lean.VEnv.Model.SoundAt.constDF, `Lean4Lean.VEnv.IsDefEqStrong.constDF]
      else []
    unless required.all visited.contains do
      throwError "model-soundness proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelSoundnessAudit
