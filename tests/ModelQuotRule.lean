import Lean4Lean.Theory.Typing.HeadInjectivity.Model.QuotRule
import Lean.Util.CollectAxioms

namespace ModelQuotRuleTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model
open scoped Lean4Lean.VEnv.Model

def one : VLevel := .succ .zero
def two : VLevel := .succ one
def altZero : VLevel := .max .zero .zero
def tag : Ob := .sort zeroF
def typeTag : Ob := .sort (fun _ => 1)

theorem zeroEq : VLevel.zero ≈ altZero :=
  VLevel.equiv_def.2 fun _ => by simp [altZero, VLevel.eval]

theorem distinctLevels : VLevel.zero ≠ altZero := by intro h; cases h

def firstName : Name := Name.mkSimple "DeltaBase"
def aliasName : Name := Name.mkSimple "DeltaAlias"
def firstValue : VDefVal := ⟨⟨⟨1, .sort (.succ (.param 0))⟩, firstName⟩, .sort (.param 0)⟩
def firstBase : VEnv := {
  constants n := if firstName = n then some firstValue.toVConstant else none
  defeqs _ := False }
def firstEnv : VEnv := firstBase.addDefEq firstValue.toDefEq
def aliasValue : VDefVal := ⟨⟨⟨1, .sort (.succ (.param 0))⟩, aliasName⟩,
  .const firstName [.param 0]⟩
def aliasBase : VEnv := {
  constants n := if aliasName = n then some aliasValue.toVConstant else firstEnv.constants n
  defeqs := firstEnv.defeqs }
def env : VEnv := aliasBase.addDefEq aliasValue.toDefEq

theorem firstHistory : firstEnv.WF' [.def firstValue] :=
  .decl (.def (ci := firstValue) (.sort (by decide)) rfl) .empty

theorem firstLookupAtSource : firstEnv.constants firstName = some firstValue.toVConstant := by
  simp [firstEnv, VEnv.addDefEq, firstBase]

theorem history : env.WF' [.def aliasValue, .def firstValue] := by
  refine .decl (.def (ci := aliasValue) ?_ rfl) firstHistory
  exact .const firstLookupAtSource (by intro l hl; cases List.mem_singleton.1 hl; decide) rfl

theorem envWF : env.WF := ⟨_, history⟩

theorem inclusion : firstEnv ≤ env :=
  (VEnv.addConst_le (show firstEnv.addConst aliasName aliasValue.toVConstant = some aliasBase from rfl)).trans
    VEnv.addDefEq_le

theorem noQuot : ¬ env.defeqs quotDefEq := by
  intro h
  rcases h with h | h | h
  · cases congrArg VDefEq.lhs h
  · cases congrArg VDefEq.lhs h
  · exact h

theorem firstRegistered : env.defeqs firstValue.toDefEq := .inr (.inl rfl)
theorem aliasRegistered : env.defeqs aliasValue.toDefEq := .inl rfl

theorem hasActualRules : ∃ df, env.defeqs df := ⟨_, aliasRegistered⟩

theorem firstLookup : env.constants firstName = some firstValue.toVConstant :=
  inclusion.constants firstLookupAtSource

theorem aliasLookup : env.constants aliasName = some aliasValue.toVConstant := by
  simp [env, VEnv.addDefEq, aliasBase]

theorem firstValid : RuleValid env firstValue.toDefEq :=
  RuleValid.delta_of_wf envWF firstRegistered rfl

theorem aliasValid : RuleValid env aliasValue.toDefEq :=
  RuleValid.delta_of_wf envWF aliasRegistered rfl

theorem firstHeadUnique (registered : env.defeqs df)
    (head : df.lhs.stripLams.appHead = .const firstName ls) : df = firstValue.toDefEq :=
  envWF.deltaRules.excl _ _ firstRegistered registered _ _ _ rfl head

theorem firstNotRigid : ¬ env.Rigid firstName :=
  fun h => h _ firstRegistered [.param 0] rfl

theorem firstNotConstructor : ¬ IsInstalledCtor env firstName :=
  fun h => firstNotRigid (envWF.installed_constructor_rigid h)

theorem firstConstStrong (hl : l.WF 0) :
    env.IsDefEqStrong 0 Γ (.const firstName [l]) (.const firstName [l]) (.sort (.succ l)) := by
  exact .constDF (u := .succ (.succ l)) firstLookup
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl)
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl)
    rfl (.cons rfl .nil) hl
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl)
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl)

theorem aliasConstStrong (hl : l.WF 0) :
    env.IsDefEqStrong 0 Γ (.const aliasName [l]) (.const aliasName [l]) (.sort (.succ l)) := by
  exact .constDF (u := .succ (.succ l)) aliasLookup
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl)
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl)
    rfl (.cons rfl .nil) hl
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl)
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl)

theorem firstStrong (hl : l.WF 0) :
    env.IsDefEqStrong 0 Γ (.const firstName [l]) (.sort l) (.sort (.succ l)) := by
  exact .extra (df := firstValue.toDefEq) (ls := [l]) (u := .succ (.succ l)) firstRegistered
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl) rfl hl
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl) (firstConstStrong hl) (.sortDF hl hl rfl)
    (firstConstStrong hl) (.sortDF hl hl rfl)

theorem aliasStrong (hl : l.WF 0) :
    env.IsDefEqStrong 0 Γ (.const aliasName [l]) (.const firstName [l]) (.sort (.succ l)) := by
  exact .extra (df := aliasValue.toDefEq) (ls := [l]) (u := .succ (.succ l)) aliasRegistered
    (by intro x hx; cases List.mem_singleton.1 hx; exact hl) rfl hl
    (.sortDF (l := .succ l) (l' := .succ l) hl hl rfl) (aliasConstStrong hl) (firstConstStrong hl)
    (aliasConstStrong hl) (firstConstStrong hl)

theorem twoUnfoldings : env.IsDefEqStrong 0 Γ (.const aliasName [altZero]) (.sort altZero)
    (.sort (.succ altZero)) :=
  (aliasStrong (by trivial)).trans (firstStrong (by trivial))

theorem bothSound : SoundAt env 0 [] Γ (.const aliasName [altZero]) (.sort altZero)
      (.sort (.succ altZero)) ∧
    HTS env 0 [] Γ (.const aliasName [altZero]) (.sort (.succ altZero)) ∧
    HTS env 0 [] Γ (.sort altZero) (.sort (.succ altZero)) :=
  sound_no_quot envWF envWF VEnv.LE.rfl noQuot (by trivial) twoUnfoldings

theorem aliasObserved : Obs env 0 [] .id .empty (.const aliasName [altZero]) tag := by
  obtain ⟨o, ho, le⟩ := (bothSound (Γ := [])).1 .id .id .empty .nil TV.empty TV.empty |>.2.1 tag
    (show Obs env 0 [] .id .empty (.sort altZero) tag from .sort)
  cases le.sort_inv
  exact ho

theorem forwardObserved : ∃ o, Obs env 0 [] .id .empty (.sort altZero) o ∧ o ≼ tag :=
  ((bothSound (Γ := [])).1 .id .id .empty .nil TV.empty TV.empty).1 _ aliasObserved

theorem aliasObservationTyped : TypedAt env 0 []
    (vcls env 0 [] .id (.const aliasName [altZero]) (.sort (.succ altZero)))
      .id .empty (.sort (.succ altZero)) tag :=
  ((bothSound (Γ := [])).1 .id .id .empty .nil TV.empty TV.empty).2.2.1 _ aliasObserved

def leftAnchor : VExpr.Subst := VExpr.Subst.id.cons (.sort .zero)
def rightAnchor : VExpr.Subst := VExpr.Subst.id.cons (.sort altZero)
def sets : ObSets := ObSets.empty.cons (listSet [tag])

theorem relatedAnchors : Ctx.SubstEq env 0 [] leftAnchor rightAnchor [.sort one] :=
  .cons .nil (.sort (by trivial)) (.sortDF (by trivial) (by trivial) zeroEq)

theorem sortBacked : Backed (listSet [tag]) := by
  intro o ho w hw
  cases List.mem_singleton.1 ho
  cases hw

theorem anchorTyped (a : VExpr) : TV env 0 [] [.sort one]
    (VExpr.Subst.id.cons a) sets :=
  TV.cons TV.empty sortBacked (fun o ho => by
    cases List.mem_singleton.1 ho
    exact ⟨[typeTag], fun τ hτ => by cases List.mem_singleton.1 hτ; exact .sort,
      .sort (.head _)⟩)

theorem underRelatedAnchors : ∃ o, Obs env 0 [] rightAnchor sets (.sort altZero) o ∧ o ≼ tag := by
  have observed : Obs env 0 [] leftAnchor sets (.const aliasName [altZero]) tag :=
    (Obs.closed_iff_id (by trivial)).2 aliasObserved
  exact ((bothSound (Γ := [.sort one])).1 leftAnchor rightAnchor sets relatedAnchors
    (anchorTyped _) (anchorTyped _)).1 _ observed

-- The target interpretation can contain the real quotient equation even though
-- validity for that equation is still open.
def equalityBase : VEnv := {
  constants n := if ``Eq = n then some eqConst else env.constants n
  defeqs := env.defeqs }
def mixedEnv : VEnv := equalityBase.addQuot |>.getD .empty

theorem equalityAdded : env.addConst ``Eq eqConst = some equalityBase := rfl

theorem mixedWF : mixedEnv.WF := by
  have equalityHistory : equalityBase.WF' (.axiom ⟨eqConst, ``Eq⟩ ::
      [.def aliasValue, .def firstValue]) := by
    refine .decl (.axiom (ci := ⟨eqConst, ``Eq⟩) ?_ equalityAdded) history
    exact ⟨_, by unfold eqConst; type_tac⟩
  have ready : equalityBase.QuotReady := by simp [QuotReady, equalityBase]
  exact ⟨_, .decl (.quot ready (show equalityBase.addQuot = some mixedEnv from rfl)) equalityHistory⟩

theorem mixedInclusion : env ≤ mixedEnv := by
  have installed : equalityBase.addQuot = some mixedEnv := rfl
  simp only [VEnv.addQuot, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at installed
  obtain ⟨q, hq, m, hm, l, hl, i, hi, result⟩ := installed
  rw [← result]
  exact (VEnv.addConst_le equalityAdded).trans <| (VEnv.addConst_le hq).trans <|
    (VEnv.addConst_le hm).trans <| (VEnv.addConst_le hl).trans <|
    (VEnv.addConst_le hi).trans VEnv.addDefEq_le

theorem mixedQuotRegistered : mixedEnv.defeqs quotDefEq :=
  addQuot_defeq (show equalityBase.addQuot = some mixedEnv from rfl)

theorem mixedConstructor : IsInstalledCtor mixedEnv ``Quot.mk :=
  ⟨quotDefEq, mixedQuotRegistered, quotConstructorMajor⟩

theorem mixedConstructorRigid : mixedEnv.Rigid ``Quot.mk :=
  mixedWF.installed_constructor_rigid mixedConstructor

theorem mixedDeltaValid : RuleValid mixedEnv aliasValue.toDefEq :=
  RuleValid.delta_of_wf mixedWF (mixedInclusion.defeqs aliasRegistered) rfl

theorem mixedSound : SoundAt mixedEnv 0 [] [] (.const aliasName [altZero]) (.sort altZero)
      (.sort (.succ altZero)) ∧
    HTS mixedEnv 0 [] [] (.const aliasName [altZero]) (.sort (.succ altZero)) ∧
    HTS mixedEnv 0 [] [] (.sort altZero) (.sort (.succ altZero)) :=
  sound_no_quot mixedWF envWF mixedInclusion noQuot (by trivial) twoUnfoldings

theorem mixedObserved : Obs mixedEnv 0 [] .id .empty (.const aliasName [altZero]) tag := by
  obtain ⟨o, ho, le⟩ := (mixedSound.1 .id .id .empty .nil TV.empty TV.empty).2.1 tag
    (show Obs mixedEnv 0 [] .id .empty (.sort altZero) tag from .sort)
  cases le.sort_inv
  exact ho

theorem mixedRejectsNoQuot : ¬ (¬ mixedEnv.defeqs quotDefEq) :=
  fun h => h mixedQuotRegistered

def functionName : Name := Name.mkSimple "DeltaIdentity"
def functionType : VExpr := .forallE (.sort one) (.sort one)
def functionBody : VExpr := .lam (.sort one) (.bvar 0)
def functionValue : VDefVal := ⟨⟨⟨0, functionType⟩, functionName⟩, functionBody⟩
def functionBase : VEnv := {
  constants n := if functionName = n then some functionValue.toVConstant else env.constants n
  defeqs := env.defeqs }
def functionEnv : VEnv := functionBase.addDefEq functionValue.toDefEq

theorem functionWF : functionEnv.WF := by
  refine ⟨_, .decl (.def (ci := functionValue) ?_ rfl) history⟩
  exact .lamDF (HasType.sort (by trivial)) (.bvar .zero)

theorem functionNoQuot : ¬ functionEnv.defeqs quotDefEq := by
  intro h
  rcases h with h | h
  · cases congrArg VDefEq.lhs h
  · exact noQuot h

theorem functionRegistered : functionEnv.defeqs functionValue.toDefEq := .inl rfl

theorem functionLookup : functionEnv.constants functionName = some functionValue.toVConstant := by
  simp [functionEnv, VEnv.addDefEq, functionBase]

theorem functionTypeStrong : functionEnv.IsDefEqStrong 0 Γ functionType functionType
    (.sort (.imax two two)) :=
  .forallEDF (by trivial) (by trivial) (.sortDF (by trivial) (by trivial) rfl)
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)

theorem functionBodyStrong : functionEnv.IsDefEqStrong 0 Γ functionBody functionBody functionType :=
  .lamDF (by trivial) (by trivial) (.sortDF (by trivial) (by trivial) rfl)
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)
    (.bvar .zero (by trivial) (.sortDF (by trivial) (by trivial) rfl))
    (.bvar .zero (by trivial) (.sortDF (by trivial) (by trivial) rfl))

theorem functionConstStrong : functionEnv.IsDefEqStrong 0 Γ
    (.const functionName []) (.const functionName []) functionType :=
  .constDF functionLookup nofun nofun rfl .nil (by trivial) functionTypeStrong functionTypeStrong

theorem functionDeltaStrong : functionEnv.IsDefEqStrong 0 Γ
    (.const functionName []) functionBody functionType :=
  .extra (ls := []) (u := .imax two two) functionRegistered nofun rfl (by trivial) functionTypeStrong functionConstStrong
    functionBodyStrong functionConstStrong functionBodyStrong

theorem functionDeltaSound : SoundAt functionEnv 0 [] Γ
    (.const functionName []) functionBody functionType :=
  (sound_no_quot functionWF functionWF VEnv.LE.rfl functionNoQuot (by trivial) functionDeltaStrong).1

def argumentD : VExpr → Prop := TyCls functionEnv 0 [] (.sort one)
def argumentC : VExpr → Prop := ElCls functionEnv 0 [] argumentD (.sort .zero)
def functionObservation : Ob := .app argumentD argumentC [tag, tag] tag

theorem argumentTyped : TypedElCls functionEnv 0 [] argumentD argumentC :=
  .of_hasType (HasType.sort (by trivial))

theorem duplicateBacked : Backed (listSet [tag, tag]) := by
  intro o ho w hw
  have : o = tag := by simpa [listSet] using ho
  subst o
  cases hw

theorem functionBodyObserved : Obs functionEnv 0 [] .id .empty functionBody functionObservation := by
  refine .lam (τs := [typeTag]) argumentTyped ?_ ?_ duplicateBacked ElCls.self (.bvar (.head _))
  · intro τ hτ; cases List.mem_singleton.1 hτ; exact .sort
  · intro k hk
    have : k = tag := by simpa using hk
    subst k
    exact .sort (.head _)

theorem functionHeadObserved : ∃ o,
    Obs functionEnv 0 [] .id .empty (.const functionName []) o ∧ o ≼ functionObservation :=
  (functionDeltaSound (Γ := []) .id .id .empty .nil TV.empty TV.empty).2.1 _ functionBodyObserved

theorem functionHeadTyped : ∃ o,
    Obs functionEnv 0 [] .id .empty (.const functionName []) o ∧ o ≼ functionObservation ∧
    TypedAt functionEnv 0 [] (vcls functionEnv 0 [] .id (.const functionName []) functionType)
      .id .empty functionType o := by
  obtain ⟨o, ho, le⟩ := functionHeadObserved
  exact ⟨o, ho, le, (functionDeltaSound (Γ := []) .id .id .empty .nil TV.empty TV.empty).2.2.1 _ ho⟩

theorem functionApplicationObserved : Obs functionEnv 0 [] .id .empty
    (.app (.const functionName []) (.sort .zero)) tag := by
  obtain ⟨o, ho, le⟩ := functionHeadObserved
  obtain ⟨K, y, rfl, cover, le⟩ := le.app_inv
  cases le.sort_inv
  refine .app ho rfl (K' := [tag, tag]) ?_ cover
  intro k hk
  have : k = tag := by simpa using hk
  subst k
  exact .sort

theorem functionApplicationStrong : functionEnv.IsDefEqStrong 0 Γ
    (.app (.const functionName []) (.sort .zero))
    (.app (.const functionName []) (.sort .zero)) (.sort one) :=
  .appDF (by trivial) (by trivial) (.sortDF (by trivial) (by trivial) rfl)
    (.sortDF (by trivial) (by trivial) rfl) functionConstStrong
    (.sortDF (by trivial) (by trivial) rfl) (.sortDF (by trivial) (by trivial) rfl)

theorem functionApplicationTyped : TypedAt functionEnv 0 []
    (vcls functionEnv 0 [] .id (.app (.const functionName []) (.sort .zero)) (.sort one))
    .id .empty (.sort one) tag := by
  have h := sound_no_quot (Δ := []) functionWF functionWF VEnv.LE.rfl functionNoQuot
    (by trivial) (functionApplicationStrong (Γ := []))
  exact (h.1 .id .id .empty .nil TV.empty TV.empty).2.2.1 _ functionApplicationObserved

/-- Both actual rule kinds in the same checked target are valid. -/
theorem allMixedRulesValid {df : VDefEq} (h : mixedEnv.defeqs df) : RuleValid mixedEnv df :=
  RuleValid.of_wf mixedWF h

theorem mixedQuotientValid : RuleValid mixedEnv quotDefEq :=
  RuleValid.quot_of_wf mixedWF mixedQuotRegistered

theorem actualQuotientLookups : QuotConsts mixedEnv :=
  QuotConsts.of_wf mixedWF mixedQuotRegistered

theorem actualQuotientRigid : mixedEnv.Rigid ``Quot :=
  quotient_rigid mixedWF mixedQuotRegistered

/-- The source itself contains BOTH delta and quotient equations. -/
theorem mixedSourceSound : SoundAt mixedEnv 0 [] [] (.const aliasName [altZero]) (.sort altZero)
      (.sort (.succ altZero)) ∧
    HTS mixedEnv 0 [] [] (.const aliasName [altZero]) (.sort (.succ altZero)) ∧
    HTS mixedEnv 0 [] [] (.sort altZero) (.sort (.succ altZero)) :=
  sound_of_wf mixedWF mixedWF VEnv.LE.rfl (by trivial) (twoUnfoldings.mono mixedInclusion)

/-- Recover a positive observation using the unrestricted theorem. -/
theorem mixedSourceObserved : Obs mixedEnv 0 [] .id .empty (.const aliasName [altZero]) tag := by
  obtain ⟨o, ho, le⟩ := (mixedSourceSound.1 .id .id .empty .nil TV.empty TV.empty).2.1 tag
    (show Obs mixedEnv 0 [] .id .empty (.sort altZero) tag from .sort)
  cases le.sort_inv
  exact ho

/-- A genuinely nonzero source cannot satisfy the proposition-mode indicator. -/
theorem nonzeroRejectsIndicator {keys : List Key} (hlen : keys.length = quotLead.length)
    (h : Obs mixedEnv 0 [] .id .empty (quotLiftConst.type.instL [one, one])
      (piCodChain keys (.piDomOb (.rigid ``Quot [fun _ => 1] 2 zeroF)))) : False := by
  have hz := quot_C_level actualQuotientLookups actualQuotientRigid hlen h
  have impossible : 1 = 0 := congrFun hz []
  cases impossible

namespace ModeC

def levels : List VLevel := [altZero, one]
def domains : List VExpr := quotDoms.map (·.instL levels)
def locals : List VExpr := domains.reverse

theorem domainsShape : domains = (quotLiftDoms.take 5 ++ [VExpr.bvar 4]).map (·.instL levels) := rfl

theorem levelsWF : ∀ l ∈ levels, l.WF 0 := by
  intro l hl
  simp only [levels, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl <;> trivial

theorem vanished : ((VLevel.param 0).inst levels).eval = zeroF := rfl

theorem contextWF : OnCtx locals (mixedEnv.IsType 0) := by
  have eqLookup : mixedEnv.constants ``Eq = some eqConst := rfl
  unfold locals
  rw [domainsShape]
  unfold quotLiftDoms levels altZero one
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩,
    _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩

theorem anchorTyped : Ctx.SubstEq mixedEnv 0 locals .id .id (domains.reverse ++ []) := by
  simpa only [List.append_nil, locals] using Ctx.SubstEq.id mixedWF.ordered contextWF

/-- The real sixth binder has a proposition as its actual type, even for a
syntactically noncanonical zero universe. -/
theorem fieldIsProof : (∃ P, TyCls mixedEnv 0 locals ((binderTy quotDoms levels 0).subst .id) P ∧
      mixedEnv.HasType 0 locals P (.sort .zero)) ∧
    ∀ τ, Obs mixedEnv 0 locals .id .empty (binderTy quotDoms levels 0) τ →
      ∃ cv', TypedOb mixedEnv 0 locals cv' τ [.sort zeroF] := by
  exact quot_pf levelsWF vanished 0 (by decide) (by intro i; cases i with
      | zero => intro h; cases h
      | succ i => cases i with
        | zero => intro h; cases h
        | succ i => cases i with
          | zero => intro h; cases h
          | succ i => cases i with
            | zero => intro h; cases h
            | succ i => cases i <;> (intro h; cases h))
    .id .empty anchorTyped TV.empty

theorem fieldActualType : mixedEnv.HasType 0 locals (.bvar 5) (.sort .zero) := by
  have h : mixedEnv.HasType 0 locals (.bvar 5) (.sort altZero) := .bvar (by
    unfold locals
    rw [domainsShape]
    unfold quotLiftDoms levels
    lookup_tac)
  exact (IsDefEq.sortDF (by trivial) (by trivial) zeroEq.symm).defeqDF h


def marker : Ob := .piDom (fun _ => False)
def nonemptySets : ObSets := fun i o => i = 5 ∧ o = marker

theorem alphaLookup : Lookup locals 5 (.sort altZero) := by
  unfold locals
  rw [domainsShape]
  unfold quotLiftDoms levels
  lookup_tac

/-- A positive proposition observation at alpha is typed by its actual sort. -/
theorem valuationTyped : TV mixedEnv 0 locals locals .id nonemptySets := by
  refine ⟨?_, ?_⟩
  · intro i o ho w hw
    obtain ⟨hi, he⟩ := ho
    subst o
    cases hw
  · intro i A hL o ho
    obtain ⟨rfl, he⟩ := ho
    subst o
    cases hL.uniq alphaLookup
    exact ⟨[.sort zeroF], fun τ h => by cases List.mem_singleton.1 h; exact .sort,
      .piDom (.head _)⟩

theorem positiveFieldTypeObservation : Obs mixedEnv 0 locals .id nonemptySets
    (binderTy quotDoms levels 0) marker := .bvar ⟨rfl, rfl⟩

theorem positiveFieldTypeTyped : ∃ cv', TypedOb mixedEnv 0 locals cv' marker [.sort zeroF] := by
  have h := quot_pf levelsWF vanished 0 (by decide)
    (fun i he => by
      have hx := List.getElem?_eq_some_iff.1 he
      have hm := hx.2
      have hmem := List.getElem_mem hx.1
      rw [hm] at hmem
      simp [quotLead] at hmem)
    .id nonemptySets anchorTyped valuationTyped
  exact h.2 marker positiveFieldTypeObservation

end ModeC

end ModelQuotRuleTest

namespace ModelQuotRuleAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.Model.lamDoms,
    `Lean4Lean.VEnv.Model.quotDoms,
    `Lean4Lean.VEnv.Model.quotLead,
    `Lean4Lean.VEnv.Model.quotDefEq_lhs,
    `Lean4Lean.VEnv.Model.quotDefEq_rhs,
    `Lean4Lean.VEnv.Model.quotDoms_length,
    `Lean4Lean.VEnv.Model.quot_cov,
    `Lean4Lean.VEnv.Model.QuotConsts,
    `Lean4Lean.VEnv.Model.quotLiftDoms,
    `Lean4Lean.VEnv.Model.quotLiftConst_type,
    `Lean4Lean.VEnv.Model.chain_terminal_sort,
    `Lean4Lean.VEnv.Model.quot_lead_x,
    `Lean4Lean.VEnv.Model.quot_binderTy0,
    `Lean4Lean.VEnv.Model.quot_binderTy5,
    `Lean4Lean.VEnv.Model.tele_obs_inv,
    `Lean4Lean.VEnv.Model.quot_C_level,
    `Lean4Lean.VEnv.Model.quot_pf,
    `Lean4Lean.VEnv.Model.quot_uniq,
    `Lean4Lean.VEnv.Model.QuotConsts.of_wf,
    `Lean4Lean.VEnv.Model.quotient_rigid,
    `Lean4Lean.VEnv.Model.RuleValid.quot_of_wf,
    `Lean4Lean.VEnv.Model.RuleValid.of_wf,
    `Lean4Lean.VEnv.Model.sound_of_wf,
    `ModelQuotRuleTest.one,
    `ModelQuotRuleTest.two,
    `ModelQuotRuleTest.altZero,
    `ModelQuotRuleTest.tag,
    `ModelQuotRuleTest.typeTag,
    `ModelQuotRuleTest.zeroEq,
    `ModelQuotRuleTest.distinctLevels,
    `ModelQuotRuleTest.firstName,
    `ModelQuotRuleTest.aliasName,
    `ModelQuotRuleTest.firstValue,
    `ModelQuotRuleTest.firstBase,
    `ModelQuotRuleTest.firstEnv,
    `ModelQuotRuleTest.aliasValue,
    `ModelQuotRuleTest.aliasBase,
    `ModelQuotRuleTest.env,
    `ModelQuotRuleTest.firstHistory,
    `ModelQuotRuleTest.firstLookupAtSource,
    `ModelQuotRuleTest.history,
    `ModelQuotRuleTest.envWF,
    `ModelQuotRuleTest.inclusion,
    `ModelQuotRuleTest.noQuot,
    `ModelQuotRuleTest.firstRegistered,
    `ModelQuotRuleTest.aliasRegistered,
    `ModelQuotRuleTest.hasActualRules,
    `ModelQuotRuleTest.firstLookup,
    `ModelQuotRuleTest.aliasLookup,
    `ModelQuotRuleTest.firstValid,
    `ModelQuotRuleTest.aliasValid,
    `ModelQuotRuleTest.firstHeadUnique,
    `ModelQuotRuleTest.firstNotRigid,
    `ModelQuotRuleTest.firstNotConstructor,
    `ModelQuotRuleTest.firstConstStrong,
    `ModelQuotRuleTest.aliasConstStrong,
    `ModelQuotRuleTest.firstStrong,
    `ModelQuotRuleTest.aliasStrong,
    `ModelQuotRuleTest.twoUnfoldings,
    `ModelQuotRuleTest.bothSound,
    `ModelQuotRuleTest.aliasObserved,
    `ModelQuotRuleTest.forwardObserved,
    `ModelQuotRuleTest.aliasObservationTyped,
    `ModelQuotRuleTest.leftAnchor,
    `ModelQuotRuleTest.rightAnchor,
    `ModelQuotRuleTest.sets,
    `ModelQuotRuleTest.relatedAnchors,
    `ModelQuotRuleTest.sortBacked,
    `ModelQuotRuleTest.anchorTyped,
    `ModelQuotRuleTest.underRelatedAnchors,
    `ModelQuotRuleTest.equalityBase,
    `ModelQuotRuleTest.mixedEnv,
    `ModelQuotRuleTest.equalityAdded,
    `ModelQuotRuleTest.mixedWF,
    `ModelQuotRuleTest.mixedInclusion,
    `ModelQuotRuleTest.mixedQuotRegistered,
    `ModelQuotRuleTest.mixedConstructor,
    `ModelQuotRuleTest.mixedConstructorRigid,
    `ModelQuotRuleTest.mixedDeltaValid,
    `ModelQuotRuleTest.mixedSound,
    `ModelQuotRuleTest.mixedObserved,
    `ModelQuotRuleTest.mixedRejectsNoQuot,
    `ModelQuotRuleTest.functionName,
    `ModelQuotRuleTest.functionType,
    `ModelQuotRuleTest.functionBody,
    `ModelQuotRuleTest.functionValue,
    `ModelQuotRuleTest.functionBase,
    `ModelQuotRuleTest.functionEnv,
    `ModelQuotRuleTest.functionWF,
    `ModelQuotRuleTest.functionNoQuot,
    `ModelQuotRuleTest.functionRegistered,
    `ModelQuotRuleTest.functionLookup,
    `ModelQuotRuleTest.functionTypeStrong,
    `ModelQuotRuleTest.functionBodyStrong,
    `ModelQuotRuleTest.functionConstStrong,
    `ModelQuotRuleTest.functionDeltaStrong,
    `ModelQuotRuleTest.functionDeltaSound,
    `ModelQuotRuleTest.argumentD,
    `ModelQuotRuleTest.argumentC,
    `ModelQuotRuleTest.functionObservation,
    `ModelQuotRuleTest.argumentTyped,
    `ModelQuotRuleTest.duplicateBacked,
    `ModelQuotRuleTest.functionBodyObserved,
    `ModelQuotRuleTest.functionHeadObserved,
    `ModelQuotRuleTest.functionHeadTyped,
    `ModelQuotRuleTest.functionApplicationObserved,
    `ModelQuotRuleTest.functionApplicationStrong,
    `ModelQuotRuleTest.functionApplicationTyped,
    `ModelQuotRuleTest.allMixedRulesValid,
    `ModelQuotRuleTest.mixedQuotientValid,
    `ModelQuotRuleTest.actualQuotientLookups,
    `ModelQuotRuleTest.actualQuotientRigid,
    `ModelQuotRuleTest.mixedSourceSound,
    `ModelQuotRuleTest.mixedSourceObserved,
    `ModelQuotRuleTest.nonzeroRejectsIndicator,
    `ModelQuotRuleTest.ModeC.levels,
    `ModelQuotRuleTest.ModeC.domains,
    `ModelQuotRuleTest.ModeC.locals,
    `ModelQuotRuleTest.ModeC.domainsShape,
    `ModelQuotRuleTest.ModeC.levelsWF,
    `ModelQuotRuleTest.ModeC.vanished,
    `ModelQuotRuleTest.ModeC.contextWF,
    `ModelQuotRuleTest.ModeC.anchorTyped,
    `ModelQuotRuleTest.ModeC.fieldIsProof,
    `ModelQuotRuleTest.ModeC.fieldActualType,
    `ModelQuotRuleTest.ModeC.marker,
    `ModelQuotRuleTest.ModeC.nonemptySets,
    `ModelQuotRuleTest.ModeC.alphaLookup,
    `ModelQuotRuleTest.ModeC.valuationTyped,
    `ModelQuotRuleTest.ModeC.positiveFieldTypeObservation,
    `ModelQuotRuleTest.ModeC.positiveFieldTypeTyped]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.Model.lamDoms, [`propext]),
    (`Lean4Lean.VEnv.Model.quotDoms, [`propext]),
    (`Lean4Lean.VEnv.Model.quotLead, []),
    (`Lean4Lean.VEnv.Model.quotDefEq_lhs, [`propext]),
    (`Lean4Lean.VEnv.Model.quotDefEq_rhs, [`propext]),
    (`Lean4Lean.VEnv.Model.quotDoms_length, [`propext]),
    (`Lean4Lean.VEnv.Model.quot_cov, [`propext]),
    (`Lean4Lean.VEnv.Model.QuotConsts, []),
    (`Lean4Lean.VEnv.Model.quotLiftDoms, []),
    (`Lean4Lean.VEnv.Model.quotLiftConst_type, []),
    (`Lean4Lean.VEnv.Model.chain_terminal_sort, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quot_lead_x, [`propext]),
    (`Lean4Lean.VEnv.Model.quot_binderTy0, [`propext]),
    (`Lean4Lean.VEnv.Model.quot_binderTy5, [`propext]),
    (`Lean4Lean.VEnv.Model.tele_obs_inv, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quot_C_level, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quot_pf, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quot_uniq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.QuotConsts.of_wf, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quotient_rigid, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RuleValid.quot_of_wf, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RuleValid.of_wf, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.sound_of_wf, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.one, []),
    (`ModelQuotRuleTest.two, []),
    (`ModelQuotRuleTest.altZero, []),
    (`ModelQuotRuleTest.tag, []),
    (`ModelQuotRuleTest.typeTag, []),
    (`ModelQuotRuleTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.distinctLevels, []),
    (`ModelQuotRuleTest.firstName, []),
    (`ModelQuotRuleTest.aliasName, []),
    (`ModelQuotRuleTest.firstValue, []),
    (`ModelQuotRuleTest.firstBase, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstEnv, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasValue, []),
    (`ModelQuotRuleTest.aliasBase, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.env, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstHistory, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstLookupAtSource, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.history, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.envWF, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.inclusion, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.noQuot, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstRegistered, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasRegistered, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.hasActualRules, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstLookup, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasLookup, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstValid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasValid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstHeadUnique, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstNotRigid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstNotConstructor, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstConstStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasConstStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.firstStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.twoUnfoldings, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.bothSound, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.forwardObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.aliasObservationTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.leftAnchor, []),
    (`ModelQuotRuleTest.rightAnchor, []),
    (`ModelQuotRuleTest.sets, []),
    (`ModelQuotRuleTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.sortBacked, [`propext]),
    (`ModelQuotRuleTest.anchorTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.underRelatedAnchors, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.equalityBase, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedEnv, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.equalityAdded, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedWF, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedInclusion, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedQuotRegistered, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedConstructor, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedConstructorRigid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedDeltaValid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedSound, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedRejectsNoQuot, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionName, []),
    (`ModelQuotRuleTest.functionType, []),
    (`ModelQuotRuleTest.functionBody, []),
    (`ModelQuotRuleTest.functionValue, []),
    (`ModelQuotRuleTest.functionBase, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionEnv, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionWF, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionNoQuot, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionRegistered, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionLookup, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionTypeStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionBodyStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionConstStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionDeltaStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionDeltaSound, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.argumentD, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.argumentC, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionObservation, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.argumentTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.duplicateBacked, [`propext]),
    (`ModelQuotRuleTest.functionBodyObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionHeadObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionHeadTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionApplicationObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionApplicationStrong, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.functionApplicationTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.allMixedRulesValid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedQuotientValid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.actualQuotientLookups, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.actualQuotientRigid, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedSourceSound, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.mixedSourceObserved, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.nonzeroRejectsIndicator, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.levels, []),
    (`ModelQuotRuleTest.ModeC.domains, [`propext]),
    (`ModelQuotRuleTest.ModeC.locals, [`propext]),
    (`ModelQuotRuleTest.ModeC.domainsShape, [`propext]),
    (`ModelQuotRuleTest.ModeC.levelsWF, [`propext]),
    (`ModelQuotRuleTest.ModeC.vanished, [`propext]),
    (`ModelQuotRuleTest.ModeC.contextWF, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.anchorTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.fieldIsProof, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.fieldActualType, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.marker, []),
    (`ModelQuotRuleTest.ModeC.nonemptySets, []),
    (`ModelQuotRuleTest.ModeC.alphaLookup, [`propext]),
    (`ModelQuotRuleTest.ModeC.valuationTyped, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.positiveFieldTypeObservation, [`Quot.sound, `propext]),
    (`ModelQuotRuleTest.ModeC.positiveFieldTypeTyped, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-quotrule manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-quotrule manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-quotrule axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-quotrule admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-quotrule value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-quotrule dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-quotrule type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-quotrule admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-quotrule dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-quotrule traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-quotrule axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.Model.quot_C_level then [`Lean4Lean.VEnv.Model.Obs.const_iff, `Lean4Lean.VEnv.Model.chain_terminal_sort, `Lean4Lean.VEnv.Model.tele_obs_inv, `Lean4Lean.VEnv.Model.wrap_of_obs_mkApps_le]
      else if root == `Lean4Lean.VEnv.Model.quot_pf then [`Lean4Lean.VEnv.Model.quot_lead_x, `Lean4Lean.VEnv.Model.lookup_binderTy, `Lean4Lean.VEnv.Model.quot_binderTy0, `Lean4Lean.VEnv.Model.quot_binderTy5, `Lean4Lean.VEnv.Model.typedAt_sort_iff, `Lean4Lean.VEnv.IsDefEq.sortDF]
      else if root == `Lean4Lean.VEnv.Model.QuotConsts.of_wf then [`Lean4Lean.VEnv.WF.quotientObjects]
      else if root == `Lean4Lean.VEnv.Model.quotient_rigid then [`Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VEnv.RewriteMetadata.quotientNames, `Lean4Lean.VEnv.WF.rewriteMetadata]
      else if root == `Lean4Lean.VEnv.Model.RuleValid.quot_of_wf then [`Lean4Lean.VEnv.Model.sound_pat, `Lean4Lean.VEnv.Model.quot_pf, `Lean4Lean.VEnv.Model.quot_C_level, `Lean4Lean.VEnv.Model.quot_uniq, `Lean4Lean.VEnv.Model.QuotConsts.of_wf, `Lean4Lean.VEnv.Model.quotient_rigid, `Lean4Lean.VEnv.Model.RewriteMetadata.quot_head_unique, `Lean4Lean.VEnv.WF.installed_constructor_rigid, `Lean4Lean.VEnv.WF.deltaRules, `Lean4Lean.VEnv.IsDefEq.extra, `Lean4Lean.VEnv.Model.RuleValid]
      else if root == `Lean4Lean.VEnv.Model.RuleValid.of_wf then [`Lean4Lean.VEnv.Model.RuleValid.quot_of_wf, `Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `Lean4Lean.VEnv.RewriteMetadata.classify]
      else if root == `Lean4Lean.VEnv.Model.sound_of_wf then [`Lean4Lean.VEnv.Model.sound, `Lean4Lean.VEnv.Model.RuleValid.quot_of_wf, `Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VEnv.LE.defeqs]
      else if root == `ModelQuotRuleTest.mixedQuotientValid then [`Lean4Lean.VEnv.Model.RuleValid.quot_of_wf, `ModelQuotRuleTest.mixedWF, `ModelQuotRuleTest.mixedQuotRegistered]
      else if root == `ModelQuotRuleTest.allMixedRulesValid then [`Lean4Lean.VEnv.Model.RuleValid.of_wf, `ModelQuotRuleTest.mixedWF]
      else if root == `ModelQuotRuleTest.mixedSourceSound then [`Lean4Lean.VEnv.Model.sound_of_wf, `ModelQuotRuleTest.mixedWF, `ModelQuotRuleTest.twoUnfoldings, `Lean4Lean.VEnv.IsDefEqStrong.extra]
      else if root == `ModelQuotRuleTest.mixedSourceObserved then [`ModelQuotRuleTest.mixedSourceSound, `Lean4Lean.VEnv.Model.TV.empty]
      else if root == `ModelQuotRuleTest.nonzeroRejectsIndicator then [`Lean4Lean.VEnv.Model.quot_C_level, `ModelQuotRuleTest.actualQuotientLookups, `ModelQuotRuleTest.actualQuotientRigid]
      else if root == `ModelQuotRuleTest.ModeC.fieldIsProof then [`Lean4Lean.VEnv.Model.quot_pf, `ModelQuotRuleTest.ModeC.anchorTyped, `ModelQuotRuleTest.ModeC.contextWF]
      else if root == `ModelQuotRuleTest.ModeC.positiveFieldTypeTyped then [`Lean4Lean.VEnv.Model.quot_pf, `ModelQuotRuleTest.ModeC.valuationTyped, `ModelQuotRuleTest.ModeC.positiveFieldTypeObservation, `ModelQuotRuleTest.ModeC.anchorTyped]
      else if root == `ModelQuotRuleTest.functionHeadTyped then [`ModelQuotRuleTest.functionHeadObserved, `ModelQuotRuleTest.functionDeltaSound, `ModelQuotRuleTest.functionDeltaStrong, `Lean4Lean.VEnv.IsDefEqStrong.extra]
      else []
    unless required.all visited.contains do
      throwError "model-quotrule proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelQuotRuleAudit
