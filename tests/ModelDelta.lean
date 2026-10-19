import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Delta
import Lean.Util.CollectAxioms

namespace ModelDeltaTest
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

end ModelDeltaTest

namespace ModelDeltaAudit
open Lean

run_meta
  let roots : List Name := [
    `Lean4Lean.VEnv.DeltaRules,
    `Lean4Lean.VEnv.RewriteMetadata.deltaRules,
    `Lean4Lean.VEnv.WF.deltaRules,
    `Lean4Lean.VEnv.Model.quotConstructorMajor,
    `Lean4Lean.VEnv.Model.RewriteMetadata.installedCtor,
    `Lean4Lean.VEnv.WF.installed_constructor_rigid,
    `Lean4Lean.VEnv.Model.wrapLams_mkApps_head,
    `Lean4Lean.VEnv.Model.wrapLams_mkApps_ne_const,
    `Lean4Lean.VEnv.Model.RuleValid.delta,
    `Lean4Lean.VEnv.Model.RuleValid.delta_of_wf,
    `Lean4Lean.VEnv.Model.sound_no_quot,
    `Lean4Lean.VEnv.DeltaRules.mk,
    `Lean4Lean.VEnv.DeltaRules.const,
    `Lean4Lean.VEnv.DeltaRules.excl,
    `ModelDeltaTest.one,
    `ModelDeltaTest.two,
    `ModelDeltaTest.altZero,
    `ModelDeltaTest.tag,
    `ModelDeltaTest.typeTag,
    `ModelDeltaTest.zeroEq,
    `ModelDeltaTest.distinctLevels,
    `ModelDeltaTest.firstName,
    `ModelDeltaTest.aliasName,
    `ModelDeltaTest.firstValue,
    `ModelDeltaTest.firstBase,
    `ModelDeltaTest.firstEnv,
    `ModelDeltaTest.aliasValue,
    `ModelDeltaTest.aliasBase,
    `ModelDeltaTest.env,
    `ModelDeltaTest.firstHistory,
    `ModelDeltaTest.firstLookupAtSource,
    `ModelDeltaTest.history,
    `ModelDeltaTest.envWF,
    `ModelDeltaTest.inclusion,
    `ModelDeltaTest.noQuot,
    `ModelDeltaTest.firstRegistered,
    `ModelDeltaTest.aliasRegistered,
    `ModelDeltaTest.hasActualRules,
    `ModelDeltaTest.firstLookup,
    `ModelDeltaTest.aliasLookup,
    `ModelDeltaTest.firstValid,
    `ModelDeltaTest.aliasValid,
    `ModelDeltaTest.firstHeadUnique,
    `ModelDeltaTest.firstNotRigid,
    `ModelDeltaTest.firstNotConstructor,
    `ModelDeltaTest.firstConstStrong,
    `ModelDeltaTest.aliasConstStrong,
    `ModelDeltaTest.firstStrong,
    `ModelDeltaTest.aliasStrong,
    `ModelDeltaTest.twoUnfoldings,
    `ModelDeltaTest.bothSound,
    `ModelDeltaTest.aliasObserved,
    `ModelDeltaTest.forwardObserved,
    `ModelDeltaTest.aliasObservationTyped,
    `ModelDeltaTest.leftAnchor,
    `ModelDeltaTest.rightAnchor,
    `ModelDeltaTest.sets,
    `ModelDeltaTest.relatedAnchors,
    `ModelDeltaTest.sortBacked,
    `ModelDeltaTest.anchorTyped,
    `ModelDeltaTest.underRelatedAnchors,
    `ModelDeltaTest.equalityBase,
    `ModelDeltaTest.mixedEnv,
    `ModelDeltaTest.equalityAdded,
    `ModelDeltaTest.mixedWF,
    `ModelDeltaTest.mixedInclusion,
    `ModelDeltaTest.mixedQuotRegistered,
    `ModelDeltaTest.mixedConstructor,
    `ModelDeltaTest.mixedConstructorRigid,
    `ModelDeltaTest.mixedDeltaValid,
    `ModelDeltaTest.mixedSound,
    `ModelDeltaTest.mixedObserved,
    `ModelDeltaTest.mixedRejectsNoQuot,
    `ModelDeltaTest.functionName,
    `ModelDeltaTest.functionType,
    `ModelDeltaTest.functionBody,
    `ModelDeltaTest.functionValue,
    `ModelDeltaTest.functionBase,
    `ModelDeltaTest.functionEnv,
    `ModelDeltaTest.functionWF,
    `ModelDeltaTest.functionNoQuot,
    `ModelDeltaTest.functionRegistered,
    `ModelDeltaTest.functionLookup,
    `ModelDeltaTest.functionTypeStrong,
    `ModelDeltaTest.functionBodyStrong,
    `ModelDeltaTest.functionConstStrong,
    `ModelDeltaTest.functionDeltaStrong,
    `ModelDeltaTest.functionDeltaSound,
    `ModelDeltaTest.argumentD,
    `ModelDeltaTest.argumentC,
    `ModelDeltaTest.functionObservation,
    `ModelDeltaTest.argumentTyped,
    `ModelDeltaTest.duplicateBacked,
    `ModelDeltaTest.functionBodyObserved,
    `ModelDeltaTest.functionHeadObserved,
    `ModelDeltaTest.functionHeadTyped,
    `ModelDeltaTest.functionApplicationObserved,
    `ModelDeltaTest.functionApplicationStrong,
    `ModelDeltaTest.functionApplicationTyped]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.DeltaRules, [`propext]),
    (`Lean4Lean.VEnv.RewriteMetadata.deltaRules, [`propext]),
    (`Lean4Lean.VEnv.WF.deltaRules, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.quotConstructorMajor, [`propext]),
    (`Lean4Lean.VEnv.Model.RewriteMetadata.installedCtor, [`propext]),
    (`Lean4Lean.VEnv.WF.installed_constructor_rigid, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrapLams_mkApps_head, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.wrapLams_mkApps_ne_const, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RuleValid.delta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.sound_no_quot, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.DeltaRules.mk, [`propext]),
    (`Lean4Lean.VEnv.DeltaRules.const, [`propext]),
    (`Lean4Lean.VEnv.DeltaRules.excl, [`propext]),
    (`ModelDeltaTest.one, []),
    (`ModelDeltaTest.two, []),
    (`ModelDeltaTest.altZero, []),
    (`ModelDeltaTest.tag, []),
    (`ModelDeltaTest.typeTag, []),
    (`ModelDeltaTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelDeltaTest.distinctLevels, []),
    (`ModelDeltaTest.firstName, []),
    (`ModelDeltaTest.aliasName, []),
    (`ModelDeltaTest.firstValue, []),
    (`ModelDeltaTest.firstBase, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstEnv, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasValue, []),
    (`ModelDeltaTest.aliasBase, [`Quot.sound, `propext]),
    (`ModelDeltaTest.env, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstHistory, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstLookupAtSource, [`Quot.sound, `propext]),
    (`ModelDeltaTest.history, [`Quot.sound, `propext]),
    (`ModelDeltaTest.envWF, [`Quot.sound, `propext]),
    (`ModelDeltaTest.inclusion, [`Quot.sound, `propext]),
    (`ModelDeltaTest.noQuot, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstRegistered, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasRegistered, [`Quot.sound, `propext]),
    (`ModelDeltaTest.hasActualRules, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstLookup, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasLookup, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstValid, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasValid, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstHeadUnique, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstNotRigid, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstNotConstructor, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstConstStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasConstStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.firstStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.twoUnfoldings, [`Quot.sound, `propext]),
    (`ModelDeltaTest.bothSound, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.forwardObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.aliasObservationTyped, [`Quot.sound, `propext]),
    (`ModelDeltaTest.leftAnchor, []),
    (`ModelDeltaTest.rightAnchor, []),
    (`ModelDeltaTest.sets, []),
    (`ModelDeltaTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelDeltaTest.sortBacked, [`propext]),
    (`ModelDeltaTest.anchorTyped, [`Quot.sound, `propext]),
    (`ModelDeltaTest.underRelatedAnchors, [`Quot.sound, `propext]),
    (`ModelDeltaTest.equalityBase, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedEnv, [`Quot.sound, `propext]),
    (`ModelDeltaTest.equalityAdded, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedWF, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedInclusion, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedQuotRegistered, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedConstructor, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedConstructorRigid, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedDeltaValid, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedSound, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.mixedRejectsNoQuot, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionName, []),
    (`ModelDeltaTest.functionType, []),
    (`ModelDeltaTest.functionBody, []),
    (`ModelDeltaTest.functionValue, []),
    (`ModelDeltaTest.functionBase, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionEnv, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionWF, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionNoQuot, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionRegistered, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionLookup, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionTypeStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionBodyStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionConstStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionDeltaStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionDeltaSound, [`Quot.sound, `propext]),
    (`ModelDeltaTest.argumentD, [`Quot.sound, `propext]),
    (`ModelDeltaTest.argumentC, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionObservation, [`Quot.sound, `propext]),
    (`ModelDeltaTest.argumentTyped, [`Quot.sound, `propext]),
    (`ModelDeltaTest.duplicateBacked, [`propext]),
    (`ModelDeltaTest.functionBodyObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionHeadObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionHeadTyped, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionApplicationObserved, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionApplicationStrong, [`Quot.sound, `propext]),
    (`ModelDeltaTest.functionApplicationTyped, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice, `Lean4Lean.VEnv.Model.Covers.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-delta manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-delta manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-delta axiom {root}"
    if let some proof := info.value? then
      if proof.hasSorry then throwError "direct model-delta admission {root}"
    else
      match info with
      | .inductInfo _ | .ctorInfo _ => pure ()
      | _ => throwError "missing model-delta value {root}"
    let mut axioms : Array Name := #[]
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-delta dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration matches .axiomInfo _ then axioms := axioms.push name
        if declaration.type.hasSorry then throwError "admitted model-delta type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-delta admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
      else
        throwError "missing model-delta dependency {name} in {root}"
    unless pending.isEmpty do throwError "model-delta traversal exceeded bound"
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-delta axiom manifest changed for {root}: {repr axioms}"
    let required :=
      if root == `Lean4Lean.VEnv.RewriteMetadata.deltaRules then [`Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VEnv.RewriteMetadata.lookup, `Lean4Lean.VEnv.RewriteMetadata.unique, `Lean4Lean.VEnv.RewriteMetadata.quotientNames]
      else if root == `Lean4Lean.VEnv.WF.deltaRules then [`Lean4Lean.VEnv.WF.rewriteMetadata, `Lean4Lean.VEnv.RewriteMetadata.deltaRules]
      else if root == `Lean4Lean.VEnv.Model.RewriteMetadata.installedCtor then [`Lean4Lean.VEnv.RewriteMetadata.classify, `Lean4Lean.VDefEq.HasConstructorMajor.unique, `Lean4Lean.VEnv.Model.quotConstructorMajor]
      else if root == `Lean4Lean.VEnv.WF.installed_constructor_rigid then [`Lean4Lean.VEnv.WF.rewriteMetadata, `Lean4Lean.VEnv.RewriteMetadata.quotientNames, `Lean4Lean.VEnv.Model.RewriteMetadata.installedCtor]
      else if root == `Lean4Lean.VEnv.Model.RuleValid.delta then [`Lean4Lean.VEnv.DeltaRules.const, `Lean4Lean.VEnv.DeltaRules.excl, `Lean4Lean.VEnv.Model.Obs.delta, `Lean4Lean.VEnv.Model.Obs.const_typed, `Lean4Lean.VEnv.Model.Obs.closed_iff_id, `Lean4Lean.VEnv.Model.vcls_defeq, `Lean4Lean.VEnv.Model.vcls_closed, `Lean4Lean.VEnv.IsDefEq.extra, `Lean4Lean.VEnv.Model.wrapLams_mkApps_ne_const]
      else if root == `Lean4Lean.VEnv.Model.RuleValid.delta_of_wf then [`Lean4Lean.VEnv.Model.RuleValid.delta, `Lean4Lean.VEnv.WF.deltaRules, `Lean4Lean.VEnv.WF.installed_constructor_rigid, `Lean4Lean.VEnv.WF.ordered]
      else if root == `Lean4Lean.VEnv.Model.sound_no_quot then [`Lean4Lean.VEnv.Model.sound, `Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `Lean4Lean.VEnv.WF.rewriteMetadata, `Lean4Lean.VEnv.RewriteMetadata.classify]
      else if root == `ModelDeltaTest.history then [`ModelDeltaTest.firstHistory, `Lean4Lean.VDecl.WF.def, `Lean4Lean.VEnv.WF'.decl]
      else if root == `ModelDeltaTest.firstValid then [`Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `ModelDeltaTest.firstRegistered, `ModelDeltaTest.envWF]
      else if root == `ModelDeltaTest.aliasValid then [`Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `ModelDeltaTest.aliasRegistered, `ModelDeltaTest.envWF]
      else if root == `ModelDeltaTest.firstHeadUnique then [`Lean4Lean.VEnv.WF.deltaRules, `ModelDeltaTest.firstRegistered]
      else if root == `ModelDeltaTest.firstNotConstructor then [`Lean4Lean.VEnv.WF.installed_constructor_rigid, `ModelDeltaTest.firstNotRigid]
      else if root == `ModelDeltaTest.firstStrong then [`Lean4Lean.VEnv.IsDefEqStrong.extra, `ModelDeltaTest.firstConstStrong, `ModelDeltaTest.firstRegistered]
      else if root == `ModelDeltaTest.aliasStrong then [`Lean4Lean.VEnv.IsDefEqStrong.extra, `ModelDeltaTest.aliasConstStrong, `ModelDeltaTest.firstConstStrong, `ModelDeltaTest.aliasRegistered]
      else if root == `ModelDeltaTest.twoUnfoldings then [`Lean4Lean.VEnv.IsDefEqStrong.trans, `ModelDeltaTest.firstStrong, `ModelDeltaTest.aliasStrong]
      else if root == `ModelDeltaTest.bothSound then [`Lean4Lean.VEnv.Model.sound_no_quot, `ModelDeltaTest.noQuot, `ModelDeltaTest.twoUnfoldings, `ModelDeltaTest.history]
      else if root == `ModelDeltaTest.aliasObserved then [`ModelDeltaTest.bothSound, `Lean4Lean.VEnv.Model.Ob.Le.sort_inv]
      else if root == `ModelDeltaTest.forwardObserved then [`ModelDeltaTest.bothSound, `ModelDeltaTest.aliasObserved]
      else if root == `ModelDeltaTest.aliasObservationTyped then [`ModelDeltaTest.bothSound, `ModelDeltaTest.aliasObserved, `Lean4Lean.VEnv.Model.TypedAt]
      else if root == `ModelDeltaTest.underRelatedAnchors then [`ModelDeltaTest.bothSound, `ModelDeltaTest.relatedAnchors, `ModelDeltaTest.anchorTyped, `ModelDeltaTest.aliasObserved, `Lean4Lean.VEnv.Model.Obs.closed_iff_id]
      else if root == `ModelDeltaTest.mixedWF then [`Lean4Lean.VDecl.WF.quot, `Lean4Lean.VDecl.WF.axiom, `ModelDeltaTest.history, `ModelDeltaTest.equalityAdded]
      else if root == `ModelDeltaTest.mixedConstructor then [`ModelDeltaTest.mixedQuotRegistered, `Lean4Lean.VEnv.Model.quotConstructorMajor]
      else if root == `ModelDeltaTest.mixedConstructorRigid then [`Lean4Lean.VEnv.WF.installed_constructor_rigid, `ModelDeltaTest.mixedConstructor, `ModelDeltaTest.mixedWF]
      else if root == `ModelDeltaTest.mixedDeltaValid then [`Lean4Lean.VEnv.Model.RuleValid.delta_of_wf, `ModelDeltaTest.mixedWF, `ModelDeltaTest.mixedInclusion, `ModelDeltaTest.aliasRegistered]
      else if root == `ModelDeltaTest.mixedSound then [`Lean4Lean.VEnv.Model.sound_no_quot, `ModelDeltaTest.mixedWF, `ModelDeltaTest.envWF, `ModelDeltaTest.mixedInclusion, `ModelDeltaTest.noQuot, `ModelDeltaTest.twoUnfoldings]
      else if root == `ModelDeltaTest.mixedObserved then [`ModelDeltaTest.mixedSound, `Lean4Lean.VEnv.Model.Ob.Le.sort_inv]
      else if root == `ModelDeltaTest.mixedRejectsNoQuot then [`ModelDeltaTest.mixedQuotRegistered]
      else if root == `ModelDeltaTest.functionWF then [`Lean4Lean.VDecl.WF.def, `ModelDeltaTest.history]
      else if root == `ModelDeltaTest.functionDeltaStrong then [`Lean4Lean.VEnv.IsDefEqStrong.extra, `ModelDeltaTest.functionRegistered, `ModelDeltaTest.functionBodyStrong, `ModelDeltaTest.functionConstStrong]
      else if root == `ModelDeltaTest.functionDeltaSound then [`Lean4Lean.VEnv.Model.sound_no_quot, `ModelDeltaTest.functionWF, `ModelDeltaTest.functionNoQuot, `ModelDeltaTest.functionDeltaStrong]
      else if root == `ModelDeltaTest.functionBodyObserved then [`Lean4Lean.VEnv.Model.Obs.lam, `ModelDeltaTest.argumentTyped, `ModelDeltaTest.duplicateBacked]
      else if root == `ModelDeltaTest.functionHeadObserved then [`ModelDeltaTest.functionDeltaSound, `ModelDeltaTest.functionBodyObserved]
      else if root == `ModelDeltaTest.functionHeadTyped then [`ModelDeltaTest.functionDeltaSound, `ModelDeltaTest.functionHeadObserved, `Lean4Lean.VEnv.Model.TypedAt]
      else if root == `ModelDeltaTest.functionApplicationObserved then [`ModelDeltaTest.functionHeadObserved, `Lean4Lean.VEnv.Model.Ob.Le.app_inv, `Lean4Lean.VEnv.Model.Obs.app]
      else if root == `ModelDeltaTest.functionApplicationStrong then [`Lean4Lean.VEnv.IsDefEqStrong.appDF, `ModelDeltaTest.functionConstStrong]
      else if root == `ModelDeltaTest.functionApplicationTyped then [`Lean4Lean.VEnv.Model.sound_no_quot, `ModelDeltaTest.functionApplicationStrong, `ModelDeltaTest.functionApplicationObserved, `ModelDeltaTest.functionNoQuot]
      else []
    unless required.all visited.contains do
      throwError "model-delta proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelDeltaAudit
