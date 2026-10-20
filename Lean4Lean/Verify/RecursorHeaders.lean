import Lean4Lean.Theory.ConstructorHeaders
import Lean4Lean.Verify.InductiveRecursorApplicationTranslationCPS
import Lean4Lean.Verify.InductiveHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.Aligned.constants_eq_none from Lean4Lean.Verify.InductiveHeaders
open private Lean4Lean.AddInductive.stateBindWF
  Lean4Lean.AddInductive.stateExceptBindWF from Lean4Lean.Verify.RecursorRegistration
open private Lean4Lean.AddInductive.readWF from Lean4Lean.Verify.InductiveStats
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)

private theorem forIn'_refinesChecker {safety : DefinitionSafety} (base : VEnv)
    (items : List α) (models : α → VConstVal) (initial : Kernel.Environment)
    (state : Nat) (ctx : Context) (venv : VEnv)
    (step : (item : α) → item ∈ items → Kernel.Environment → StateT Nat M
      (ForInStep Kernel.Environment))
    (hle : base ≤ venv) (hchecker : CheckerEnv safety initial venv)
    (hstep : ∀ item hmem env state current, base ≤ current → CheckerEnv safety env current →
      (step item hmem env state ctx).WF fun result =>
        ∃ next extended, result.1 = .yield next ∧
          current.addConst (models item).name (models item).toVConstant = some extended ∧
          CheckerEnv safety next extended) :
    (forIn' items initial step state ctx).WF fun result =>
      ∃ extended, venv.addConstructorHeaders (items.map models) = some extended ∧
        CheckerEnv safety result.1 extended := by
  induction items generalizing initial state venv with
  | nil => exact .pure ⟨venv, rfl, hchecker⟩
  | cons item items ih =>
    rw [List.forIn'_cons]
    refine (hstep item (by simp) initial state venv hle hchecker).bind ?_
    rintro ⟨_, nextState⟩ ⟨next, current, rfl, added, nextChecker⟩
    refine (ih next nextState current
      (fun entry hmem env => step entry (by simp [hmem]) env)
      (hle.trans (VEnv.addConst_le added)) nextChecker
      (fun entry hmem env state current hle hchecker =>
        hstep entry (by simp [hmem]) env state current hle hchecker)).mono ?_
    rintro result ⟨extended, rest, finalChecker⟩
    exact ⟨extended, by simpa only [List.map_cons, VEnv.addConstructorHeaders, added]
      using rest, finalChecker⟩

/-- Replay the actual native name checks and recursor insertions in the model.
The supplied translations concern constant types; no reduction rule is added. -/
theorem declareRecursors.refinesChecker {safety : DefinitionSafety} {venv : VEnv}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (models : Nat → VConstVal)
    (hchecker : CheckerEnv safety ctx.env venv)
    (translations : ∀ index, index < types.size → ∀ rules,
      TrConstVal safety venv (.recInfo
        (metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules))
        (models index))
    (typesWF : ∀ index, index < types.size → (models index).toVConstant.WF venv) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF
      fun result => ∃ extended,
        venv.addConstructorHeaders ((List.range types.size).map models) = some extended ∧
          CheckerEnv safety result extended := by
  unfold declareRecursors
  dsimp only
  simp only [pure_bind, bind_pure]
  apply Except.WF.map
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_refinesChecker venv _ models _ _ _ venv _ .rfl hchecker
    intro index hindex env state current hle currentChecker
    have bound : index < types.size := by simpa using hindex
    apply Lean4Lean.AddInductive.stateBindWF
    intro rules nextState
    refine Lean4Lean.AddInductive.stateExceptBindWF (Lean4Lean.checkName.WF env
      (mkRecName types[index].name) ctx.allowPrimitive) ?_
    rintro _ ⟨fresh, _⟩
    let record := metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules
    have translated := (translations index bound rules).mono hle
    have recordFresh : env.constants.find? (ConstantInfo.recInfo record).name = none := by
      simpa only [record, metadataVal, ConstantInfo.name, ConstantInfo.toConstantVal,
        getElem!_pos, bound] using fresh
    have modelFresh : current.constants (models index).name = none :=
      translated.2 ▸ currentChecker.aligned.constants_eq_none recordFresh
    obtain ⟨extended, added⟩ :
        ∃ extended, current.addConst (models index).name (models index).toVConstant =
          some extended := by
      simp [VEnv.addConst, modelFresh]
    have nextChecker := currentChecker.addConst recordFresh translated.1 rfl
      ((typesWF index bound).mono hle) (translated.2.symm ▸ added)
    refine .pure ⟨_, extended, rfl, added, ?_⟩
    simpa only [record, metadataVal, getElem!_pos, bound] using nextChecker
  · rintro result ⟨extended, added, finalChecker⟩
    exact ⟨extended, by simpa only [List.range_eq_range'] using added, finalChecker⟩

/-- Construct all model constants from their closed type receipts, then insert them
using the native declaration's own successful name checks. -/
theorem declareRecursors.refinesChecker_of_typeReceipts
    {safety : DefinitionSafety} {venv : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (isK : Bool) (ctx : Context)
    (initial final : MLCtx) (hchecker : CheckerEnv safety ctx.env venv)
    (receipts : ∀ index, index < types.size →
      RecursorTypeModelReceipt venv universes stats infos index ctx initial final)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : initial.vlctx = []) :
    (declareRecursors stats types elimLevel infos lparams ctx.lctx isK false ctx).WF
      fun result => ∃ (models : Nat → VConstVal) (extended : VEnv),
        (∀ index, index < types.size → ∀ rules,
          TrConstVal .safe venv (.recInfo
            (metadataVal stats types elimLevel infos lparams ctx.lctx isK false index rules))
            (models index) ∧ (models index).toVConstant.WF venv) ∧
        venv.addConstructorHeaders ((List.range types.size).map models) = some extended ∧
        CheckerEnv safety result extended := by
  classical
  have perIndex : ∀ index : Nat, ∃ constant : VConstVal,
      ∀ (_bound : index < types.size) (rules : List RecursorRule),
        TrConstVal .safe venv (.recInfo
          (metadataVal stats types elimLevel infos lparams ctx.lctx isK false index rules))
          constant ∧ constant.toVConstant.WF venv := by
    intro index
    by_cases bound : index < types.size
    · obtain ⟨constant, translated, typed⟩ :=
        (receipts index bound).existsDeclaredRecursor lparams isK [] levels empty
      exact ⟨constant, fun _ _ => ⟨translated, typed⟩⟩
    · exact ⟨{ name := .anonymous, uvars := 0, type := .sort .zero },
        fun impossible _ => (bound impossible).elim⟩
  let models := fun index => Classical.choose (perIndex index)
  have properties := fun index => Classical.choose_spec (perIndex index)
  refine (declareRecursors.refinesChecker stats types elimLevel infos lparams ctx.lctx
    isK false ctx models hchecker
    (fun index bound rules =>
      ⟨(properties index bound rules).1.1.sf_mono DefinitionSafety.le_safe,
        (properties index bound rules).1.2⟩)
    (fun index bound => (properties index bound []).2)).mono ?_
  rintro result ⟨extended, added, finalChecker⟩
  exact ⟨models, extended, properties, added, finalChecker⟩

/-- The generated recursor scope now has an actual checker-model extension.
Selected-domain and pass support remain explicit; rule reduction is separate. -/
theorem mkRecInfos.registeredTranslatedAppliedChecker
    {safety : DefinitionSafety} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (reader : Context)
    (checker : CheckerEnv safety reader.env env)
    (constants : CanonicalAnnotationConstants env) (definitions : CanonicalAnnotationDefinitions env)
    (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : model.vlctx = []) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false reader).WF fun result =>
      ∃ (models : Nat → VConstVal) (extended : VEnv),
        (∀ index, index < types.size → ∀ rules,
          TrConstVal .safe env (.recInfo
            (declareRecursors.metadataVal stats types elimLevel result.2.1 lparams
              result.2.2.lctx isK false index rules)) (models index) ∧
            (models index).toVConstant.WF env) ∧
        env.addConstructorHeaders ((List.range types.size).map models) = some extended ∧
        CheckerEnv safety result.1 extended := by
  unfold mkRecInfos.scopeRegistration
  refine mkRecInfos.scopedTranslatedAppliedRecursorTypes stats types elimLevel _ reader _ checker.wf
    constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
    domainSupport ?_
  intro infos current finalModel frame _counts _endpoint receipts
  apply Lean4Lean.AddInductive.readWF
  have currentChecker : CheckerEnv safety current.env env := by
    simpa only [frame.env] using checker
  refine (declareRecursors.refinesChecker_of_typeReceipts stats types elimLevel infos
    lparams isK current model finalModel currentChecker receipts levels empty).bind ?_
  rintro result ⟨models, extended, properties, added, finalChecker⟩
  exact .pure ⟨models, extended, properties, added, finalChecker⟩

end Lean4Lean.AddInductive
