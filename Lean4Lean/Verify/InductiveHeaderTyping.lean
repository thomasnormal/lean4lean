import Lean4Lean.Verify.InductiveHeaderModels
import Lean4Lean.Verify.InductiveHeaders

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.readWF Lean4Lean.AddInductive.bindWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

theorem acceptedHeaderSortIsType (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {source result : Expr} {semantic : VExpr}
    (translated : checker.TrExprS source semantic)
    (accepted : (monadLift (TypeChecker.ensureSort source) : M Expr) reader = .ok result) :
    checker.IsType semantic := by
  have nativeAccepted : (Prod.fst <$> TypeChecker.ensureSort source source
      checker.toContext ({} : TypeChecker.VState).toState) = .ok result := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.ensureSort source source
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨normalized, final⟩ := returned
    change Except.ok normalized = .ok result at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, ⟨normalizedSemantic, normalizedTranslated, equality⟩, level, rfl⟩ :=
      TypeChecker.ensureSort.WF translated initialWF result final checked
    cases normalizedTranslated with
    | sort translatedLevel =>
      exact VEnv.IsType.defeqU_l checker.Ewf checker.Δwf.toCtx equality
        ⟨_, .sort (.of_ofLevel translatedLevel)⟩

theorem checkInductiveTypes.firstHeaderIsType (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker) (nonempty : 0 < types.size) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∃ semantic, checker.TrExprS types[0]!.type semantic ∧ checker.IsType semantic := by
  unfold checkInductiveTypes
  apply Lean4Lean.AddInductive.readWF
  rw [checkInductiveTypes.loopInd.eq_def]
  dsimp only
  split
  · rename_i bound
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro checkedUnit guarded
    cases checkedUnit
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro inferred checked
    apply Lean4Lean.AddInductive.readWF
    apply Lean4Lean.AddInductive.bindHeaderResultWF
    intro normalized normalizedCall
    have guarded : reader.env.checkNoMVarNoFVar types[0]!.name types[0]!.type = .ok () := by
      simpa only [getElem!_pos types 0 bound] using guarded
    have checked : (monadLift (TypeChecker.checkType types[0]!.type) : M Expr) reader = .ok inferred := by
      simpa only [getElem!_pos types 0 bound] using checked
    have normalizedCall : (monadLift (TypeChecker.whnf types[0]!.type) : M Expr) reader = .ok normalized := by
      simpa only [getElem!_pos types 0 bound] using normalizedCall
    have supported := checkNoMVarNoFVar.WF reader.env types[0]!.name types[0]!.type () guarded
    obtain ⟨sourceSemantic, sourceTranslated⟩ := acceptedSourceTranslation checker reader aligned initialWF
      (supported.mono fun _ impossible => impossible.elim) checked
    obtain ⟨normalizedSemantic, normalizedTranslated, equality⟩ :=
      acceptedHeaderNormalization checker reader aligned initialWF
        (sourceTranslated.trExpr checker.Ewf.ordered checker.Δwf) normalizedCall
    have finish (typed : checker.IsType normalizedSemantic) :
        ∃ semantic, checker.TrExprS types[0]!.type semantic ∧ checker.IsType semantic :=
      ⟨sourceSemantic, sourceTranslated, VEnv.IsType.defeqU_l checker.Ewf checker.Δwf.toCtx equality typed⟩
    by_cases binder : normalized.isForall = true
    · cases normalized <;> simp only [Expr.isForall, Bool.false_eq_true] at binder
      cases normalizedTranslated with
      | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
        exact fun _ _ => finish (domainTyped.forallE bodyTyped)
    · cases fuel : reader.fuel.inductiveFuel with
      | zero => exact Except.WF.throw
      | succ fuel =>
        rw [checkInductiveTypes.loopInd.loop.eq_def]
        dsimp only
        simp only [show (default : InductiveStats).indConsts.isEmpty = true from rfl, if_true]
        cases normalized <;> try exact False.elim (binder rfl)
        all_goals
          dsimp only
          split
          · exact Except.WF.throw
          · simp only [pure_bind]
            apply Lean4Lean.AddInductive.bindHeaderResultWF
            intro sorted sortedCall
            exact fun _ _ => finish
              (acceptedHeaderSortIsType checker reader aligned initialWF normalizedTranslated sortedCall)
  · rename_i empty
    exact False.elim (empty nonempty)

theorem checkInductiveTypes.firstHeaderWF (nparams : Nat) (types : Array InductiveType)
    (next : InductiveStats → M α) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (empty : checker.mlctx = .nil)
    (nonempty : 0 < types.size) :
    (checkInductiveTypes nparams types next reader).WF fun _ =>
      ∃ header, TrInductiveHeader checker.venv reader.lparams types[0]! header ∧
        header.toVConstant.WF checker.venv := by
  have initialWF := TypeChecker.VState.WF.reset checker (by
    simp [TypeChecker.VContext.vlctx, empty, TypeChecker.MLCtx.vlctx])
  refine (checkInductiveTypes.firstHeaderIsType nparams types next checker reader aligned initialWF nonempty).mono ?_
  rintro _ ⟨semantic, translated, typed⟩
  have universes : checker.lparams = reader.lparams := congrArg TypeChecker.Context.lparams aligned
  have context : checker.vlctx = [] := by simp only [TypeChecker.VContext.vlctx, empty, TypeChecker.MLCtx.vlctx]
  refine ⟨{ name := types[0]!.name, uvars := reader.lparams.length, type := semantic, ctors := [] },
    ⟨rfl, rfl, ?_⟩, ?_⟩
  · simpa only [TypeChecker.VContext.TrExprS, universes, context] using translated
  · simpa only [TypeChecker.VContext.IsType, VConstant.WF, universes, context, VLCtx.toCtx] using typed

theorem checkInductiveTypes.singleHeaderChecker (nparams : Nat) (type : InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (empty : checker.mlctx = .nil)
    (safety : checker.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams #[type]
      (fun stats => declareInductiveTypes stats nparams #[type] numNested isUnsafe) reader).WF
      fun result => ∃ header final,
        TrInductiveHeader checker.venv reader.lparams type header ∧
        header.toVConstant.WF checker.venv ∧
        checker.venv.addInductHeaders [header] = some final ∧
        CheckerEnv checker.safety result final := by
  intro result accepted
  obtain ⟨header, translated, typed⟩ := checkInductiveTypes.firstHeaderWF nparams #[type]
    (fun stats => declareInductiveTypes stats nparams #[type] numNested isUnsafe)
    checker reader aligned empty (by simp) result accepted
  have translated : TrInductiveHeader checker.venv reader.lparams type header := by
    simpa using translated
  have nativeEnv : checker.env = reader.env := congrArg TypeChecker.Context.env aligned
  have initialChecker : CheckerEnv checker.safety reader.env checker.venv := by
    rw [← nativeEnv]
    exact checker.trenv.checkerEnv
  have models : List.Forall₂ (TrInductiveHeader checker.venv reader.lparams)
      (#[type].toList) [header] := .cons translated .nil
  have typesWF : ∀ candidate ∈ [header], candidate.toVConstant.WF checker.venv := by
    intro candidate member
    simp only [List.mem_singleton] at member
    subst candidate
    exact typed
  obtain ⟨final, registered, finalChecker⟩ :=
    checkInductiveTypes.refinesHeadersChecker reader nparams #[type] numNested isUnsafe
      initialChecker safety models typesWF result accepted
  exact ⟨header, final, translated, typed, registered, finalChecker⟩

theorem run.firstHeaderWF (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader) (empty : checker.mlctx = .nil)
    (nonempty : 0 < types.length) :
    (run nparams types numNested reader).WF fun _ =>
      ∃ header, TrInductiveHeader checker.venv reader.lparams types.toArray[0]! header ∧
        header.toVConstant.WF checker.venv := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.firstHeaderWF nparams types.toArray _ checker reader aligned empty
    (by simpa only [List.size_toArray] using nonempty)

end Lean4Lean.AddInductive
