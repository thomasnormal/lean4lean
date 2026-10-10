import Lean4Lean.Verify.InductiveConstructorDomainReceipts

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem ParameterPrefix.baseWF
    (parameters : ParameterPrefix base source identifiers) (sourceWF : source.WF env universes) :
    base.WF env universes := by
  induction parameters with
  | nil => exact sourceWF
  | snoc _ induction => exact induction sourceWF.1

theorem ParameterPrefix.uncons
    (parameters : ParameterPrefix base source identifiers)
    (shape : identifiers = identifier :: remaining) :
    ∃ name nativeDomain semanticDomain binder,
      ParameterPrefix (.vlam identifier name nativeDomain semanticDomain binder base) source remaining := by
  induction parameters generalizing identifier remaining with
  | nil => cases shape
  | @snoc previous identifiers last name nativeDomain semanticDomain binder parameters induction =>
    cases identifiers with
    | nil =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      have same : previous = base := by simpa using parameters.drop
      subst previous
      exact ⟨name, nativeDomain, semanticDomain, binder, .nil⟩
    | cons first rest =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj shape
      obtain ⟨firstName, firstNative, firstSemantic, firstBinder, tail⟩ := induction rfl
      exact ⟨firstName, firstNative, firstSemantic, firstBinder, .snoc tail⟩

theorem ParameterPrefix.retainsLookup
    (parameters : ParameterPrefix base source identifiers) (sourceWF : source.WF env universes)
    (lookup : base.lctx.find? identifier = some declaration) :
    source.lctx.find? identifier = some declaration := by
  induction parameters with
  | nil => exact lookup
  | @snoc previous identifiers nextIdentifier name nativeDomain semanticDomain binder parameters induction =>
    have previousLookup := induction sourceWF.1
    have different : identifier ≠ nextIdentifier := by
      intro same
      subst identifier
      have absent := sourceWF.2.1
      rw [previousLookup] at absent
      cases absent
    rw [sourceWF.find?_eq]
    simp only [MLCtx.decls, List.find?_cons, LocalDecl.fvarId, beq_eq_false_iff_ne.mpr different]
    exact sourceWF.1.find?_eq.symm.trans previousLookup

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix)
open private selectedParameterBound absentParameterBound from Lean4Lean.Verify.InductiveConstructorDomainTrace

theorem AcceptedConstructorTrace.receiptsAfterParameters
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    {trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal}
    (complete : stats.params.size ≤ index) (env : VEnv) (universes : List Name)
    (source target : List VExpr) :
    CheckedConstructorDomainReceipts env universes trace source target source target := by
  induction trace with
  | terminal notForall valid => exact .terminal notForall valid
  | parameter selected => have bound := selectedParameterBound selected; omega
  | field notParameter domainChecked universeAccepted positive tail induction =>
    exact .field notParameter domainChecked universeAccepted positive (induction (by omega))

theorem TrExprS.openCanonicalParameter
    {env : VEnv} {universes : List Name} {current : MLCtx}
    {identifier : FVarId} {name : Name} {stored : Expr} {storedSemantic : VExpr} {binder : BinderInfo}
    (envWF : env.WF)
    (nextWF : (MLCtx.vlam identifier name stored storedSemantic binder current).WF env universes)
    {body : Expr} {candidateSemantic bodySemantic : VExpr}
    (translated : TrExprS env universes ((none, .vlam candidateSemantic) :: current.vlctx) body bodySemantic)
    {level : VLevel}
    (equal : env.IsDefEq universes.length current.vlctx.toCtx storedSemantic candidateSemantic (.sort level)) :
    ∃ openedSemantic, TrExprS env universes
      (MLCtx.vlam identifier name stored storedSemantic binder current).vlctx
      (body.instantiate1 (.fvar identifier)) openedSemantic := by
  have contexts : VLCtx.IsDefEq env universes.length
      ((none, .vlam candidateSemantic) :: current.vlctx) ((none, .vlam storedSemantic) :: current.vlctx) :=
    .cons (.refl envWF.ordered nextWF.1.tr.wf) nofun (.vlam equal.symm)
  obtain ⟨openedSemantic, translated⟩ := translated.defeqDFC envWF contexts
  refine ⟨openedSemantic, ?_⟩
  simpa only [Expr.instantiate1_eq] using (translated.inst_fvar envWF.ordered nextWF.tr.wf)

private theorem AcceptedConstructorTrace.prefixReceipts
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (remaining : List FVarId) {stats : InductiveStats} {isUnsafe : Bool} {parent : Nat}
    {current : MLCtx} (parameters : ParameterPrefix current checker.mlctx remaining)
    (processed : List FVarId)
    (statsParams : stats.params = ((processed ++ remaining).map Expr.fvar).toArray)
    {type terminal : Expr} {semanticType : VExpr} {finalReader : Context} {finalIndex : Nat}
    (translated : TrExprS checker.venv checker.lparams current.vlctx type semanticType)
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader processed.length type finalReader finalIndex terminal)
    (target : List VExpr) :
    ∃ completed finalTarget unprocessed,
      CheckedConstructorDomainReceipts checker.venv checker.lparams trace
        current.vlctx.toCtx target completed.vlctx.toCtx finalTarget ∧
      ParameterPrefix completed checker.mlctx unprocessed ∧
      unprocessed.length = stats.params.size - min finalIndex stats.params.size := by
  induction remaining generalizing current processed type semanticType target with
  | nil =>
    have complete : stats.params.size ≤ processed.length := by simp [statsParams]
    refine ⟨current, target, [], trace.receiptsAfterParameters complete checker.venv checker.lparams _ _,
      parameters, ?_⟩
    have monotone := trace.index_le
    simp only [List.length_nil]
    omega
  | cons identifier remaining induction =>
    have selected : stats.params[processed.length]? = some (.fvar identifier) := by
      simp only [statsParams, List.getElem?_toArray, List.getElem?_map,
        List.getElem?_append_right (Nat.le_refl processed.length), Nat.sub_self,
        List.getElem?_cons_zero, Option.map_some]
    cases trace with
    | terminal notForall valid =>
      refine ⟨current, target, identifier :: remaining, .terminal notForall valid, parameters, ?_⟩
      have size : stats.params.size = processed.length + (identifier :: remaining).length := by simp [statsParams]
      omega
    | field notParameter => rw [selected] at notParameter; cases notParameter
    | @parameter index parameter reader stored domain body finalReader finalIndex terminal name binder
        selectedTrace storedType accepted tail =>
      have same := Option.some.inj (selectedTrace.symm.trans selected)
      subst parameter
      obtain ⟨parameterName, nativeDomain, storedSemantic, parameterBinder, remainingParameters⟩ :=
        parameters.uncons rfl
      let next := MLCtx.vlam identifier parameterName nativeDomain storedSemantic parameterBinder current
      have nextWF : next.WF checker.venv checker.lparams := remainingParameters.baseWF checker.mlctx_wf
      have nextLookup : next.lctx.find? identifier = some
          (.cdecl current.length identifier parameterName nativeDomain parameterBinder .default) := by
        rw [nextWF.find?_eq]
        simp [next, MLCtx.decls, LocalDecl.fvarId]
      have lookup := remainingParameters.retainsLookup checker.mlctx_wf nextLookup
      have modelLocal : checker.mlctx.lctx = reader.lctx :=
        checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
      have sameDomain : nativeDomain = stored := by
        apply Except.ok.inj
        change Except.ok (reader.lctx.get! identifier).type = .ok stored at storedType
        simpa only [← modelLocal, LocalContext.get!, lookup, Option.getD_some, LocalDecl.type] using storedType
      subst stored
      let .forallE _ _ candidateTranslated bodyTranslated := translated
      obtain ⟨level, storedTyped⟩ := nextWF.2.2.2
      have receipt : ReducedParameterDomainReceipt checker.venv checker.lparams reader domain nativeDomain
          current.vlctx.toCtx storedSemantic _ :=
        ⟨checker, current.vlctx, .skipN .refl (identifier :: remaining).length, level,
          aligned, rfl, rfl, rfl, parameters.insertion, nextWF.2.2.1, candidateTranslated, storedTyped, initialWF⟩
      obtain ⟨equalLevel, equal⟩ := receipt.accepted accepted
      obtain ⟨openedSemantic, opened⟩ := TrExprS.openCanonicalParameter checker.Ewf nextWF bodyTranslated equal
      have nextStats : stats.params = (((processed ++ [identifier]) ++ remaining).map Expr.fvar).toArray := by
        simpa only [List.append_assoc, List.singleton_append] using statsParams
      have nextTrace : AcceptedConstructorTrace stats isUnsafe parent reader (processed ++ [identifier]).length
          (body.instantiate1 (.fvar identifier)) finalReader finalIndex terminal := by
        simpa only [List.length_append, List.length_singleton] using tail
      obtain ⟨completed, finalTarget, unprocessed, receipts, suffix, length⟩ := induction remainingParameters (processed ++ [identifier])
        nextStats opened nextTrace (_ :: target)
      refine ⟨completed, finalTarget, unprocessed, ?_, suffix, length⟩
      exact .parameter (trace := tail) selectedTrace storedType accepted receipt
        (by simpa only [List.length_append, List.length_singleton] using receipts)

theorem AcceptedConstructorTrace.completeParameters
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    (parameterFVars : stats.ParamsAreFVars) (distinct : stats.params.toList.Nodup)
    (absent : stats.RemainingParamsAbsent index type) : stats.params.size ≤ finalIndex := by
  induction trace with
  | terminal notForall valid => exact absent.validIndAppIdx parameterFVars valid
  | @parameter index parameter reader stored domain body finalReader finalIndex terminal name binder
      selected storedType accepted tail induction =>
    have bound := selectedParameterBound selected
    have same : stats.params[index] = parameter := by
      simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq] using selected
    have nextAbsent := absent.consume_param parameterFVars distinct bound
    rw [same] at nextAbsent
    exact induction nextAbsent
  | field notParameter _ _ _ tail _ =>
    have bound := absentParameterBound notParameter
    have monotone := tail.index_le
    omega

theorem AcceptedConstructorTrace.domainReceipts
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {base : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base checker.mlctx identifiers)
    {stats : InductiveStats} (statsParams : stats.params = (identifiers.map Expr.fvar).toArray)
    {type result terminal : Expr}
    (sourceFree : type.FVarsIn (fun _ => False))
    (sourceChecked : (monadLift (TypeChecker.checkType type) : M Expr) reader = .ok result)
    {isUnsafe : Bool} {parent finalIndex : Nat} {finalReader : Context}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader 0 type finalReader finalIndex terminal) :
    ∃ finalTarget,
      CheckedConstructorDomainReceipts checker.venv checker.lparams trace
        base.vlctx.toCtx base.vlctx.toCtx checker.vlctx.toCtx finalTarget ∧
      checker.venv.IsDefEqCtx checker.lparams.length base.vlctx.toCtx checker.vlctx.toCtx finalTarget ∧
      finalTarget.length = base.vlctx.toCtx.length + stats.params.size := by
  obtain ⟨semantic, ambient⟩ := acceptedSourceTranslation checker reader aligned initialWF
    (sourceFree.mono fun _ impossible => impossible.elim) sourceChecked
  obtain ⟨semantic, translated⟩ := ambient.weakFV'_inv checker.Ewf parameters.insertion
    (.refl checker.Ewf.ordered checker.Δwf) (checker.mlctx.noBV ▸ ambient.closed)
    (sourceFree.mono fun _ impossible => impossible.elim)
  obtain ⟨completed, finalTarget, unprocessed, receipts, suffix, length⟩ :=
    trace.prefixReceipts checker reader aligned initialWF identifiers parameters [] statsParams
      translated base.vlctx.toCtx
  have parameterFVars : stats.ParamsAreFVars := by
    intro parameter member
    simp only [statsParams, List.mem_toArray, List.mem_map] at member
    obtain ⟨identifier, _, rfl⟩ := member
    rfl
  have distinct : stats.params.toList.Nodup := by
    simp only [statsParams, List.toList_toArray]
    exact List.pairwise_map.mpr ((parameters.nodup checker.mlctx_wf).imp
      fun different same => different (Expr.fvar.inj same))
  have complete := trace.completeParameters parameterFVars distinct
    (InductiveStats.RemainingParamsAbsent.of_noFVars sourceFree 0)
  have empty : unprocessed = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst unprocessed
  have sameContext : completed = checker.mlctx := by simpa using suffix.drop.symm
  subst completed
  have growth := receipts.completeGrowth complete
  exact ⟨finalTarget, receipts, receipts.agreement .zero, by simpa using growth.2⟩

theorem checkConstructors.domainReceipts
    (types : Array InductiveType) (stats : InductiveStats) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {base : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base checker.mlctx identifiers)
    (statsParams : stats.params = (identifiers.map Expr.fvar).toArray) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ finalReader finalIndex terminal finalTarget,
          ∃ trace : AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type
            finalReader finalIndex terminal,
          CheckedConstructorDomainReceipts checker.venv checker.lparams trace
            base.vlctx.toCtx base.vlctx.toCtx checker.vlctx.toCtx finalTarget ∧
          checker.venv.IsDefEqCtx checker.lparams.length base.vlctx.toCtx checker.vlctx.toCtx finalTarget ∧
          finalTarget.length = base.vlctx.toCtx.length + stats.params.size := by
  refine (checkConstructors.acceptedTraces types stats isUnsafe reader).mono ?_
  intro _ traces parent bound constructor member
  obtain ⟨result, finalReader, finalIndex, terminal, sourceGuard, sourceChecked, trace⟩ :=
    traces parent bound constructor member
  have sourceFree := checkNoMVarNoFVar.WF reader.env constructor.name constructor.type () sourceGuard
  obtain ⟨finalTarget, receipts, agreement, length⟩ := trace.domainReceipts checker reader aligned initialWF
    parameters statsParams sourceFree sourceChecked
  exact ⟨finalReader, finalIndex, terminal, finalTarget, trace, receipts, agreement, length⟩

end Lean4Lean.AddInductive
