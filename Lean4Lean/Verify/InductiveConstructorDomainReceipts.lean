import Lean4Lean.Verify.InductiveConstructorDomainTrace

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem ParameterPrefix.selectedDomain
    {env : VEnv} {universes : List Name} {base source : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base source identifiers) (sourceWF : source.WF env universes)
    {index : Nat} {identifier : FVarId} (selected : identifiers[index]? = some identifier) :
    ∃ smaller nativeDomain semanticDomain insertion,
      ParameterPrefix base smaller (identifiers.take index) ∧ smaller.WF env universes ∧
      VLCtx.FVLift' smaller.vlctx source.vlctx 0 insertion 0 ∧
      TrExprS env universes smaller.vlctx nativeDomain semanticDomain ∧
      env.IsType universes.length smaller.vlctx.toCtx semanticDomain ∧
      ∃ declaration, source.lctx.find? identifier = some declaration ∧ declaration.type = nativeDomain := by
  induction parameters generalizing index identifier with
  | nil => simp at selected
  | @snoc previous identifiers nextIdentifier name nativeDomain semanticDomain binder parameters induction =>
    by_cases within : index < identifiers.length
    · have previousSelected : identifiers[index]? = some identifier := by
        simpa only [List.getElem?_append_left within] using selected
      obtain ⟨smaller, native, semantic, insertion, history, smallerWF, weakening, translated, typed,
        declaration, lookup, domain⟩ := induction sourceWF.1 previousSelected
      have different : identifier ≠ nextIdentifier := by
        intro same
        subst identifier
        have absent := sourceWF.2.1
        rw [lookup] at absent
        cases absent
      refine ⟨smaller, native, semantic, .skip insertion, ?_, smallerWF,
        weakening.skip_fvar _ _, translated, typed, declaration, ?_, domain⟩
      · simpa only [List.take_append_of_le_length (Nat.le_of_lt within)] using history
      · rw [sourceWF.find?_eq]
        simp only [MLCtx.decls, List.find?_cons, LocalDecl.fvarId,
          beq_eq_false_iff_ne.mpr different]
        exact sourceWF.1.find?_eq.symm.trans lookup
    · have atEnd : index = identifiers.length := by
        have bound := List.getElem?_eq_some_iff.mp selected |>.1
        simp only [List.length_append, List.length_singleton] at bound
        omega
      subst index
      have same : nextIdentifier = identifier := by simpa using selected
      subst identifier
      refine ⟨previous, nativeDomain, semanticDomain, .skip .refl, ?_, sourceWF.1,
        VLCtx.FVLift'.skip_fvar _ _ .refl, sourceWF.2.2.1, sourceWF.2.2.2,
        .cdecl previous.length nextIdentifier name nativeDomain binder .default, ?_, rfl⟩
      · simpa using parameters
      · rw [sourceWF.find?_eq]
        simp [MLCtx.decls, LocalDecl.fvarId]

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix)

theorem getType_fvar_eq_inferFVar (reader : Context) (identifier : FVarId)
    (declaration : LocalDecl) (lookup : reader.lctx.find? identifier = some declaration) :
    getType (.fvar identifier) reader =
      TypeChecker.Inner.inferFVar
        { env := reader.env, lctx := reader.lctx, safety := reader.safety,
          lparams := reader.lparams, fuel := reader.fuel } identifier := by
  change Except.ok (reader.lctx.get! identifier |>.type) = _
  simp [TypeChecker.Inner.inferFVar, LocalContext.get!, lookup]
  rfl

theorem acceptedSourceTranslation
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {type result : Expr} (supported : type.FVarsIn (· ∈ checker.vlctx.fvars))
    (accepted : (monadLift (TypeChecker.checkType type) : M Expr) reader = .ok result) :
    ∃ semantic, checker.TrExprS type semantic := by
  have nativeAccepted : (Prod.fst <$> TypeChecker.checkType type
      checker.toContext ({} : TypeChecker.VState).toState) = .ok result := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.checkType type
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨inferred, final⟩ := returned
    change Except.ok inferred = .ok result at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, semantic, _, _, translated, _, _⟩ :=
      TypeChecker.checkType.WF supported initialWF result final checked
    exact ⟨semantic, translated⟩

theorem ReducedParameterDomainReceipt.ofCheckedForall
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {base : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base checker.mlctx identifiers)
    {index : Nat} {identifier : FVarId} (selected : identifiers[index]? = some identifier)
    {name : Name} {domain body stored result : Expr} {binder : BinderInfo}
    (storedType : getType (.fvar identifier) reader = .ok stored)
    (supported : (Expr.forallE name domain body binder).FVarsIn (· ∈ checker.vlctx.fvars))
    (domainSupported : domain.FVarsIn (· ∈ (identifiers.take index).reverse ++ base.vlctx.fvars))
    (accepted : (monadLift (TypeChecker.checkType (.forallE name domain body binder)) : M Expr)
      reader = .ok result) :
    ∃ smaller storedSemantic candidateSemantic,
      ParameterPrefix base smaller (identifiers.take index) ∧
      ReducedParameterDomainReceipt checker.venv checker.lparams reader domain stored
        smaller.vlctx.toCtx storedSemantic candidateSemantic := by
  obtain ⟨smaller, nativeDomain, storedSemantic, insertion, history, smallerWF, weakening,
    storedTranslated, storedTyped, declaration, lookup, storedDomain⟩ :=
    parameters.selectedDomain checker.mlctx_wf selected
  have modelLocal : checker.mlctx.lctx = reader.lctx :=
    checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
  have readerLookup : reader.lctx.find? identifier = some declaration := by
    rw [← modelLocal]
    exact lookup
  have inferredType :
      TypeChecker.Inner.inferFVar
          { env := reader.env, lctx := reader.lctx, safety := reader.safety,
            lparams := reader.lparams, fuel := reader.fuel } identifier = .ok stored := by
    rw [← getType_fvar_eq_inferFVar reader identifier declaration readerLookup]
    exact storedType
  have inferredDomain :
      TypeChecker.Inner.inferFVar
          { env := reader.env, lctx := reader.lctx, safety := reader.safety,
            lparams := reader.lparams, fuel := reader.fuel } identifier =
        .ok declaration.type := by
    simp [TypeChecker.Inner.inferFVar, readerLookup]
    rfl
  have sameDomain : nativeDomain = stored := by
    rw [← storedDomain]
    exact Except.ok.inj (inferredDomain.symm.trans inferredType)
  subst stored
  obtain ⟨semantic, translated⟩ := acceptedSourceTranslation checker reader aligned initialWF supported accepted
  let .forallE _ _ candidateTranslated _ := translated
  have candidateClosed : Closed domain 0 := checker.mlctx.noBV ▸ candidateTranslated.closed
  have candidateSupported : domain.FVarsIn (· ∈ smaller.vlctx.fvars) := by
    simpa only [history.fvars] using domainSupported
  obtain ⟨candidateSemantic, candidateTranslated⟩ :=
    candidateTranslated.weakFV'_inv checker.Ewf weakening (.refl checker.Ewf checker.Δwf)
      candidateClosed candidateSupported
  obtain ⟨level, storedTyped⟩ := storedTyped
  exact ⟨smaller, storedSemantic, candidateSemantic, history, checker, smaller.vlctx, insertion, level,
    aligned, rfl, rfl, rfl, weakening, storedTranslated, candidateTranslated, storedTyped, initialWF⟩

theorem AcceptedConstructorTrace.firstDomainAgreement
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {base : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base checker.mlctx identifiers)
    {stats : InductiveStats} (statsParams : stats.params = (identifiers.map Expr.fvar).toArray)
    {identifier : FVarId} (first : identifiers[0]? = some identifier)
    {constructor name : Name} {domain body result terminal : Expr} {binder : BinderInfo}
    (sourceGuard : reader.env.checkNoMVarNoFVar constructor (.forallE name domain body binder) = .ok ())
    (sourceChecked : (monadLift (TypeChecker.checkType (.forallE name domain body binder)) : M Expr)
      reader = .ok result)
    {isUnsafe : Bool} {parent finalIndex : Nat} {finalReader : Context}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader 0
      (.forallE name domain body binder) finalReader finalIndex terminal) :
    ∃ stored storedSemantic candidateSemantic,
      getType (.fvar identifier) reader = .ok stored ∧
      (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true ∧
      ReducedParameterDomainReceipt checker.venv checker.lparams reader domain stored
        base.vlctx.toCtx storedSemantic candidateSemantic ∧
      ∃ level, checker.venv.IsDefEq checker.lparams.length base.vlctx.toCtx
        storedSemantic candidateSemantic (.sort level) := by
  have selected : stats.params[0]? = some (.fvar identifier) := by
    simp only [statsParams, List.getElem?_toArray, List.getElem?_map, first, Option.map_some]
  have sourceFree := checkNoMVarNoFVar.WF reader.env constructor (.forallE name domain body binder) () sourceGuard
  cases trace with
  | terminal notForall => cases notForall
  | parameter selectedTrace storedType accepted tail =>
    have same := Option.some.inj (selectedTrace.symm.trans selected)
    subst_vars
    obtain ⟨smaller, storedSemantic, candidateSemantic, history, receipt⟩ :=
      ReducedParameterDomainReceipt.ofCheckedForall checker reader aligned initialWF parameters first
        storedType (sourceFree.mono fun _ impossible => impossible.elim)
        (sourceFree.1.mono fun _ impossible => impossible.elim) sourceChecked
    have sameContext : smaller = base := by simpa using history.drop
    subst smaller
    exact ⟨_, storedSemantic, candidateSemantic, storedType, accepted, receipt, receipt.accepted accepted⟩
  | field notParameter => simp only [selected] at notParameter; cases notParameter

theorem checkConstructors.firstDomainAgreement
    (types : Array InductiveType) (stats : InductiveStats) (isUnsafe : Bool)
    (checker : TypeChecker.VContext) (reader : Context)
    (aligned : checker.toContext =
      { env := reader.env, lctx := reader.lctx, safety := reader.safety,
        lparams := reader.lparams, fuel := reader.fuel })
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {base : MLCtx} {identifiers : List FVarId}
    (parameters : ParameterPrefix base checker.mlctx identifiers)
    (statsParams : stats.params = (identifiers.map Expr.fvar).toArray)
    {identifier : FVarId} (first : identifiers[0]? = some identifier) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ name domain body binder, constructor.type = .forallE name domain body binder ∧
          ∃ stored storedSemantic candidateSemantic,
            getType (.fvar identifier) reader = .ok stored ∧
            (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true ∧
            ReducedParameterDomainReceipt checker.venv checker.lparams reader domain stored
              base.vlctx.toCtx storedSemantic candidateSemantic ∧
            ∃ level, checker.venv.IsDefEq checker.lparams.length base.vlctx.toCtx
              storedSemantic candidateSemantic (.sort level) := by
  have parameterFVars : stats.ParamsAreFVars := by
    intro parameter member
    simp only [statsParams, List.mem_toArray, List.mem_map] at member
    obtain ⟨identifier, _, rfl⟩ := member
    rfl
  have distinct : stats.params.toList.Nodup := by
    simp only [statsParams, List.toList_toArray]
    exact List.pairwise_map.mpr ((parameters.nodup checker.mlctx_wf).imp
      fun different same => different (Expr.fvar.inj same))
  have positive : 0 < stats.params.size := by
    have bound := List.getElem?_eq_some_iff.mp first |>.1
    simpa only [statsParams, List.size_toArray, List.length_map] using bound
  intro returned accepted parent bound constructor member
  have traces := checkConstructors.acceptedTraces types stats isUnsafe reader returned accepted
  have arity := checkConstructors.arity types stats isUnsafe reader parameterFVars distinct
    returned accepted types[parent] (Array.getElem_mem bound) constructor member
  have shape : ∃ name domain body binder, constructor.type = .forallE name domain body binder := by
    cases shape : constructor.type with
    | forallE name domain body binder => exact ⟨name, domain, body, binder, rfl⟩
    | _ => simp only [shape, declareConstructors.arity] at arity; omega
  obtain ⟨name, domain, body, binder, shape⟩ := shape
  obtain ⟨result, finalReader, finalIndex, terminal, sourceGuard, sourceChecked, trace⟩ :=
    traces parent bound constructor member
  rw [shape] at sourceGuard sourceChecked trace
  exact ⟨name, domain, body, binder, shape,
    trace.firstDomainAgreement checker reader aligned initialWF parameters statsParams first sourceGuard sourceChecked⟩

end Lean4Lean.AddInductive
