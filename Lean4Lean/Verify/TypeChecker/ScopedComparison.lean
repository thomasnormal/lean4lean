import Lean4Lean.Verify.TypeChecker.ScopedInferType
import Lean4Lean.Verify.TypeChecker.IsDefEq

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception

private theorem translateUnusedBinder {context : VContext} {state : VState}
    {locals : MLCtx} [localsWF : context.MLCWF locals]
    {body : Expr} {variables : List Expr} {domainSemantic bodySemantic : VExpr}
    (wellFormed : state.WF (context.withMLC locals))
    (domainType : (context.withMLC locals).IsType domainSemantic)
    (closedBody : body.looseBVarRange' = 0)
    (bodyTranslation : TrExprS context.venv context.lparams
      ((none, .vlam domainSemantic) :: locals.vlctx) (body.instantiateList variables 1) bodySemantic) :
    ∃ result, (context.withMLC locals).TrExprS (body.instantiateList (default :: variables)) result ∧
      context.venv.IsDefEqU context.lparams.length (domainSemantic :: locals.vlctx.toCtx)
        bodySemantic result.lift := by
  simp
  rw [← Expr.instantiateList_instantiate1_comm (by rfl)]
  let identifier : FVarId := ⟨state.ngen.curr⟩
  have extendedContext : VLCtx.WF context.venv context.lparams.length
      ((some (identifier, []), .vlam domainSemantic) :: locals.vlctx) := by
    refine ⟨localsWF.1.tr.wf, ?_, domainType⟩
    rintro _ _ ⟨⟩
    simp
    exact fun member => state.ngen.not_reserves_self (wellFormed.ngen_wf _ member)
  have instantiated := bodyTranslation.inst_fvar context.Ewf.ordered extendedContext
  have unused {replacement : Expr}
      (bodyClosed : body.looseBVarRange' = 0) (replacementClosed : replacement.looseBVarRange' = 0) :
      (body.instantiateList variables 1).instantiate1' replacement = body.instantiateList variables 1 := by
    rw [Expr.instantiate1'_eq_self]
    rw [Expr.instantiateList'_eq_self] <;> simp [*]
  rw [unused closedBody rfl, ← unused (replacement := .fvar identifier) closedBody rfl]
  obtain ⟨_, restored⟩ := instantiated.weakFV_inv context.Ewf (.skip_fvar _ _ .refl)
    (.refl context.Ewf extendedContext) (locals.noBV ▸ instantiated.closed)
    (by rw [unused closedBody rfl]; exact bodyTranslation.fvarsIn)
  exact ⟨_, restored, instantiated.uniq context.Ewf (.refl context.Ewf extendedContext)
    (restored.weakFV context.Ewf (.skip_fvar _ _ .refl) extendedContext)⟩

theorem isDefEqLambda.scopeWF {context : VContext} {state : VState}
    {locals : MLCtx} [localsWF : context.MLCWF locals]
    {first second : Expr} {firstSemantic secondSemantic : VExpr} {substitution : Array Expr}
    {variables : List Expr} (substitutions : substitution.toList.reverse = variables)
    (closedVariables : ∀ value ∈ variables, value.looseBVarRange' = 0)
    (firstTranslation : (context.withMLC locals).TrExprS (first.instantiateList variables) firstSemantic)
    (secondTranslation : (context.withMLC locals).TrExprS (second.instantiateList variables) secondSemantic) :
    (isDefEqLambda first second substitution).ScopeWF (context.withMLC locals) state
      (fun equal _ => equal → (context.withMLC locals).IsDefEqU firstSemantic secondSemantic) := by
  unfold isDefEqLambda
  let localContext := context.withMLC locals
  have instantiateMany (expression : Expr) (depth : Nat) :=
    Expr.instantiateMany_eq_instantiateList expression variables depth closedVariables
  split <;> [rename_i firstName firstDomain firstBody firstBinder secondName secondDomain secondBody secondBinder;
    (simp [substitutions, instantiateMany]; exact isDefEq.scopeWF firstTranslation secondTranslation)]
  extract_lets bodyWorker firstInstantiatedDomain secondInstantiatedDomain domainWorker
  unfold domainWorker firstInstantiatedDomain secondInstantiatedDomain
  simp at firstTranslation secondTranslation
  let .lam (ty' := firstDomainSemantic) (body' := firstBodySemantic)
    ⟨_, firstDomainTyping⟩ firstDomainTranslation firstBodyTranslation := firstTranslation
  let .lam (ty' := secondDomainSemantic) (body' := secondBodySemantic)
    secondDomainType secondDomainTranslation secondBodyTranslation := secondTranslation
  suffices ∀ {selectedDomain currentState}
      (_ : match selectedDomain with
        | none => firstDomain == secondDomain
        | some domain => domain = secondDomain.instantiateList variables),
      localContext.IsDefEqU firstDomainSemantic secondDomainSemantic →
      (bodyWorker selectedDomain).ScopeWF localContext currentState
        (fun equal _ => equal → localContext.IsDefEqU
          (firstDomainSemantic.lam firstBodySemantic) (secondDomainSemantic.lam secondBodySemantic)) by
    split <;> rename_i domainMatch
    · refine RecM.ScopeWF.pureBind <| this ‹_› ?_
      exact (firstDomainTranslation.eqv (Expr.instantiateList_eqv domainMatch)).uniq
        localContext.Ewf (.refl localContext.Ewf localContext.Δwf) secondDomainTranslation
    simp [substitutions, instantiateMany]
    refine (isDefEq.scopeWF firstDomainTranslation secondDomainTranslation).bind
      fun equal _ _ domainsEqual => ?_
    split <;> [exact RecM.ScopeWF.pure nofun; rename_i accepted]
    simp at accepted
    exact this rfl (domainsEqual accepted)
  intro selectedDomain currentState selected domainEquality
  have typedDomainEquality := domainEquality.of_l localContext.Ewf localContext.Δwf firstDomainTyping
  have ⟨_, alignedFirstBody, bodyEquality⟩ := firstBodyTranslation.defeqDFC' localContext.Ewf <|
    .cons (.refl localContext.Ewf localContext.Δwf) (by nofun) (.vlam typedDomainEquality)
  unfold bodyWorker
  split <;> rename_i bodiesDependent
  · extract_lets selectedType
    have selectedTypeEq : selectedType = secondDomain.instantiateList variables := by
      split at selected <;> [simp [selectedType, substitutions, instantiateMany]; exact selected]
    clear_value selectedType
    subst selectedTypeEq
    refine RecM.ScopeWF.stateWF fun wellFormed => ?_
    let identifier : FVarId := ⟨currentState.ngen.curr⟩
    let extended := locals.vlam identifier secondName (secondDomain.instantiateList variables)
      secondDomainSemantic secondBinder
    have extendedWF : context.MLCWF extended :=
      ⟨localsWF.1, wellFormed.find?_eq_none currentState.ngen.not_reserves_self,
        secondDomainTranslation, secondDomainType⟩
    letI : context.MLCWF extended := extendedWF
    refine RecM.ScopeWF.withLocalDecl (cwf' := extendedWF) secondDomainTranslation secondDomainType ?_
    have secondInstantiatedBody := secondBodyTranslation.inst_fvar context.Ewf extendedWF.1.tr.wf
    have firstInstantiatedBody := alignedFirstBody.inst_fvar context.Ewf extendedWF.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList]
      at firstInstantiatedBody secondInstantiatedBody
    refine (isDefEqLambda.scopeWF (localsWF := extendedWF) (variables := .fvar identifier :: variables)
      (by simp [substitutions, identifier])
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨rfl, closedVariables⟩)
      firstInstantiatedBody secondInstantiatedBody).mono fun _ _ _ compared accepted => ?_
    have ⟨_, bodyConversion⟩ := bodyEquality.symm.trans localContext.Ewf extendedWF.1.tr.wf.toCtx
      (compared accepted)
    exact ⟨_, .symm <| .lamDF typedDomainEquality.symm bodyConversion.symm⟩
  · simp [Expr.hasLooseBVars] at bodiesDependent
    refine RecM.ScopeWF.stateWF fun wellFormed => ?_
    obtain ⟨_, firstClosedTranslation, firstClosedEquality⟩ :=
      translateUnusedBinder wellFormed secondDomainType bodiesDependent.1 alignedFirstBody
    obtain ⟨_, secondClosedTranslation, secondClosedEquality⟩ :=
      translateUnusedBinder wellFormed secondDomainType bodiesDependent.2 secondBodyTranslation
    exact (isDefEqLambda.scopeWF (variables := default :: variables) (by simp [substitutions])
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨rfl, closedVariables⟩)
      firstClosedTranslation secondClosedTranslation).mono fun _ _ _ compared accepted =>
      have extendedContext := ⟨localContext.Δwf, secondDomainType⟩
      have ⟨_, bodyConversion⟩ := bodyEquality.symm.trans localContext.Ewf extendedContext firstClosedEquality
        |>.trans localContext.Ewf extendedContext ((compared accepted).weak localContext.Ewf
          (B := secondDomainSemantic))
        |>.trans localContext.Ewf extendedContext secondClosedEquality.symm
      ⟨_, .symm <| .lamDF typedDomainEquality.symm bodyConversion.symm⟩

theorem isDefEqForall.scopeWF {context : VContext} {state : VState}
    {locals : MLCtx} [localsWF : context.MLCWF locals]
    {first second : Expr} {firstSemantic secondSemantic : VExpr} {substitution : Array Expr}
    {variables : List Expr} (substitutions : substitution.toList.reverse = variables)
    (closedVariables : ∀ value ∈ variables, value.looseBVarRange' = 0)
    (firstTranslation : (context.withMLC locals).TrExprS (first.instantiateList variables) firstSemantic)
    (secondTranslation : (context.withMLC locals).TrExprS (second.instantiateList variables) secondSemantic) :
    (isDefEqForall first second substitution).ScopeWF (context.withMLC locals) state
      (fun equal _ => equal → (context.withMLC locals).IsDefEqU firstSemantic secondSemantic) := by
  unfold isDefEqForall
  let localContext := context.withMLC locals
  have instantiateMany (expression : Expr) (depth : Nat) :=
    Expr.instantiateMany_eq_instantiateList expression variables depth closedVariables
  split <;> [rename_i firstName firstDomain firstBody firstBinder secondName secondDomain secondBody secondBinder;
    (simp [substitutions, instantiateMany]; exact isDefEq.scopeWF firstTranslation secondTranslation)]
  extract_lets bodyWorker firstInstantiatedDomain secondInstantiatedDomain domainWorker
  unfold domainWorker firstInstantiatedDomain secondInstantiatedDomain
  simp at firstTranslation secondTranslation
  let .forallE (ty' := firstDomainSemantic) (body' := firstBodySemantic)
    ⟨_, firstDomainTyping⟩ _ firstDomainTranslation firstBodyTranslation := firstTranslation
  let .forallE (ty' := secondDomainSemantic) (body' := secondBodySemantic)
    secondDomainType ⟨_, secondBodyTyping⟩ secondDomainTranslation secondBodyTranslation := secondTranslation
  suffices ∀ {selectedDomain currentState}
      (_ : match selectedDomain with
        | none => firstDomain == secondDomain
        | some domain => domain = secondDomain.instantiateList variables),
      localContext.IsDefEqU firstDomainSemantic secondDomainSemantic →
      (bodyWorker selectedDomain).ScopeWF localContext currentState
        (fun equal _ => equal → localContext.IsDefEqU
          (firstDomainSemantic.forallE firstBodySemantic) (secondDomainSemantic.forallE secondBodySemantic)) by
    split <;> rename_i domainMatch
    · refine RecM.ScopeWF.pureBind <| this ‹_› ?_
      exact (firstDomainTranslation.eqv (Expr.instantiateList_eqv domainMatch)).uniq
        localContext.Ewf (.refl localContext.Ewf localContext.Δwf) secondDomainTranslation
    simp [substitutions, instantiateMany]
    refine (isDefEq.scopeWF firstDomainTranslation secondDomainTranslation).bind
      fun equal _ _ domainsEqual => ?_
    split <;> [exact RecM.ScopeWF.pure nofun; rename_i accepted]
    simp at accepted
    exact this rfl (domainsEqual accepted)
  intro selectedDomain currentState selected domainEquality
  have typedDomainEquality := domainEquality.of_l localContext.Ewf localContext.Δwf firstDomainTyping
  have ⟨_, alignedFirstBody, bodyEquality⟩ := firstBodyTranslation.defeqDFC' localContext.Ewf <|
    .cons (.refl localContext.Ewf localContext.Δwf) (by nofun) (.vlam typedDomainEquality)
  unfold bodyWorker
  split <;> rename_i bodiesDependent
  · extract_lets selectedType
    have selectedTypeEq : selectedType = secondDomain.instantiateList variables := by
      split at selected <;> [simp [selectedType, substitutions, instantiateMany]; exact selected]
    clear_value selectedType
    subst selectedTypeEq
    refine RecM.ScopeWF.stateWF fun wellFormed => ?_
    let identifier : FVarId := ⟨currentState.ngen.curr⟩
    let extended := locals.vlam identifier secondName (secondDomain.instantiateList variables)
      secondDomainSemantic secondBinder
    have extendedWF : context.MLCWF extended :=
      ⟨localsWF.1, wellFormed.find?_eq_none currentState.ngen.not_reserves_self,
        secondDomainTranslation, secondDomainType⟩
    letI : context.MLCWF extended := extendedWF
    refine RecM.ScopeWF.withLocalDecl (cwf' := extendedWF) secondDomainTranslation secondDomainType ?_
    have secondInstantiatedBody := secondBodyTranslation.inst_fvar context.Ewf extendedWF.1.tr.wf
    have firstInstantiatedBody := alignedFirstBody.inst_fvar context.Ewf extendedWF.1.tr.wf
    rw [Expr.instantiateList_instantiate1_comm (by rfl), ← Expr.instantiateList]
      at firstInstantiatedBody secondInstantiatedBody
    refine (isDefEqForall.scopeWF (localsWF := extendedWF) (variables := .fvar identifier :: variables)
      (by simp [substitutions, identifier])
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨rfl, closedVariables⟩)
      firstInstantiatedBody secondInstantiatedBody).mono fun _ _ _ compared accepted => ?_
    have bodyConversion := bodyEquality.symm.trans localContext.Ewf extendedWF.1.tr.wf.toCtx
      (compared accepted) |>.of_r localContext.Ewf extendedWF.1.tr.wf.toCtx secondBodyTyping
    exact ⟨_, .symm <| .forallEDF typedDomainEquality.symm bodyConversion.symm⟩
  · simp [Expr.hasLooseBVars] at bodiesDependent
    refine RecM.ScopeWF.stateWF fun wellFormed => ?_
    obtain ⟨_, firstClosedTranslation, firstClosedEquality⟩ :=
      translateUnusedBinder wellFormed secondDomainType bodiesDependent.1 alignedFirstBody
    obtain ⟨_, secondClosedTranslation, secondClosedEquality⟩ :=
      translateUnusedBinder wellFormed secondDomainType bodiesDependent.2 secondBodyTranslation
    exact (isDefEqForall.scopeWF (variables := default :: variables) (by simp [substitutions])
      (by simp only [List.mem_cons, forall_eq_or_imp]; exact ⟨rfl, closedVariables⟩)
      firstClosedTranslation secondClosedTranslation).mono fun _ _ _ compared accepted =>
      have extendedContext := ⟨localContext.Δwf, secondDomainType⟩
      have bodyConversion := bodyEquality.symm.trans localContext.Ewf extendedContext firstClosedEquality
        |>.trans localContext.Ewf extendedContext ((compared accepted).weak localContext.Ewf
          (B := secondDomainSemantic))
        |>.trans localContext.Ewf extendedContext secondClosedEquality.symm
        |>.of_r localContext.Ewf extendedContext secondBodyTyping
      ⟨_, .symm <| .forallEDF typedDomainEquality.symm bodyConversion.symm⟩

theorem isDefEqLambda.scopeWF_empty {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqLambda first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  context.withMLC_self ▸ isDefEqLambda.scopeWF (substitution := #[]) (variables := [])
    rfl (by simp) (context.withMLC_self ▸ firstTranslation) (context.withMLC_self ▸ secondTranslation)

theorem isDefEqForall.scopeWF_empty {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqForall first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) :=
  context.withMLC_self ▸ isDefEqForall.scopeWF (substitution := #[]) (variables := [])
    rfl (by simp) (context.withMLC_self ▸ firstTranslation) (context.withMLC_self ▸ secondTranslation)

theorem _root_.Lean4Lean.TypeChecker.RecM.ScopeWF.toLBoolM
    {context : VContext} {state : VState} {post : VState → Prop} {action : RecM Bool}
    (valid : action.ScopeWF context state (fun equal finalState => equal → post finalState)) :
    (toLBoolM action).ScopeWF context state (fun equal finalState => equal = .true → post finalState) :=
  valid.bind fun _ _ _ compared => RecM.ScopeWF.pure fun accepted => compared (by simpa using accepted)

theorem quickIsDefEq.scopeWF {context : VContext} {state : VState}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (quickIsDefEq first second useHash).ScopeWF context state
      (fun equal _ => equal = .true → context.IsDefEqU firstSemantic secondSemantic) := by
  unfold quickIsDefEq
  refine RecM.ScopeWF.bind (post := fun equal _ => equal = true →
    context.IsDefEqU firstSemantic secondSemantic) ?_ fun _ _ _ compared => ?_
  · intro methods callbacks caches wellFormed _ reachedState accepted
    simp [modifyGet, MonadStateOf.modifyGet, monadLift, MonadLift.monadLift, StateT.modifyGet,
      pure, Except.pure] at accepted
    split at accepted
    rename_i equal _ actual updatedManager managerLookup
    change let updated := _; (_, updated) = _ at accepted
    extract_lets updated at accepted
    injection accepted
    subst actual reachedState
    let ⟨_, _, levelsWF, contextLift, managerWF, reserved⟩ := wellFormed.ectx
    have ⟨updatedManagerWF, _, equality⟩ := EquivManager.isEquiv.WF managerWF managerLookup
    refine let finalModel := { state with toState := updated };
      ⟨finalModel, rfl, .rfl, { wellFormed with ectx := ?_ }, caches, ?_⟩
    · exact ⟨_, _, levelsWF, contextLift, updatedManagerWF, reserved⟩
    · intro accepted
      apply (VEnv.IsDefEqU.weak'_iff context.Ewf levelsWF contextLift.toCtx).1
      exact (equality accepted).uniq context.Ewf (contextLift.bvars_eq.trans context.mlctx.noBV)
        levelsWF (firstTranslation.weakFV' context.Ewf contextLift levelsWF)
        (secondTranslation.weakFV' context.Ewf contextLift levelsWF)
  extract_lets branchWorker
  split <;> [exact RecM.ScopeWF.pure fun _ => compared ‹_›; skip]
  refine RecM.ScopeWF.pureBind ?_
  unfold branchWorker
  split
  · exact RecM.ScopeWF.toLBoolM (isDefEqLambda.scopeWF_empty firstTranslation secondTranslation)
  · exact RecM.ScopeWF.toLBoolM (isDefEqForall.scopeWF_empty firstTranslation secondTranslation)
  · have .sort firstLevel := firstTranslation
    have .sort secondLevel := secondTranslation
    refine RecM.ScopeWF.pure fun accepted => ⟨_, .sortDF (.of_ofLevel firstLevel)
      (.of_ofLevel secondLevel) ?_⟩
    exact Level.isEquiv'_wf (toLBool_true.1 accepted) firstLevel secondLevel
  · let .mdata firstTranslation := firstTranslation
    let .mdata secondTranslation := secondTranslation
    exact RecM.ScopeWF.toLBoolM (isDefEq.scopeWF firstTranslation secondTranslation)
  · cases firstTranslation
  · rename_i firstLiteral secondLiteral _
    refine RecM.ScopeWF.pure fun accepted => ?_
    simp at accepted
    subst accepted
    exact firstTranslation.uniq context.Ewf (.refl context.Ewf context.Δwf) secondTranslation
  · exact RecM.ScopeWF.pure nofun

end Lean4Lean.TypeChecker.Inner
