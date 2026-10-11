import Lean4Lean.Verify.TypeChecker.ScopedWHNF
import Lean4Lean.Verify.TypeChecker.InferType

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open TypeChecker

theorem TypeChecker.VState.WF.next {context : VContext} {state : VState}
    (valid : state.WF context) : state.next.WF context := by
  constructor
  · exact valid.trctx
  · intro freeVariable member
    exact (valid.ngen_wf freeVariable member).mono .next
  · obtain ⟨levels, count, levelsWF, contextLift, managerWF, reserved⟩ := valid.ectx
    exact ⟨levels, count, levelsWF, contextLift, managerWF,
      fun freeVariable member => (reserved freeVariable member).mono .next⟩
  · intro expression type found
    exact (valid.inferTypeI_wf found).mono .next
  · intro expression type found
    exact (valid.inferTypeC_wf found).mono .next
  · intro expression value found
    exact (valid.whnfCore_wf found).mono .next
  · intro expression value found
    exact (valid.whnf_wf found).mono .next
  · exact valid.unfold_wf

theorem TypeChecker.VState.WF.mkLocalDecl {c : VContext} {m : MLCtx}
    [cwf : c.MLCWF m] {state : VState} {name : Name} {domain : Expr} {domain' : VExpr}
    {binder : BinderInfo}
    {cwf' : c.MLCWF (m.vlam ⟨state.ngen.curr⟩ name domain domain' binder)}
    (valid : state.WF (c.withMLC m))
    (domainTranslation : (c.withMLC m).TrExprS domain domain')
    (domainType : (c.withMLC m).IsType domain') :
    state.next.WF (c.withMLC
      (m.vlam ⟨state.ngen.curr⟩ name domain domain' binder) (wf := cwf')) := by
  letI := cwf'
  have h0 := state.ngen.next_reserves_self
  have h1 := state.ngen.not_reserves_self
  have le : state ≤ state.next := .next
  have fresh := valid.find?_eq_none h1
  let m' := m.vlam ⟨state.ngen.curr⟩ name domain domain' binder
  have trctx : (c.withMLC m').TrLCtx := valid.trctx.mkLocalDecl fresh domainTranslation domainType
  have inferCache {cache} (cacheWF : InferCache.WF (c.withMLC m) state cache) :
      InferCache.WF (c.withMLC m') state.next cache :=
    fun _ _ found => ((cacheWF found).fresh c.Ewf.ordered trctx.wf).mono le
  have whnfCache {cache} (cacheWF : WHNFCache.WF (c.withMLC m) state cache) :
      WHNFCache.WF (c.withMLC m') state.next cache :=
    fun _ _ found => ((cacheWF found).fresh c.Ewf trctx.wf).mono le
  exact {
    ngen_wf := by
      simp [m', VContext.withMLC]
      exact ⟨h0, fun _ h => le.reservesV (valid.ngen_wf _ h)⟩
    ectx := by
      let ⟨_, _, a1, a2, a3, a4⟩ := valid.ectx
      refine
        have b1 := ⟨a1, ?_, domainType.weak' c.Ewf.ordered a2.toCtx⟩
        ⟨_, _, b1, a2.cons_fvar _ _ domainTranslation.fvarsList,
          a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
          fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
      rintro _ _ ⟨⟩
      exact ⟨mt (a4 _) h1, domainTranslation.fvarsList.trans a2.fvars_sublist.subset⟩
    trctx, inferTypeI_wf := inferCache valid.inferTypeI_wf, inferTypeC_wf := inferCache valid.inferTypeC_wf
    whnfCore_wf := whnfCache valid.whnfCore_wf, whnf_wf := whnfCache valid.whnf_wf, unfold_wf := valid.unfold_wf }

theorem TypeChecker.VState.WF.mkLetDecl {c : VContext} {m : MLCtx}
    [cwf : c.MLCWF m] {state : VState} {name : Name} {type value : Expr}
    {type' value' : VExpr}
    {cwf' : c.MLCWF (m.vlet ⟨state.ngen.curr⟩ name type value type' value')}
    (valid : state.WF (c.withMLC m))
    (typeTranslation : (c.withMLC m).TrExprS type type')
    (valueTranslation : (c.withMLC m).TrExprS value value')
    (valueType : (c.withMLC m).HasType value' type') :
    state.next.WF (c.withMLC
      (m.vlet ⟨state.ngen.curr⟩ name type value type' value') (wf := cwf')) := by
  letI := cwf'
  have h0 := state.ngen.next_reserves_self
  have h1 := state.ngen.not_reserves_self
  have le : state ≤ state.next := .next
  have fresh := valid.find?_eq_none h1
  let m' := m.vlet ⟨state.ngen.curr⟩ name type value type' value'
  have trctx : (c.withMLC m').TrLCtx :=
    valid.trctx.mkLetDecl fresh typeTranslation valueTranslation valueType
  have inferCache {cache} (cacheWF : InferCache.WF (c.withMLC m) state cache) :
      InferCache.WF (c.withMLC m') state.next cache :=
    fun _ _ found => ((cacheWF found).fresh c.Ewf.ordered trctx.wf).mono le
  have whnfCache {cache} (cacheWF : WHNFCache.WF (c.withMLC m) state cache) :
      WHNFCache.WF (c.withMLC m') state.next cache :=
    fun _ _ found => ((cacheWF found).fresh c.Ewf trctx.wf).mono le
  exact {
    ngen_wf := by
      simp [m', VContext.withMLC]
      exact ⟨h0, fun _ h => le.reservesV (valid.ngen_wf _ h)⟩
    ectx := by
      let ⟨_, _, a1, a2, a3, a4⟩ := valid.ectx
      have values := List.append_subset.2 ⟨typeTranslation.fvarsList, valueTranslation.fvarsList⟩
      refine
        have b1 := ⟨a1, ?_, valueType.weak' c.Ewf.ordered a2.toCtx⟩
        ⟨_, _, b1, a2.cons_fvar _ _ values,
          a3.weak' c.Ewf (.skip_fvar _ _ .refl) b1,
          fun _ h => by obtain _ | ⟨_, h⟩ := h <;> [exact h0; exact (a4 _ h).mono le]⟩
      rintro _ _ ⟨⟩
      exact ⟨mt (a4 _) h1, values.trans a2.fvars_sublist.subset⟩
    trctx, inferTypeI_wf := inferCache valid.inferTypeI_wf, inferTypeC_wf := inferCache valid.inferTypeC_wf
    whnfCore_wf := whnfCache valid.whnfCore_wf, whnf_wf := whnfCache valid.whnf_wf, unfold_wf := valid.unfold_wf }

theorem TypeChecker.RecM.ScopeWF.withLocalDecl {c : VContext} {m : MLCtx}
    [cwf : c.MLCWF m] {state : VState} {continuation : Expr → RecM Result}
    {post : Result → VState → Prop} {name : Name} {domain : Expr} {domain' : VExpr}
    {binder : BinderInfo}
    {cwf' : c.MLCWF (m.vlam ⟨state.ngen.curr⟩ name domain domain' binder)}
    (domainTranslation : (c.withMLC m).TrExprS domain domain')
    (domainType : (c.withMLC m).IsType domain')
    (valid : (continuation (.fvar ⟨state.ngen.curr⟩)).ScopeWF
      (c.withMLC (m.vlam ⟨state.ngen.curr⟩ name domain domain' binder) (wf := cwf'))
      state.next post) :
    (withLocalDecl name binder domain continuation).ScopeWF (c.withMLC m) state post := by
  unfold TypeChecker.RecM.ScopeWF
  intro methods callbacks caches wellFormed result finalState accepted
  let id : FVarId := ⟨state.ngen.curr⟩
  have fresh := wellFormed.find?_eq_none state.ngen.not_reserves_self
  let m' := m.vlam id name domain domain' binder
  letI : c.MLCWF m' := cwf'
  have extendedWF : state.next.WF (c.withMLC m') :=
    TypeChecker.VState.WF.mkLocalDecl wellFormed domainTranslation domainType
  have extendedCaches : HeadScopeCacheWF (c.withMLC m').lctx' state.next.toState := by
    simpa [m', VContext.withMLC, VState.next] using
      caches.mkLocalDecl wellFormed.trctx.1 wellFormed.localNames name domain binder
  change continuation (.fvar id) methods (c.withMLC m').toContext state.next.toState =
    .ok (result, finalState) at accepted
  have final := valid methods callbacks extendedCaches extendedWF result finalState accepted
  obtain ⟨updated, equal, increasing, updatedWF, ⟨updatedCaches, resultPost⟩⟩ := final
  have inferCache {cache} (cacheWF : InferCache.WF (c.withMLC m') updated cache) :
      InferCache.WF (c.withMLC m) updated cache := by
    intro expression type found
    exact (cacheWF found).weakN_inv c.Ewf updatedWF.trctx.wf
  have whnfCache {cache} (cacheWF : WHNFCache.WF (c.withMLC m') updated cache) :
      WHNFCache.WF (c.withMLC m) updated cache := by
    intro expression value found
    exact (cacheWF found).weakN_inv c.Ewf updatedWF.trctx.wf
  have baseWF : updated.WF (c.withMLC m) := by
    let ⟨_, _, levelsWF, contextLift, managerWF, reserved⟩ := updatedWF.ectx
    exact {
      ngen_wf := (by simpa [VContext.withMLC] using updatedWF.ngen_wf :).2
      ectx := ⟨_, _, levelsWF, .comp (.skip_fvar _ _ .refl) contextLift, managerWF, reserved⟩
      trctx := wellFormed.trctx
      inferTypeI_wf := inferCache updatedWF.inferTypeI_wf
      inferTypeC_wf := inferCache updatedWF.inferTypeC_wf
      whnfCore_wf := whnfCache updatedWF.whnfCore_wf
      whnf_wf := whnfCache updatedWF.whnf_wf
      unfold_wf := updatedWF.unfold_wf }
  have restoredCaches : HeadScopeCacheWF (c.withMLC m).lctx' updated.toState := by
    simpa [m', VContext.withMLC] using
      updatedCaches.leaveLocalDecl wellFormed.trctx.1 id fresh name domain binder
  exact ⟨updated, equal, NameGenerator.LE.next.trans increasing, baseWF,
    restoredCaches, resultPost⟩

theorem TypeChecker.RecM.ScopeWF.withLetDecl {c : VContext} {m : MLCtx}
    [cwf : c.MLCWF m] {state : VState} {continuation : Expr → RecM Result}
    {post : Result → VState → Prop} {name : Name} {type value : Expr}
    {type' value' : VExpr}
    {cwf' : c.MLCWF (m.vlet ⟨state.ngen.curr⟩ name type value type' value')}
    (typeTranslation : (c.withMLC m).TrExprS type type')
    (valueTranslation : (c.withMLC m).TrExprS value value')
    (valueType : (c.withMLC m).HasType value' type')
    (valid : (continuation (.fvar ⟨state.ngen.curr⟩)).ScopeWF
      (c.withMLC (m.vlet ⟨state.ngen.curr⟩ name type value type' value') (wf := cwf'))
      state.next post) :
    (withLetDecl name type value continuation).ScopeWF (c.withMLC m) state post := by
  unfold TypeChecker.RecM.ScopeWF
  intro methods callbacks caches wellFormed result finalState accepted
  let id : FVarId := ⟨state.ngen.curr⟩
  have fresh := wellFormed.find?_eq_none state.ngen.not_reserves_self
  let m' := m.vlet id name type value type' value'
  letI : c.MLCWF m' := cwf'
  have extendedWF : state.next.WF (c.withMLC m') :=
    TypeChecker.VState.WF.mkLetDecl wellFormed typeTranslation valueTranslation valueType
  have extendedCaches : HeadScopeCacheWF (c.withMLC m').lctx' state.next.toState := by
    simpa [m', VContext.withMLC, VState.next] using
      caches.mkLetDecl wellFormed.trctx.1 wellFormed.localNames wellFormed.headCacheNames
        name type value
  change continuation (.fvar id) methods (c.withMLC m').toContext state.next.toState =
    .ok (result, finalState) at accepted
  have final := valid methods callbacks extendedCaches extendedWF result finalState accepted
  obtain ⟨updated, equal, increasing, updatedWF, ⟨updatedCaches, resultPost⟩⟩ := final
  have inferCache {cache} (cacheWF : InferCache.WF (c.withMLC m') updated cache) :
      InferCache.WF (c.withMLC m) updated cache := by
    intro expression type found
    exact (cacheWF found).weakN_inv c.Ewf updatedWF.trctx.wf
  have whnfCache {cache} (cacheWF : WHNFCache.WF (c.withMLC m') updated cache) :
      WHNFCache.WF (c.withMLC m) updated cache := by
    intro expression value found
    exact (cacheWF found).weakN_inv c.Ewf updatedWF.trctx.wf
  have baseWF : updated.WF (c.withMLC m) := by
    let ⟨_, _, levelsWF, contextLift, managerWF, reserved⟩ := updatedWF.ectx
    exact {
      ngen_wf := (by simpa [VContext.withMLC] using updatedWF.ngen_wf :).2
      ectx := ⟨_, _, levelsWF, .comp (.skip_fvar _ _ .refl) contextLift, managerWF, reserved⟩
      trctx := wellFormed.trctx
      inferTypeI_wf := inferCache updatedWF.inferTypeI_wf
      inferTypeC_wf := inferCache updatedWF.inferTypeC_wf
      whnfCore_wf := whnfCache updatedWF.whnfCore_wf
      whnf_wf := whnfCache updatedWF.whnf_wf
      unfold_wf := updatedWF.unfold_wf }
  have restoredCaches : HeadScopeCacheWF (c.withMLC m).lctx' updated.toState := by
    simpa [m', VContext.withMLC] using
      updatedCaches.leaveLetDecl wellFormed.trctx.1 id fresh name type value
  exact ⟨updated, equal, NameGenerator.LE.next.trans increasing, baseWF,
    restoredCaches, resultPost⟩

theorem TypeChecker.HeadScopeCacheWF.next {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) :
    HeadScopeCacheWF locals { state with ngen := state.ngen.next } := by
  exact stable

theorem TypeChecker.RecM.ScopeWF.withFreshId {context : VContext} {state : VState}
    {continuation : Name → RecM Result} {post : Result → VState → Prop}
    (valid : ∀ name,
      (continuation name).ScopeWF context state.next post) :
    (withFreshId continuation).ScopeWF context state post := by
  intro methods callbacks caches wellFormed result finalState accepted
  change continuation state.ngen.curr methods context.toContext state.next.toState =
    .ok (result, finalState) at accepted
  have final := valid state.ngen.curr methods callbacks
    (by simpa [VState.next] using caches.next)
    (wellFormed.next) result finalState accepted
  obtain ⟨updated, equal, increasing, wellFormed', scopedPost⟩ := final
  exact ⟨updated, equal, NameGenerator.LE.next.trans increasing, wellFormed', scopedPost⟩

namespace TypeChecker.Inner

theorem inferType.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (inferType expression inferOnly).ScopeWF context state fun type _ =>
      ∃ expression' semanticType, context.TrTyping expression type expression' semanticType := by
  intro methods callbacks
  change (methods.inferType expression inferOnly).ScopeWF context state _
  exact callbacks.inferType freeVariables translated

theorem checkType.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (inferType expression false).ScopeWF context state fun type _ =>
      ∃ expression' semanticType, context.TrTyping expression type expression' semanticType := by
  exact inferType.scopeWF freeVariables (by simp)

theorem ensureSortCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (ensureSortCore expression expected).ScopeWF context state fun result _ =>
      (∃ level, result = .sort level) ∧ context.TrExpr result semantic ∧
        context.FVarsBelow expression result := by
  simp [ensureSortCore]
  split
  · let .sort level := expression
    exact RecM.ScopeWF.pure ⟨⟨level, rfl⟩, translated.trExpr context.Ewf context.Δwf, .rfl⟩
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨below, normalizedTranslation, _⟩ := normalizedResult
  split
  · let .sort level := normalized
    exact RecM.ScopeWF.pure ⟨⟨level, rfl⟩, normalizedTranslation, below⟩
  exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw

theorem ensureForallCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (ensureForallCore expression expected).ScopeWF context state fun result _ =>
      context.FVarsBelow expression result ∧ context.TrExpr result semantic ∧
        ∃ name domain body binder, result = .forallE name domain body binder := by
  simp [ensureForallCore]
  split
  · let .forallE name domain body binder := expression
    exact RecM.ScopeWF.pure ⟨.rfl, translated.trExpr context.Ewf context.Δwf,
      _, _, _, _, rfl⟩
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨below, normalizedTranslation, _⟩ := normalizedResult
  split
  · let .forallE name domain body binder := normalized
    exact RecM.ScopeWF.pure ⟨below, normalizedTranslation, _, _, _, _, rfl⟩
  exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw

theorem inferFVar.scopeWF {context : VContext} {state : VState} {name : FVarId} :
    RecM.ScopeWF context state (readThe Context >>= fun context => liftM (inferFVar context name))
      (fun type _ =>
        ∃ expression semanticType, context.TrTyping (.fvar name) type expression semanticType) :=
  by
    apply RecM.ScopeWF.readThe
    change RecM.ScopeWF context state (liftM (inferFVar context.toContext name)) _
    exact RecM.ScopeWF.liftExcept inferFVar.WF

theorem checkLevel.scopeWF {context : VContext} {state : VState} {level : Level}
    (valid : level.hasMVar' = false) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context => liftM (checkLevel context level))
      (fun _ _ => ∃ level', VLevel.ofLevel context.lparams level = some level') := by
  apply RecM.ScopeWF.readThe
  change RecM.ScopeWF context state (liftM (checkLevel context.toContext level)) _
  exact RecM.ScopeWF.liftExcept (checkLevel.WF valid)

theorem envGet.scopeWF {context : VContext} {state : VState} {name : Name} :
    RecM.ScopeWF context state
      ((liftM TypeChecker.getEnv : RecM Environment) >>= fun environment =>
        liftM (environment.get name))
      (fun info _ => context.env.find? name = some info) := by
  apply RecM.ScopeWF.getEnv
  exact RecM.ScopeWF.liftExcept envGet.WF

theorem inferConstant.scopeWF {context : VContext} {state : VState}
    {name : Name} {levels : List Level} {inferOnly : Bool}
    (validLevels : ∀ level ∈ levels, level.hasMVar' = false)
    (validInference : inferOnly = true → ∃ expression,
      context.TrExprS (.const name levels) expression) :
    RecM.ScopeWF context state
      (readThe Context >>= fun context =>
        liftM (inferConstant context name levels inferOnly))
      (fun type _ => ∃ expression semanticType,
        context.TrTyping (.const name levels) type expression semanticType) := by
  apply RecM.ScopeWF.readThe
  change RecM.ScopeWF context state
    (liftM (inferConstant context.toContext name levels inferOnly)) _
  exact RecM.ScopeWF.liftExcept (inferConstant.WF validLevels validInference)

theorem inferLambda.loop.scopeWF {context : VContext} {state : VState}
    {initialExpression : Expr} {locals : MLCtx} [localsWF : context.MLCWF locals]
    {binderCount : Nat} (countBound : binderCount ≤ locals.length)
    (dropped : locals.dropN binderCount countBound = context.mlctx)
    (arguments : args.toList.reverse = (locals.fvarRevList binderCount countBound).map .fvar)
    (initial : initialExpression = locals.mkLambda binderCount countBound instantiated)
    (instantiation : expression.instantiateList
      ((locals.fvarRevList binderCount countBound).map .fvar) = instantiated)
    (below : ∀ predicate, IsFVarUpSet predicate context.vlctx → FVarsIn predicate initialExpression →
      IsFVarUpSet (AllAbove context.vlctx predicate) locals.vlctx ∧
      FVarsIn (AllAbove context.vlctx predicate) instantiated ∧
      ∀ type, FVarsIn (AllAbove context.vlctx predicate) type →
        FVarsIn (AllAbove context.vlctx predicate) (locals.mkForall binderCount countBound type))
    (freeVariables : expression.FVarsIn (· ∈ locals.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, (context.withMLC locals).TrExprS instantiated semantic) :
    (inferLambda.loop inferOnly args expression).ScopeWF (context.withMLC locals) state
      fun type _ => ∃ semantic semanticType, context.TrTyping initialExpression type semantic semanticType := by
  unfold inferLambda.loop
  generalize variablesEq : (locals.fvarRevList binderCount countBound).map Expr.fvar = variables at *
  have closed : ∀ value ∈ variables, value.looseBVarRange' = 0 := by
    intro value member
    rw [← variablesEq] at member
    obtain ⟨identifier, _, rfl⟩ := List.mem_map.mp member
    rfl
  have many (value : Expr) (depth : Nat) :=
    Expr.instantiateMany_eq_instantiateList value variables depth closed
  simp [arguments, many, -bind_pure_comp]
  split
  · rename_i name domain body binder
    generalize actionEq : withLocalDecl (m := RecM) _ _ _ _ = action
    generalize postEq : (fun type finalState => ∃ _, _) = post
    rw [Expr.instantiateList_lam] at instantiation
    subst instantiated
    have main {middleState : VState} {domain'}
        (domainType : (context.withMLC locals).IsType domain')
        (domainTranslation : (context.withMLC locals).TrExprS (domain.instantiateList variables) domain')
        (bodyTranslation : inferOnly = true → ∃ body',
          TrExprS context.venv context.lparams ((none, .vlam domain') :: locals.vlctx)
            (body.instantiateList variables 1) body') :
        action.ScopeWF (context.withMLC locals) middleState post := by
      refine RecM.ScopeWF.stateWF fun wellFormed => ?_
      let identifier : FVarId := ⟨middleState.ngen.curr⟩
      have fresh : ¬middleState.ngen.Reserves identifier := middleState.ngen.not_reserves_self
      let extended := locals.vlam identifier name (domain.instantiateList variables) domain' binder
      have extendedWF : context.MLCWF extended :=
        ⟨localsWF.1, wellFormed.find?_eq_none fresh, domainTranslation, domainType⟩
      letI : context.MLCWF extended := extendedWF
      subst actionEq postEq
      refine RecM.ScopeWF.withLocalDecl (cwf' := extendedWF) domainTranslation domainType ?_
      have commute := @Expr.instantiateList_instantiate1_comm body variables (.fvar identifier) (by trivial)
      refine inferLambda.loop.scopeWF (Nat.succ_le_succ countBound) (by simp [dropped])
        (by simp [← variablesEq, arguments]) ?_ (by simp; rfl) ?_
        (freeVariables.2.mono fun _ => .tail _) ?_
      · rw [initial, variablesEq, ← commute]
        simp
        congr 2
        refine (FVarsIn.abstract_instantiate1 ((freeVariables.2.instantiateList ?_ _).mono ?_)).symm
        · simp [← variablesEq, FVarsIn]
          exact locals.fvarRevList_prefix.subset
        · rintro _ member rfl
          exact (extendedWF.1.tr.wf.2.1 _ _ rfl).1 member
      · intro predicate upSet inputScope
        have ⟨upSet', inputScope', closeScope⟩ := below _ upSet inputScope
        refine ⟨⟨upSet', fun _ => (fvarsIn_iff.1 inputScope'.1).1⟩, ?_,
          fun type typeScope => closeScope _ ⟨inputScope'.1, typeScope.abstract1⟩⟩
        rw [variablesEq, ← commute]
        refine inputScope'.2.instantiate1 fun member => ?_
        exact fresh.elim (wellFormed.ngen_wf _
          (locals.dropN_fvars_subset binderCount countBound (dropped ▸ member)))
      · intro checked
        let ⟨_, bodyTranslation⟩ := bodyTranslation checked
        exact variablesEq.symm ▸ commute ▸
          ⟨_, bodyTranslation.inst_fvar context.Ewf.ordered extendedWF.1.tr.wf⟩
    split
    · subst inferOnly
      refine (checkType.scopeWF ?_).bind fun universeType _ _
        ⟨domain', universe', _, domainTranslation, universeTranslation, domainTyping⟩ => ?_
      · apply freeVariables.1.instantiateList
        simp [← variablesEq]
        exact locals.fvarRevList_prefix.subset
      refine (ensureSortCore.scopeWF universeTranslation).bind fun _ _ _ ⟨sort, sortTranslation, _⟩ => ?_
      obtain ⟨_, rfl⟩ := sort
      let ⟨_, .sort _, sortEquality⟩ := sortTranslation
      have domainType := domainTyping.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx sortEquality.symm
      exact main ⟨_, domainType⟩ domainTranslation nofun
    · simp_all
      let ⟨_, lambdaTranslation⟩ := translated
      have .lam (ty' := domain') (body' := body') domainType domainTranslation bodyTranslation := lambdaTranslation
      exact main domainType domainTranslation _ bodyTranslation
  · subst instantiated
    refine (inferType.scopeWF ?_ translated).bind fun type _ _
      ⟨semantic, semanticType, typeBelow, expressionTranslation, typeTranslation, typing⟩ => ?_
    · apply freeVariables.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine RecM.ScopeWF.stateWF fun wellFormed => RecM.ScopeWF.getLCtx <| RecM.ScopeWF.pure ?_
    have ⟨_, reducedTranslation, reductionEquality⟩ := typeTranslation.trExpr context.Ewf.ordered wellFormed.trctx.wf
      |>.cheapBetaReduce context.Ewf wellFormed.trctx.wf locals.noBV
    have typing := typing.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx reductionEquality.symm
    let ⟨lambdaTranslation, lambdaTyping⟩ := localsWF.1.mkLambda_trS context.Ewf expressionTranslation typing binderCount countBound
    have forallTranslation := (localsWF.1.mkForall_trS context.Ewf reducedTranslation
      (typing.isType context.Ewf localsWF.1.tr.wf.toCtx) binderCount countBound).1
    simp [dropped] at lambdaTranslation lambdaTyping forallTranslation
    refine localsWF.1.mkForall_eq _ _ (variablesEq ▸ arguments)
      (locals.noBV ▸ reducedTranslation.closed).looseBVarRange_zero ▸
      ⟨_, _, fun predicate upSet inputScope => ?_, initial ▸ lambdaTranslation, forallTranslation, lambdaTyping⟩
    have ⟨upSet', inputScope', closeScope⟩ := below _ upSet inputScope
    have outputScope := closeScope _ <| FVarsBelow.cheapBetaReduce (locals.noBV ▸ typeTranslation.closed) _ upSet' <|
      typeBelow _ upSet' inputScope'
    exact outputScope.mp (fun _ => id) forallTranslation.fvarsIn

theorem inferLambda.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (inferLambda expression inferOnly).ScopeWF context state
      fun type _ => ∃ semantic semanticType, context.TrTyping expression type semantic semanticType := by
  refine RecM.ScopeWF.stateWF fun wellFormed => ?_
  refine (context.withMLC_self ▸ inferLambda.loop.scopeWF (Nat.zero_le _) rfl rfl rfl rfl ?_ freeVariables) translated
  exact fun predicate upSet inputScope =>
    ⟨(AllAbove.wf wellFormed.trctx.wf.fvwf).2 upSet, inputScope.mono fun _ member _ => member, fun _ => id⟩

end TypeChecker.Inner
end Lean4Lean
