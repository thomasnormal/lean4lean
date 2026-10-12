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

theorem inferType.scopeWF_of_translation {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (inferType expression true).ScopeWF context state fun type _ =>
      ∃ semanticType, context.TrTyping expression type semantic semanticType := by
  refine (inferType.scopeWF translated.fvarsIn (fun _ => ⟨_, translated⟩)).mono
    fun _ _ _ ⟨_, _, below, source, typeTranslation, typing⟩ => ?_
  exact ⟨_, below, translated, typeTranslation, typing.defeqU_l context.Ewf context.Δwf
    (source.uniq context.Ewf (.refl context.Ewf context.Δwf) translated)⟩

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

theorem isProp.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (isProp expression).ScopeWF context state
      (fun result _ => result → context.HasType semantic (.sort .zero)) := by
  unfold isProp
  refine (inferType.scopeWF translated.fvarsIn (fun _ => ⟨_, translated⟩)).bind
    fun type _ _ typeResult => ?_
  obtain ⟨_, _, typing⟩ := typeResult
  obtain ⟨_, expressionTranslation, typeTranslation, typing⟩ := typing
  have expressionEquality := expressionTranslation.uniq context.Ewf
    (.refl context.Ewf context.Δwf) translated
  refine (Inner.whnf.scopeWF typeTranslation).bind
    fun normalized _ _ normalizedResult => ?_
  obtain ⟨_, normalizedTranslation, _⟩ := normalizedResult
  by_cases proposition : normalized == Expr.prop
  · have normalizedEq : normalized = .sort .zero := by
      simpa [Expr.prop, Expr.eqv_sort] using proposition
    subst normalized
    have proposition : (Expr.sort .zero == Expr.prop) = true := by
      simp [Expr.prop, Expr.eqv_sort]
    rw [proposition]
    exact RecM.ScopeWF.pure fun equal => by
      cases equal
      obtain ⟨_, source, equality⟩ := normalizedTranslation
      cases source with
      | sort level =>
        simp [VLevel.ofLevel] at *
        cases level
        exact (typing.defeqU_l context.Ewf context.Δwf expressionEquality).defeqU_r
          context.Ewf context.Δwf equality.symm
  · have proposition : (normalized == Expr.prop) = false := by
      cases h : normalized == Expr.prop <;> simp_all
    rw [proposition]
    exact RecM.ScopeWF.pure nofun

theorem nativeProjectionField.scopeWF {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (parent : Name) (structureExpr : Expr)
    (propositional : Bool) (index : Nat) (current : Expr)
    (translated : context.TrExprS current semantic) :
    (nativeProjectionField environment source parent structureExpr propositional index current).ScopeWF
      context state (fun _ _ => True) := by
  unfold nativeProjectionField
  dsimp only [Bind.bind, ReaderT.bind]
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨_, normalizedTranslation, _⟩ := normalizedResult
  cases normalized <;> try exact nativeProjectionFailure.scopeWF environment source
  case forallE name domain body binder =>
    dsimp only
    split
    · cases propositional <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
      · exact RecM.ScopeWF.pure (result := ForInStep.yield _) trivial
      · obtain ⟨_, sourceTranslation, _⟩ := normalizedTranslation
        let .forallE _ _ domainTranslation _ := sourceTranslation
        refine (Inner.isProp.scopeWF domainTranslation).bind fun proposition _ _ _ => ?_
        cases proposition <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        · exact nativeProjectionFailure.scopeWF environment source
        · exact RecM.ScopeWF.pure (result := ForInStep.yield _) trivial
    · exact RecM.ScopeWF.pure (result := ForInStep.yield _) trivial

theorem nativeProjectionFinal.scopeWF {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (propositional : Bool) (current : Expr)
    (translated : context.TrExprS current semantic) :
    (nativeProjectionFinal environment source propositional current).ScopeWF context state
      (fun _ _ => True) := by
  unfold nativeProjectionFinal
  dsimp only [Bind.bind, ReaderT.bind]
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ normalizedResult => ?_
  obtain ⟨_, normalizedTranslation, _⟩ := normalizedResult
  cases normalized <;> try exact nativeProjectionFailure.scopeWF environment source
  case forallE name domain body binder =>
    dsimp only
    cases propositional <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    · exact RecM.ScopeWF.pure trivial
    · obtain ⟨_, sourceTranslation, _⟩ := normalizedTranslation
      let .forallE _ _ domainTranslation _ := sourceTranslation
      refine (Inner.isProp.scopeWF domainTranslation).bind fun proposition _ _ _ => ?_
      cases proposition <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
      · exact nativeProjectionFailure.scopeWF environment source
      · exact RecM.ScopeWF.pure trivial

theorem inferProj.scopeWF {context : VContext} {state : VState}
    (typed : context.TrTyping expression type semantic semanticType) :
    (inferProj parent index expression type).ScopeWF context state fun result _ =>
      ∃ projected resultType, context.TrTyping (.proj parent index expression) result projected resultType :=
  RecM.ScopeWF.of_rejects (inferProj.rejects typed.2.2.1)

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

theorem inferForall.loop.scopeWF {context : VContext} {state : VState}
    {initialExpression : Expr} {locals : MLCtx} [localsWF : context.MLCWF locals]
    {binderCount : Nat} (countBound : binderCount ≤ locals.length)
    (dropped : locals.dropN binderCount countBound = context.mlctx)
    (arguments : args.toList.reverse = (locals.fvarRevList binderCount countBound).map .fvar)
    (initial : initialExpression = locals.mkForall binderCount countBound instantiated)
    (instantiation : expression.instantiateList
      ((locals.fvarRevList binderCount countBound).map .fvar) = instantiated)
    (freeVariables : expression.FVarsIn (· ∈ locals.vlctx.fvars))
    (levels : universes.toList.reverse.Forall₂ (VLevel.ofLevel context.lparams · = some ·) semanticUniverses)
    (sorts : locals.vlctx.SortList context.venv context.lparams.length semanticUniverses)
    (levelCount : semanticUniverses.length = binderCount)
    (translated : inferOnly = true → ∃ semantic, (context.withMLC locals).TrExprS instantiated semantic) :
    (inferForall.loop inferOnly args universes expression).ScopeWF (context.withMLC locals) state
      fun type _ => ∃ semantic level, context.TrTyping initialExpression type semantic (.sort level) := by
  unfold inferForall.loop
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
    rw [Expr.instantiateList_forallE] at instantiation
    subst instantiated
    refine (inferType.scopeWF ?_ ?_).bind fun universeType _ _
      ⟨domain', universe', _, domainTranslation, universeTranslation, domainTyping⟩ => ?_
    · apply freeVariables.1.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    · intro checked
      let ⟨_, .forallE _ _ domainTranslation _⟩ := translated checked
      exact ⟨_, domainTranslation⟩
    refine (ensureSortCore.scopeWF universeTranslation).bind fun _ middleState _
      ⟨sort, sortTranslation, _⟩ => ?_
    obtain ⟨_, rfl⟩ := sort
    let ⟨_, .sort levelTranslation, sortEquality⟩ := sortTranslation
    refine RecM.ScopeWF.stateWF fun wellFormed => ?_
    have domainTyping := domainTyping.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx sortEquality.symm
    have domainType : (context.withMLC locals).IsType domain' := ⟨_, domainTyping⟩
    let identifier : FVarId := ⟨middleState.ngen.curr⟩
    let extended := locals.vlam identifier name (domain.instantiateList variables) domain' binder
    have extendedWF : context.MLCWF extended :=
      ⟨localsWF.1, wellFormed.find?_eq_none middleState.ngen.not_reserves_self,
        domainTranslation, domainType⟩
    letI : context.MLCWF extended := extendedWF
    refine RecM.ScopeWF.withLocalDecl (cwf' := extendedWF) domainTranslation domainType ?_
    have commute := @Expr.instantiateList_instantiate1_comm body variables (.fvar identifier) (by trivial)
    refine inferForall.loop.scopeWF (Nat.succ_le_succ countBound) (by simp [dropped])
      (by simp [variablesEq, arguments]) ?_ (by simp [variablesEq]; rfl)
      (freeVariables.2.mono fun _ => .tail _)
      (by simpa using ⟨levelTranslation, levels⟩) (.cons sorts domainTyping) (by simp [levelCount]) ?_
    · rw [initial, ← commute]
      simp
      congr 2
      refine (FVarsIn.abstract_instantiate1 ((freeVariables.2.instantiateList ?_ _).mono ?_)).symm
      · simp [← variablesEq, FVarsIn]
        exact locals.fvarRevList_prefix.subset
      · rintro _ member rfl
        exact (extendedWF.1.tr.wf.2.1 _ _ rfl).1 member
    · intro checked
      let ⟨_, .forallE (body' := body') _ _ domainTranslation' bodyTranslation⟩ := translated checked
      have contextEquality := VLCtx.IsDefEq.refl context.Ewf localsWF.1.tr.wf
      have domainEquality := domainTranslation'.uniq context.Ewf contextEquality domainTranslation
      have domainEquality := domainEquality.of_r context.Ewf localsWF.1.tr.wf.toCtx domainTyping
      have ⟨_, bodyTranslation'⟩ := bodyTranslation.defeqDFC context.Ewf <|
        .cons contextEquality (ofv := none) nofun (.vlam domainEquality)
      exact commute ▸ ⟨_, bodyTranslation'.inst_fvar context.Ewf.ordered extendedWF.1.tr.wf⟩
  · subst instantiated
    refine (inferType.scopeWF ?_ translated).bind fun type _ _
      ⟨semantic, semanticType, _, expressionTranslation, typeTranslation, typing⟩ => ?_
    · apply freeVariables.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine (ensureSortCore.scopeWF typeTranslation).bind fun _ _ _ ⟨sort, sortTranslation, _⟩ => ?_
    obtain ⟨_, rfl⟩ := sort
    let ⟨_, .sort (u' := semanticLevel) levelTranslation, sortEquality⟩ := sortTranslation
    obtain ⟨universes, rfl⟩ : ∃ values, ⟨List.reverse values⟩ = universes :=
      ⟨universes.toList.reverse, by simp⟩
    simp [Expr.sortLevel!] at levels ⊢
    have typing := typing.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx sortEquality.symm
    let ⟨forallTranslation, _⟩ := localsWF.1.mkForall_trS context.Ewf expressionTranslation
      ⟨_, typing⟩ binderCount countBound
    have ⟨_, resultLevel, forallTyping⟩ := mkForall_hasType levels sorts levelTranslation typing
      binderCount countBound (levels.length_eq.trans levelCount)
    simp [dropped] at forallTranslation forallTyping
    have resultTranslation : context.TrExprS (.sort _) (.sort _) := TrExprS.sort resultLevel
    exact RecM.ScopeWF.pure
      ⟨_, _, fun _ _ _ => resultTranslation.fvarsIn, initial ▸ forallTranslation, resultTranslation, forallTyping⟩

theorem inferForall.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (inferForall expression inferOnly).ScopeWF context state
      fun type _ => ∃ semantic level, context.TrTyping expression type semantic (.sort level) :=
  (context.withMLC_self ▸ inferForall.loop.scopeWF (Nat.zero_le _) rfl rfl rfl rfl
    freeVariables .nil .nil rfl) translated

theorem inferLet.loop.scopeWF_inferOnly {context : VContext} {state : VState}
    {initialExpression : Expr} {locals : MLCtx} [localsWF : context.MLCWF locals]
    {binderCount : Nat} {declarations : List (Option Bool)}
    (countBound : binderCount ≤ locals.length)
    (declarationsBound : declarations.length = binderCount)
    (dropped : locals.dropN binderCount countBound = context.mlctx)
    (arguments : args.toList.reverse = (locals.fvarRevList binderCount countBound).map .fvar)
    (initial : initialExpression = locals.mkLet binderCount countBound declarations declarationsBound instantiated)
    (instantiation : expression.instantiateList
      ((locals.fvarRevList binderCount countBound).map .fvar) = instantiated)
    (below : ∀ predicate, IsFVarUpSet predicate context.vlctx → FVarsIn predicate initialExpression →
      IsFVarUpSet (AllAbove context.vlctx predicate) locals.vlctx ∧
      FVarsIn (AllAbove context.vlctx predicate) instantiated ∧
      ∀ type, FVarsIn (AllAbove context.vlctx predicate) type →
        FVarsIn (AllAbove context.vlctx predicate) (locals.mkForall binderCount countBound type))
    (freeVariables : expression.FVarsIn (· ∈ locals.vlctx.fvars))
    (translated : ∃ semantic, (context.withMLC locals).TrExprS instantiated semantic) :
    (inferLet.loop true args expression).ScopeWF (context.withMLC locals) state
      fun type _ => ∃ semantic semanticType, context.TrTyping initialExpression type semantic semanticType := by
  refine RecM.ScopeWF.stateWF fun wellFormed => ?_
  unfold inferLet.loop
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
  · rename_i name domain value body declaration
    rw [Expr.instantiateList_letE] at instantiation
    subst instantiated
    let ⟨_, .letE (ty' := domain') (val' := value') (body' := body')
      valueType domainTranslation valueTranslation bodyTranslation⟩ := translated
    let identifier : FVarId := ⟨state.ngen.curr⟩
    let extended := locals.vlet identifier name (domain.instantiateList variables)
      (value.instantiateList variables) domain' value'
    have extendedWF : context.MLCWF extended :=
      ⟨localsWF.1, wellFormed.find?_eq_none state.ngen.not_reserves_self,
        domainTranslation, valueTranslation, valueType⟩
    letI : context.MLCWF extended := extendedWF
    refine RecM.ScopeWF.withLetDecl (cwf' := extendedWF) domainTranslation valueTranslation valueType ?_
    have commute := @Expr.instantiateList_instantiate1_comm body variables (.fvar identifier) (by trivial)
    refine inferLet.loop.scopeWF_inferOnly (declarations := some declaration :: declarations)
      (Nat.succ_le_succ countBound) (by simp [declarationsBound]) (by simp [dropped])
      (by simp [variablesEq, arguments]) ?_ (by simp [variablesEq]; rfl) ?_
      (freeVariables.2.2.mono fun _ => .tail _) ?_
    · rw [initial, ← commute]
      have step :
          (MLCtx.vlet identifier name (domain.instantiateList variables)
            (value.instantiateList variables) domain' value' locals).mkLet
              (Nat.succ binderCount) (Nat.succ_le_succ countBound)
              (some declaration :: declarations) (by simp [declarationsBound])
              ((body.instantiateList variables 1).instantiate1' (.fvar identifier)) =
            locals.mkLet binderCount countBound declarations declarationsBound
              (MLCtx.mkLetArg identifier name (domain.instantiateList variables)
                (value.instantiateList variables) declaration
                ((body.instantiateList variables 1).instantiate1' (.fvar identifier))) := by
        rfl
      dsimp [extended, identifier]
      calc
        _ = locals.mkLet binderCount countBound declarations declarationsBound
            (MLCtx.mkLetArg identifier name (domain.instantiateList variables)
              (value.instantiateList variables) declaration
              ((body.instantiateList variables 1).instantiate1' (.fvar identifier))) := by
          simp [MLCtx.mkLetArg]
          congr 2
          refine (FVarsIn.abstract_instantiate1 ((freeVariables.2.2.instantiateList ?_ _).mono ?_)).symm
          · simp [← variablesEq, FVarsIn]
            exact locals.fvarRevList_prefix.subset
          · rintro _ member rfl
            exact (extendedWF.1.tr.wf.2.1 _ _ rfl).1 member
        _ = _ := step.symm
    · intro predicate upSet inputScope
      have ⟨upSet', inputScope', typeBelow⟩ := below _ upSet inputScope
      refine ⟨⟨upSet', fun _ => ?_⟩, ?_, fun type typeScope => ?_⟩
      · simp [or_imp, forall_and]
        exact ⟨(fvarsIn_iff.1 inputScope'.1).1, (fvarsIn_iff.1 inputScope'.2.1).1⟩
      · have bodyScope := inputScope'.2.2
        have fvarScope : FVarsIn (AllAbove context.vlctx predicate) (.fvar identifier) := by
          intro member
          exact state.ngen.not_reserves_self.elim (wellFormed.ngen_wf _
            (locals.dropN_fvars_subset binderCount countBound (dropped ▸ member)))
        have bodyScope' := bodyScope.instantiate1 fvarScope
        exact commute ▸ bodyScope'
      · simp
        split <;> rename_i hasBinder
        · exact typeBelow _ ⟨inputScope'.1, inputScope'.2.1, typeScope.abstract1⟩
        · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using hasBinder)]
          exact typeBelow _ (typeScope.abstract1.instantiate1 rfl)
    · have bodyTranslation' := bodyTranslation.inst_fvar context.Ewf.ordered extendedWF.1.tr.wf
      refine ⟨body', ?_⟩
      simpa [commute, identifier, extended] using bodyTranslation'
  · subst instantiated
    refine (inferType.scopeWF ?_ (fun _ => translated)).bind fun type _ _
      ⟨semantic, semanticType, bodyBelow, expressionTranslation, typeTranslation, typing⟩ => ?_
    · apply freeVariables.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine RecM.ScopeWF.stateWF fun wellFormed => RecM.ScopeWF.getLCtx <| RecM.ScopeWF.pure ?_
    have ⟨_, reducedTranslation, reductionEquality⟩ := typeTranslation.trExpr context.Ewf.ordered wellFormed.trctx.wf
      |>.cheapBetaReduce context.Ewf wellFormed.trctx.wf locals.noBV
    have typing := typing.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx reductionEquality.symm
    let ⟨wholeTranslation, wholeTyping⟩ := localsWF.1.mkLet_trS context.Ewf expressionTranslation typing
      binderCount countBound declarations declarationsBound
    let ⟨forallTranslation, forallTyping⟩ := localsWF.1.mkForall_trS context.Ewf reducedTranslation
      (typing.isType context.Ewf localsWF.1.tr.wf.toCtx) binderCount countBound
    simp [dropped] at wholeTranslation wholeTyping forallTranslation forallTyping
    refine localsWF.1.mkForall_eq _ _ (variablesEq ▸ arguments)
      (locals.noBV ▸ reducedTranslation.closed).looseBVarRange_zero ▸
      ⟨_, _, fun predicate upSet inputScope => ?_, initial ▸ wholeTranslation,
        forallTranslation, wholeTyping⟩
    have ⟨upSet', inputScope', typeBelow⟩ := below _ upSet inputScope
    have typeScope := FVarsBelow.cheapBetaReduce (locals.noBV ▸ typeTranslation.closed) _ upSet' <|
      bodyBelow _ upSet' inputScope'
    exact (typeBelow _ typeScope).mp (fun _ => id) forallTranslation.fvarsIn

theorem inferLet.scopeWF_inferOnly {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : context.TrExprS expression semantic) :
    (inferLet expression true).ScopeWF context state
      fun type _ => ∃ semantic semanticType, context.TrTyping expression type semantic semanticType := by
  refine RecM.ScopeWF.stateWF fun wellFormed => ?_
  refine context.withMLC_self ▸ inferLet.loop.scopeWF_inferOnly (declarations := [])
    (Nat.zero_le _) rfl rfl rfl rfl rfl ?_ freeVariables ⟨_, translated⟩
  exact fun predicate upSet inputScope =>
    ⟨(AllAbove.wf wellFormed.trctx.wf.fvwf).2 upSet,
      inputScope.mono fun _ member _ => member, fun _ => id⟩

theorem inferLet.loop.scopeWF {context : VContext} {state : VState}
    {initialExpression : Expr} {locals : MLCtx} [localsWF : context.MLCWF locals]
    {binderCount : Nat} {declarations : List (Option Bool)}
    (countBound : binderCount ≤ locals.length)
    (declarationsBound : declarations.length = binderCount)
    (dropped : locals.dropN binderCount countBound = context.mlctx)
    (arguments : args.toList.reverse = (locals.fvarRevList binderCount countBound).map .fvar)
    (initial : initialExpression = locals.mkLet binderCount countBound declarations declarationsBound instantiated)
    (instantiation : expression.instantiateList
      ((locals.fvarRevList binderCount countBound).map .fvar) = instantiated)
    (below : ∀ predicate, IsFVarUpSet predicate context.vlctx → FVarsIn predicate initialExpression →
      IsFVarUpSet (AllAbove context.vlctx predicate) locals.vlctx ∧
      FVarsIn (AllAbove context.vlctx predicate) instantiated ∧
      ∀ type, FVarsIn (AllAbove context.vlctx predicate) type →
        FVarsIn (AllAbove context.vlctx predicate) (locals.mkForall binderCount countBound type))
    (freeVariables : expression.FVarsIn (· ∈ locals.vlctx.fvars)) :
    (inferLet.loop false args expression).ScopeWF (context.withMLC locals) state
      fun type _ => ∃ semantic semanticType, context.TrTyping initialExpression type semantic semanticType := by
  refine RecM.ScopeWF.stateWF fun wellFormed => ?_
  unfold inferLet.loop
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
  · rename_i name domain value body declaration
    rw [Expr.instantiateList_letE] at instantiation
    subst instantiated
    refine (checkType.scopeWF ?_).bind fun domainType _ _
      ⟨domainSemantic, _, _, domainTranslation, domainTypeTranslation, _⟩ => ?_
    · apply freeVariables.1.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine (ensureSortCore.scopeWF domainTypeTranslation).bind fun sortedDomain _ _
      ⟨⟨_, sortedDomainEq⟩, sortedDomainTranslation, _⟩ => ?_
    subst sortedDomainEq
    let ⟨_, .sort _, _⟩ := sortedDomainTranslation
    refine (checkType.scopeWF ?_).bind fun valueType _ _
      ⟨valueSemantic, _, _, valueTranslation, valueTypeTranslation, valueTyping⟩ => ?_
    · apply freeVariables.2.1.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine (isDefEq.scopeWF valueTypeTranslation domainTranslation).bind fun equal middleState _ equalProof => ?_
    cases equal <;> simp
    · exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw
    · refine RecM.ScopeWF.stateWF fun middleWellFormed => ?_
      have valueType' := valueTyping.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx (equalProof rfl)
      let identifier : FVarId := ⟨middleState.ngen.curr⟩
      let extended := locals.vlet identifier name
        (domain.instantiateList variables) (value.instantiateList variables) domainSemantic valueSemantic
      have extendedWF : context.MLCWF extended :=
        ⟨localsWF.1, middleWellFormed.find?_eq_none middleState.ngen.not_reserves_self,
          domainTranslation, valueTranslation, valueType'⟩
      letI : context.MLCWF extended := extendedWF
      refine RecM.ScopeWF.withLetDecl (type' := domainSemantic) (value' := valueSemantic)
        (cwf' := extendedWF) domainTranslation valueTranslation valueType' ?_
      have commute := @Expr.instantiateList_instantiate1_comm body variables (.fvar identifier) (by trivial)
      refine inferLet.loop.scopeWF (declarations := some declaration :: declarations)
        (Nat.succ_le_succ countBound) (by simp [declarationsBound]) (by simp [dropped])
        (by simp [variablesEq, arguments]) ?_ (by simp [variablesEq]; rfl) ?_
        (freeVariables.2.2.mono fun _ => .tail _)
      · rw [initial, ← commute]
        have step :
            (MLCtx.vlet identifier name (domain.instantiateList variables)
              (value.instantiateList variables) domainSemantic valueSemantic locals).mkLet
                (Nat.succ binderCount) (Nat.succ_le_succ countBound)
                (some declaration :: declarations) (by simp [declarationsBound])
                ((body.instantiateList variables 1).instantiate1' (.fvar identifier)) =
              locals.mkLet binderCount countBound declarations declarationsBound
                (MLCtx.mkLetArg identifier name (domain.instantiateList variables)
                  (value.instantiateList variables) declaration
                  ((body.instantiateList variables 1).instantiate1' (.fvar identifier))) := by
          rfl
        dsimp [extended, identifier]
        calc
          _ = locals.mkLet binderCount countBound declarations declarationsBound
              (MLCtx.mkLetArg identifier name (domain.instantiateList variables)
                (value.instantiateList variables) declaration
                ((body.instantiateList variables 1).instantiate1' (.fvar identifier))) := by
            simp [MLCtx.mkLetArg]
            congr 2
            refine (FVarsIn.abstract_instantiate1 ((freeVariables.2.2.instantiateList ?_ _).mono ?_)).symm
            · simp [← variablesEq, FVarsIn]
              exact locals.fvarRevList_prefix.subset
            · rintro _ member rfl
              exact (extendedWF.1.tr.wf.2.1 _ _ rfl).1 member
          _ = _ := step.symm
      · intro predicate upSet inputScope
        have ⟨upSet', inputScope', typeBelow⟩ := below _ upSet inputScope
        refine ⟨⟨upSet', fun _ => ?_⟩, ?_, fun type typeScope => ?_⟩
        · simp [or_imp, forall_and]
          exact ⟨(fvarsIn_iff.1 inputScope'.1).1, (fvarsIn_iff.1 inputScope'.2.1).1⟩
        · have bodyScope := inputScope'.2.2
          have fvarScope : FVarsIn (AllAbove context.vlctx predicate) (.fvar identifier) := by
            intro member
            exact middleState.ngen.not_reserves_self.elim (middleWellFormed.ngen_wf _
              (locals.dropN_fvars_subset binderCount countBound (dropped ▸ member)))
          have bodyScope' := bodyScope.instantiate1 fvarScope
          exact commute ▸ bodyScope'
        · simp
          split <;> rename_i hasBinder
          · exact typeBelow _ ⟨inputScope'.1, inputScope'.2.1, typeScope.abstract1⟩
          · rw [Expr.lowerLooseBVars_eq_instantiate (v := .sort .zero) (by simpa using hasBinder)]
            exact typeBelow _ (typeScope.abstract1.instantiate1 rfl)
  · subst instantiated
    refine (inferType.scopeWF ?_ (by simp)).bind fun type _ _
      ⟨semantic, semanticType, bodyBelow, expressionTranslation, typeTranslation, typing⟩ => ?_
    · apply freeVariables.instantiateList
      simp [← variablesEq]
      exact locals.fvarRevList_prefix.subset
    refine RecM.ScopeWF.stateWF fun wellFormed => RecM.ScopeWF.getLCtx <| RecM.ScopeWF.pure ?_
    have ⟨_, reducedTranslation, reductionEquality⟩ := typeTranslation.trExpr context.Ewf.ordered wellFormed.trctx.wf
      |>.cheapBetaReduce context.Ewf wellFormed.trctx.wf locals.noBV
    have typing := typing.defeqU_r context.Ewf localsWF.1.tr.wf.toCtx reductionEquality.symm
    let ⟨wholeTranslation, wholeTyping⟩ := localsWF.1.mkLet_trS context.Ewf expressionTranslation typing
      binderCount countBound declarations declarationsBound
    let ⟨forallTranslation, forallTyping⟩ := localsWF.1.mkForall_trS context.Ewf reducedTranslation
      (typing.isType context.Ewf localsWF.1.tr.wf.toCtx) binderCount countBound
    simp [dropped] at wholeTranslation wholeTyping forallTranslation forallTyping
    refine localsWF.1.mkForall_eq _ _ (variablesEq ▸ arguments)
      (locals.noBV ▸ reducedTranslation.closed).looseBVarRange_zero ▸
      ⟨_, _, fun predicate upSet inputScope => ?_, initial ▸ wholeTranslation,
        forallTranslation, wholeTyping⟩
    have ⟨upSet', inputScope', typeBelow⟩ := below _ upSet inputScope
    have typeScope := FVarsBelow.cheapBetaReduce (locals.noBV ▸ typeTranslation.closed) _ upSet' <|
      bodyBelow _ upSet' inputScope'
    exact (typeBelow _ typeScope).mp (fun _ => id) forallTranslation.fvarsIn
termination_by expression

theorem inferLet.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars)) :
    (inferLet expression false).ScopeWF context state
      fun type _ => ∃ semantic semanticType, context.TrTyping expression type semantic semanticType := by
  refine RecM.ScopeWF.stateWF fun wellFormed => ?_
  refine context.withMLC_self ▸ inferLet.loop.scopeWF (declarations := [])
    (Nat.zero_le _) rfl rfl rfl rfl rfl ?_ freeVariables
  exact fun predicate upSet inputScope =>
    ⟨(AllAbove.wf wellFormed.trctx.wf.fvwf).2 upSet,
      inputScope.mono fun _ member _ => member, fun _ => id⟩

theorem inferApp.loop.scopeWF {context : VContext} {state : VState}
    {ll lm lr : List _}
    (stack : AppStack context.venv context.lparams context.vlctx (.mkAppRevList e lm) e' lr)
    (below : FVarsBelow context.vlctx e fType)
    (functionType : context.TrExpr (fType.instantiateList lm) functionSemantic)
    (expressionType : context.HasType e' functionSemantic)
    (arguments : args = ll ++ lm.reverse ++ lr)
    (headIndex : j = ll.length) (pendingIndex : i = ll.length + lm.length) :
    (inferApp.loop e₀ ⟨args⟩ fType j i).ScopeWF context state (fun type _ =>
      ∃ resultSemantic resultType, context.TrTyping
        (e.mkAppRevList lm |>.mkAppList lr) type resultSemantic resultType) := by
  subst i j
  rw [inferApp.loop.eq_def]
  have closed := Expr.mkAppRevList_args_noLooseBVars e lm
    (context.mlctx.noBV ▸ stack.tr.closed).looseBVarRange_zero
  have many (expression : Expr) (depth : Nat) :=
    Expr.instantiateMany_eq_instantiateList expression lm depth closed
  simp [arguments]
  cases lr with simp
  | cons argument lr =>
    let .app functionTypeTyping argumentTypeTyping functionTranslation argumentTranslation stack := stack
    have uniqueFunction := functionTypeTyping.uniqU context.Ewf context.Δwf expressionType
    split
    · rw [Expr.instantiateList_forallE] at functionType
      let ⟨_, .forallE _ _ domainTranslation bodyTranslation, functionTypeEq⟩ := functionType
      have ⟨⟨_, domainLevel⟩, _, bodyLevel⟩ :=
        functionTypeEq.trans context.Ewf context.Δwf uniqueFunction.symm |>.forallE_inv context.Ewf context.Δwf
      refine inferApp.loop.scopeWF (lm := argument :: lm) stack ?_ ?_ (.app functionTypeTyping argumentTypeTyping)
        (by simp) rfl rfl
      · exact fun _ predicate member => (below _ predicate member).2
      · have closedArgument := context.mlctx.noBV ▸ argumentTranslation.closed
        simp [← Expr.instantiateList_instantiate1_comm closedArgument.looseBVarRange_zero]
        exact .inst context.Ewf context.Δwf
          (argumentTypeTyping.defeqU_r context.Ewf context.Δwf ⟨_, domainLevel.symm⟩)
          ⟨_, bodyTranslation, _, bodyLevel⟩ (argumentTranslation.trExpr context.Ewf context.Δwf)
    · simp [Nat.add_sub_cancel_left, many]
      let ⟨_, functionTypeTranslation, functionTypeEq⟩ := functionType
      refine (ensureForallCore.scopeWF functionTypeTranslation).bind fun normalized _ _
        ⟨normalizedBelow, normalizedTranslation, forallShape⟩ => ?_
      obtain ⟨name, domain, body, binder, normalizedEq⟩ := forallShape
      subst normalizedEq
      simp [Expr.bindingBody!]
      let ⟨_, forallTypeTranslation, forallTypeEq⟩ := normalizedTranslation
      let .forallE _ _ domainTranslation bodyTranslation := forallTypeTranslation
      have uniqueForall := forallTypeEq.trans context.Ewf context.Δwf <|
        functionTypeEq.trans context.Ewf context.Δwf uniqueFunction.symm
      have ⟨⟨_, domainLevel⟩, _, bodyLevel⟩ :=
        uniqueForall.forallE_inv context.Ewf context.Δwf
      refine inferApp.loop.scopeWF (ll := ll ++ lm.reverse) (lm := [argument]) stack ?_ ?_
        (.app functionTypeTyping argumentTypeTyping) (by simp) (by simp) (by simp)
      · intro _ predicate member
        have ⟨headMember, argumentMembers⟩ := FVarsIn.appRevList.1 member
        exact (normalizedBelow _ predicate <| (below _ predicate headMember).instantiateList argumentMembers).2
      · exact .inst context.Ewf context.Δwf
          (argumentTypeTyping.defeqU_r context.Ewf context.Δwf ⟨_, domainLevel.symm⟩)
          ⟨_, bodyTranslation, _, bodyLevel⟩ (argumentTranslation.trExpr context.Ewf context.Δwf)
  | nil =>
    rw [← List.length_reverse, List.take_length]
    simp only [List.reverse_reverse, many]
    let ⟨functionTypeSemantic, functionTypeTranslation, functionTypeEq⟩ := functionType
    exact RecM.ScopeWF.pure ⟨_, _, fun _ predicate member => by
        have ⟨headMember, argumentMembers⟩ := FVarsIn.appRevList.1 member
        exact (below _ predicate headMember).instantiateList argumentMembers,
      stack.tr, functionTypeTranslation, expressionType.defeqU_r context.Ewf context.Δwf functionTypeEq.symm⟩
termination_by lr.length


theorem inferApp.scopeWF {context : VContext} {state : VState} {expression : Expr} {semantic : VExpr}
    (translated : context.TrExprS expression semantic) :
    (inferApp expression).ScopeWF context state
      (fun type _ => ∃ typeSemantic, context.TrTyping expression type semantic typeSemantic) := by
  rw [inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  have ⟨_, stack⟩ := AppStack.build <| expression.mkAppList_getAppArgsList ▸ translated
  refine (inferType.scopeWF stack.tr.fvarsIn (fun _ => ⟨_, stack.tr⟩)).bind fun type _ _
    ⟨_, typeSemanticType, typeBelow, expressionTranslation, typeTranslation, typeTyping⟩ => ?_
  have equal := expressionTranslation.uniq context.Ewf (.refl context.Ewf context.Δwf) stack.tr
  have typeTyping := typeTyping.defeqU_l context.Ewf context.Δwf equal
  have environmentWF := context.Ewf
  have contextWF := context.Δwf
  refine (inferApp.loop.scopeWF (ll := []) (lm := []) stack typeBelow
      (typeTranslation.trExpr environmentWF contextWF) typeTyping rfl rfl rfl).mono
    fun _ _ _ ⟨resultSemantic, resultType, below, expressionTranslation, typeTranslation, typing⟩ => ?_
  have unique := (expression.mkAppList_getAppArgsList ▸ expressionTranslation).uniq environmentWF
    (.refl environmentWF contextWF) translated
  exact ⟨resultType, expression.mkAppList_getAppArgsList ▸ below, translated,
    typeTranslation, typing.defeqU_l environmentWF contextWF unique⟩

theorem inferType'.scopeWF {context : VContext} {state : VState}
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (inferType' expression inferOnly).ScopeWF context state fun type _ =>
      ∃ semantic semanticType, context.TrTyping expression type semantic semanticType := by
  unfold inferType'; lift_lets; intro save dispatch worker
  split <;> [exact RecM.ScopeWF.throw; refine RecM.ScopeWF.get <| RecM.ScopeWF.get ?_]
  split
  · rename_i found
    refine RecM.ScopeWF.stateWF fun wellFormed => RecM.ScopeWF.pure ?_
    generalize selected : cond .. = cache at found
    have validCache : cache.WF context state := by
      subst cache
      cases inferOnly <;> [exact wellFormed.inferTypeC_wf; exact wellFormed.inferTypeI_wf]
    exact (validCache found).2.2.2.2 freeVariables
  generalize postEq : (fun type : Expr => _) = post
  have saveWF {type semantic semanticType state}
      (typing : context.TrTyping expression type semantic semanticType) :
      (save type).ScopeWF context state post := by
    rintro methods callbacks caches wellFormed result finalState ⟨⟩
    refine let finalState := _; ⟨finalState, rfl, ?_⟩
    have insertWF {cache} (valid : InferCache.WF context state cache) :
        InferCache.WF context state (cache.insert expression type) := by
      intro _ _ found
      rw [Std.HashMap.getElem?_insert] at found
      split at found <;> [cases found; exact valid found]
      rename_i equal
      refine .mk context.mlctx.noBV (.eqv typing equal BEq.rfl) (.eqv equal ?_) ?_
      · exact typing.2.1.fvarsIn.mono wellFormed.ngen_wf
      · exact typing.2.2.1.fvarsIn.mono wellFormed.ngen_wf
    subst post
    revert finalState
    cases inferOnly <;>
      (dsimp -zeta; intro finalState; refine ⟨.rfl, ?_, caches, _, _, typing⟩)
    · exact { wellFormed with inferTypeC_wf := insertWF wellFormed.inferTypeC_wf }
    · exact { wellFormed with inferTypeI_wf := insertWF wellFormed.inferTypeI_wf }
  unfold dispatch
  refine RecM.ScopeWF.get ?_
  split
  · extract_lets literalWorker
    split <;> [split; skip]
    · refine RecM.ScopeWF.getEnv <| (RecM.ScopeWF.liftExcept envGet.WF).bind fun _ _ _ found => ?_
      have ⟨_, model, _⟩ := context.trenv.find? found <|
        (context.safePrimitives found (literal_is_primitive (.inl rfl))).1 ▸ DefinitionSafety.le_safe
      exact saveWF (infer_literal ⟨_, model⟩)
    · refine RecM.ScopeWF.getEnv <| (RecM.ScopeWF.liftExcept envGet.WF).bind fun _ _ _ firstFound => ?_
      refine RecM.ScopeWF.getEnv <| (RecM.ScopeWF.liftExcept envGet.WF).bind fun _ _ _ secondFound => ?_
      have ⟨_, firstModel, _⟩ := context.trenv.find? firstFound <|
        (context.safePrimitives firstFound (literal_is_primitive (.inr (.inl rfl)))).1 ▸ DefinitionSafety.le_safe
      have ⟨_, secondModel, _⟩ := context.trenv.find? secondFound <|
        (context.safePrimitives secondFound (literal_is_primitive (.inr (.inr rfl)))).1 ▸ DefinitionSafety.le_safe
      exact saveWF (infer_literal ⟨⟨_, firstModel⟩, ⟨_, secondModel⟩⟩)
    · rename_i inference
      have ⟨_, literalTranslation⟩ := translated (by simpa using inference)
      have literals := literalTranslation.lit_has_type
      simp [literalWorker]
      exact saveWF (infer_literal literals)
  · refine (inferType'.scopeWF (by exact freeVariables) ?_).bind
      fun _ _ _ ⟨_, _, below, expressionTranslation, typing⟩ => ?_
    · exact fun inference => let ⟨_, .mdata inner⟩ := translated inference; ⟨_, inner⟩
    exact saveWF ⟨below, .mdata expressionTranslation, typing⟩
  · refine (inferType'.scopeWF (by exact freeVariables) ?_).bind
      fun _ _ _ ⟨_, _, below, expressionTranslation, typeTranslation, typing⟩ => ?_
    · exact fun inference => let ⟨_, .proj inner ..⟩ := translated inference; ⟨_, inner⟩
    exact (inferProj.scopeWF ⟨below, expressionTranslation, typeTranslation, typing⟩).bind
      fun _ _ _ ⟨_, _, projectedTyping⟩ => saveWF projectedTyping
  · exact inferFVar.scopeWF.bind fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
  · exact RecM.ScopeWF.throw
  · rename_i loose _
    simp [Expr.hasLooseBVars, Expr.looseBVarRange'] at loose
  · split <;> rename_i inference
    · refine RecM.ScopeWF.readThe <|
        (RecM.ScopeWF.liftExcept (checkLevel.WF freeVariables)).bind fun _ _ _ ⟨_, levelTranslation⟩ => ?_
      exact saveWF (infer_sort levelTranslation)
    · let ⟨_, .sort levelTranslation⟩ := translated (by simpa using inference)
      exact saveWF (infer_sort levelTranslation)
  · exact (inferConstant.scopeWF freeVariables translated).bind fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
  · exact (inferLambda.scopeWF freeVariables translated).bind fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
  · exact (inferForall.scopeWF freeVariables translated).bind fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
  · split <;> rename_i inference
    · let ⟨_, applicationTranslation⟩ := translated inference
      exact (inferApp.scopeWF applicationTranslation).bind fun _ _ _ ⟨_, typing⟩ => saveWF typing
    refine (inferType'.scopeWF freeVariables.1 ?_).bind
      fun _ _ _ ⟨_, _, functionBelow, functionTranslation, functionTypeTranslation, functionTyping⟩ => ?_
    · exact fun inference => let ⟨_, .app _ _ function _⟩ := translated inference; ⟨_, function⟩
    refine (ensureForallCore.scopeWF functionTypeTranslation).bind fun _ _ _ forallWF => ?_
    obtain ⟨forallBelow, forallTranslation, name, domain, body, binder, rfl⟩ := forallWF
    let ⟨_, forallStructural, forallEquality⟩ := forallTranslation
    let .forallE (ty' := domainSemantic) _ _ domainTranslation bodyTranslation := forallStructural
    extract_lets _ functionWorker
    refine (inferType'.scopeWF freeVariables.2 ?_).bind
      fun _ _ _ ⟨_, argumentTypeSemantic, argumentBelow, argumentTranslation,
        argumentTypeTranslation, argumentTyping⟩ => ?_
    · exact fun inference => let ⟨_, .app _ _ _ argument⟩ := translated inference; ⟨_, argument⟩
    extract_lets comparisonWorker
    suffices ∀ {state equal} (matched : equal = true → context.IsDefEqU domainSemantic argumentTypeSemantic),
        (comparisonWorker equal).ScopeWF context state post by
      split
      · refine RecM.ScopeWF.bind ?_
          (post := fun equal _ => equal = true → context.IsDefEqU domainSemantic argumentTypeSemantic)
          fun _ _ _ matched => this matched
        intro methods callbacks caches wellFormed result finalState accepted
        let eagerContext := { context with eagerReduce := true }
        have ⟨finalModel, sameState, increasing, finalWF, finalCaches, equal⟩ :=
          isDefEq.scopeWF (context := eagerContext) domainTranslation argumentTypeTranslation
            methods callbacks caches { wellFormed with } result finalState accepted
        exact ⟨finalModel, sameState, increasing, { finalWF with }, finalCaches, equal⟩
      · exact (isDefEq.scopeWF domainTranslation argumentTypeTranslation).bind
          fun _ _ _ matched => this matched
    subst comparisonWorker
    dsimp
    rintro state ⟨⟩ matched
    · exact RecM.ScopeWF.getEnv <| RecM.ScopeWF.getLCtx RecM.ScopeWF.throw
    simp [functionWorker, Expr.bindingBody!]
    have functionTyping := functionTyping.defeqU_r context.Ewf context.Δwf forallEquality.symm
    have argumentTyping := argumentTyping.defeqU_r context.Ewf context.Δwf (matched rfl).symm
    subst postEq
    refine saveWF ⟨?_, .app functionTyping argumentTyping functionTranslation argumentTranslation,
      bodyTranslation.inst context.Ewf argumentTyping argumentTranslation, .app functionTyping argumentTyping⟩
    exact fun _ upSet inputScope =>
      (functionBelow.trans forallBelow _ upSet inputScope.1).2.instantiate1 inputScope.2
  · cases inferOnly
    · exact (inferLet.scopeWF freeVariables).bind fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
    · obtain ⟨_, letTranslation⟩ := translated rfl
      exact (inferLet.scopeWF_inferOnly freeVariables letTranslation).bind
        fun _ _ _ ⟨_, _, typing⟩ => saveWF typing
termination_by expression

end TypeChecker.Inner
end Lean4Lean
