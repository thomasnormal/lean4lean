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

end TypeChecker.Inner
end Lean4Lean
