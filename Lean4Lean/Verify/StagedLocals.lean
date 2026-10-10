import Lean4Lean.Verify.StagedApplications

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

namespace RestrictedContext

def InferCacheWF (context : RestrictedContext safety env venv) (state : State) (cache : InferCache) : Prop :=
  ∀ ⦃expression type : Expr⦄, cache[expression]? = some type →
    ConditionallyHasType state.ngen venv context.lparams context.scope expression type

def WHNFCacheWF (context : RestrictedContext safety env venv) (state : State) (cache : InferCache) : Prop :=
  ∀ ⦃expression result : Expr⦄, cache[expression]? = some result →
    ConditionallyWHNF state.ngen venv context.lparams context.scope expression result

structure StateWF (context : RestrictedContext safety env venv) (state : State) : Prop where
  reserved : ∀ identifier ∈ context.scope.fvars, state.ngen.Reserves identifier
  equivalence : ∃ scope shift, scope.WF venv context.lparams.length ∧
    context.scope.FVLift' scope 0 shift 0 ∧ state.eqvManager.WF venv context.lparams scope ∧
      ∀ identifier ∈ scope.fvars, state.ngen.Reserves identifier
  inferI : context.InferCacheWF state state.inferTypeI
  inferC : context.InferCacheWF state state.inferTypeC
  whnfCore : context.WHNFCacheWF state state.whnfCoreCache
  whnf : context.WHNFCacheWF state state.whnfCache
  unfold : ∀ ⦃expression result : Expr⦄, state.unfold[expression]? = some result →
    ∃ name levels info, expression = .const name levels ∧ env.find? name = some info ∧
      result = info.instantiateValueLevelParams! levels

theorem StateWF.empty (context : RestrictedContext safety env venv)
    (reserved : ∀ identifier ∈ context.scope.fvars, generator.Reserves identifier) :
    context.StateWF { ngen := generator } := by
  refine ⟨reserved, ⟨context.scope, .refl, context.scope_wf, .refl, .empty, reserved⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro expression result lookup; simp at lookup

theorem StateWF.find?_eq_none {context : RestrictedContext safety env venv}
    (stateWF : context.StateWF state) (fresh : ¬state.ngen.Reserves identifier) :
    context.mlctx.lctx.find? identifier = none :=
  context.trScope.find?_eq_none.2 fun member => fresh (stateWF.reserved _ member)

theorem StateWF.freshLambda {context : RestrictedContext safety env venv}
    (stateWF : context.StateWF state)
    (domainTr : TrExprS venv context.lparams context.scope domain semantic)
    (domainType : venv.IsType context.lparams.length context.scope.toCtx semantic)
    (extendedWF : (MLCtx.vlam ⟨state.ngen.curr⟩ name domain semantic binder context.mlctx).WF
      venv context.lparams) :
    (context.withMLC _ extendedWF).StateWF { state with ngen := state.ngen.next } := by
  have extendedScopeWF := extendedWF.tr.wf
  have allocated := state.ngen.next_reserves_self
  have fresh := state.ngen.not_reserves_self
  have increase : state.ngen ≤ state.ngen.next := .next
  have inference {cache} (correct : context.InferCacheWF state cache) :
      (context.withMLC _ extendedWF).InferCacheWF { state with ngen := state.ngen.next } cache := by
    intro expression type lookup
    simp only [withMLC, MLCtx.vlctx, context.scope_eq] at ⊢
    exact ((correct lookup).fresh context.checker.wf.ordered
      (by simpa only [MLCtx.vlctx, context.scope_eq] using extendedScopeWF)).mono increase
  have normalization {cache} (correct : context.WHNFCacheWF state cache) :
      (context.withMLC _ extendedWF).WHNFCacheWF { state with ngen := state.ngen.next } cache := by
    intro expression result lookup
    simp only [withMLC, MLCtx.vlctx, context.scope_eq] at ⊢
    exact ((correct lookup).fresh context.checker.wf
      (by simpa only [MLCtx.vlctx, context.scope_eq] using extendedScopeWF)).mono increase
  refine ⟨?_, ?_, inference stateWF.inferI, inference stateWF.inferC,
    normalization stateWF.whnfCore, normalization stateWF.whnf, stateWF.unfold⟩
  · intro identifier member
    simp only [withMLC, MLCtx.vlctx, VLCtx.fvars_cons_some] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact allocated
    · exact (stateWF.reserved _ (context.scope_eq ▸ member)).mono increase
  · obtain ⟨scope, shift, scopeWF, inserted, equivalent, reserved⟩ := stateWF.equivalence
    have domainScope := domainTr.fvarsList
    have typed : VLocalDecl.WF venv context.lparams.length scope.toCtx
        (.vlam (semantic.lift' shift)) := domainType.weak' context.checker.wf.ordered inserted.toCtx
    have nextScopeWF : VLCtx.WF venv context.lparams.length
        ((some (⟨state.ngen.curr⟩, domain.fvarsList), .vlam (semantic.lift' shift)) :: scope) := by
      refine ⟨scopeWF, ?_, typed⟩
      intro identifier dependencies same
      cases same
      exact ⟨fun member => fresh (reserved _ member), domainScope.trans inserted.fvars_sublist.subset⟩
    refine ⟨_, shift.consN 1, nextScopeWF, ?_,
      equivalent.weak' context.checker.wf (.skip_fvar _ _ .refl) nextScopeWF, ?_⟩
    · simpa only [withMLC, MLCtx.vlctx, context.scope_eq] using inserted.cons_fvar _ _ domainScope
    · intro identifier member
      rcases List.mem_cons.mp member with rfl | member
      · exact allocated
      · exact (reserved _ member).mono increase

theorem StateWF.restoreLambda {context : RestrictedContext safety env venv}
    (extendedWF : (MLCtx.vlam identifier name domain semantic binder context.mlctx).WF venv context.lparams)
    (stateWF : (context.withMLC _ extendedWF).StateWF state) : context.StateWF state := by
  have extendedScopeWF := extendedWF.tr.wf
  have inference {cache} (correct : (context.withMLC _ extendedWF).InferCacheWF state cache) :
      context.InferCacheWF state cache := by
    intro expression type lookup
    have typed := correct lookup
    simp only [withMLC, MLCtx.vlctx, context.scope_eq] at typed
    exact typed.weakN_inv context.checker.wf
      (by simpa only [MLCtx.vlctx, context.scope_eq] using extendedScopeWF)
  have normalization {cache} (correct : (context.withMLC _ extendedWF).WHNFCacheWF state cache) :
      context.WHNFCacheWF state cache := by
    intro expression result lookup
    have normalized := correct lookup
    simp only [withMLC, MLCtx.vlctx, context.scope_eq] at normalized
    exact normalized.weakN_inv context.checker.wf
      (by simpa only [MLCtx.vlctx, context.scope_eq] using extendedScopeWF)
  refine ⟨?_, ?_, inference stateWF.inferI, inference stateWF.inferC,
    normalization stateWF.whnfCore, normalization stateWF.whnf, stateWF.unfold⟩
  · intro identifier member
    exact stateWF.reserved _ (by simpa only [withMLC, MLCtx.vlctx, context.scope_eq, VLCtx.fvars_cons_some]
      using (List.mem_cons_of_mem _ member))
  · obtain ⟨scope, shift, scopeWF, inserted, equivalent, reserved⟩ := stateWF.equivalence
    exact ⟨scope, _, scopeWF, .comp (.skip_fvar _ _ .refl) (by
      simpa only [withMLC, MLCtx.vlctx, context.scope_eq] using inserted), equivalent, reserved⟩

theorem inferFVar (context : RestrictedContext safety env venv) :
    (Inner.inferFVar context.toContext identifier).WF fun result =>
      ∃ semantic type, TrTyping venv context.lparams context.scope (.fvar identifier) result semantic type := by
  simp [Inner.inferFVar, toContext]
  split
  · refine .pure ?_
    rename_i declaration lookup
    rw [context.trScope.1.find?_eq_find?_toList] at lookup
    have same := List.find?_some lookup
    simp at same
    subst same
    obtain ⟨semantic, type, semanticLookup, _, below, _, typeTr⟩ :=
      context.trScope.find?_of_mem context.checker.wf (List.mem_of_find?_eq_some lookup)
    exact ⟨semantic, type, below, .fvar semanticLookup, typeTr,
      context.scope_wf.find?_wf context.checker.wf semanticLookup⟩
  · exact .throw

theorem RunWF.withLocalDecl {context : RestrictedContext safety env venv}
    {methods : Methods} {continuation : Expr → RecM Result} {post : Result → Prop}
    (domainTr : TrExprS venv context.lparams context.scope domain semantic)
    (domainType : venv.IsType context.lparams.length context.scope.toCtx semantic)
    (continuationWF : ∀ identifier, ∀ extendedWF :
      (MLCtx.vlam identifier name domain semantic binder context.mlctx).WF venv context.lparams,
      (context.withMLC _ extendedWF).RunWF methods (context.withMLC _ extendedWF).StateWF
        (continuation (.fvar identifier)) post) :
    context.RunWF methods context.StateWF (withLocalDecl name binder domain continuation) post := by
  intro initial initialWF returned success
  have absent := initialWF.find?_eq_none initial.ngen.not_reserves_self
  have extendedWF : (MLCtx.vlam ⟨initial.ngen.curr⟩ name domain semantic binder context.mlctx).WF
      venv context.lparams :=
    ⟨context.mlctx_wf, absent, context.scope_eq ▸ domainTr, context.scope_eq ▸ domainType⟩
  obtain ⟨finalWF, finalPost⟩ := continuationWF ⟨initial.ngen.curr⟩ extendedWF
    { initial with ngen := initial.ngen.next } (initialWF.freshLambda domainTr domainType extendedWF)
    returned success
  exact ⟨finalWF.restoreLambda extendedWF, finalPost⟩

end RestrictedContext
end Lean4Lean
