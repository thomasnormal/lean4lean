import Lean4Lean.Verify.InductiveIndexReconstruction

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

/-- Two native telescopes share this many domains. Their terminal expressions
may differ. The relation is preserved by actual dependent substitutions. -/
inductive NativeTelescopePrefix : Expr → Expr → Nat → Prop where
  | nil : NativeTelescopePrefix left right 0
  | cons (tail : NativeTelescopePrefix leftBody rightBody count) :
      NativeTelescopePrefix (.forallE leftName domain leftBody leftBinder)
        (.forallE rightName domain rightBody rightBinder) (count + 1)

theorem NativeTelescopePrefix.instantiate1'
    (shared : NativeTelescopePrefix left right count) (argument : Expr) (depth : Nat) :
    NativeTelescopePrefix (left.instantiate1' argument depth)
      (right.instantiate1' argument depth) count := by
  induction shared generalizing depth with
  | nil => exact .nil
  | cons _ induction => exact .cons (induction (depth + 1))

theorem NativeTelescopePrefix.abstract1
    (shared : NativeTelescopePrefix left right count) (identifier : FVarId) (depth : Nat) :
    NativeTelescopePrefix (left.abstract1 identifier depth) (right.abstract1 identifier depth) count := by
  induction shared generalizing depth with
  | nil => exact .nil
  | cons _ induction => exact .cons (induction (depth + 1))

/-- Domain correspondence after every supplied argument is substituted. -/
theorem NativeTelescopePrefix.domains
    (shared : NativeTelescopePrefix left right count) (arguments : List Expr)
    (arity : arguments.length = count) :
    ∃ leftEnd rightEnd, NativeTelescopeDomains left right arguments leftEnd rightEnd := by
  induction arguments generalizing left right count with
  | nil => cases arity; exact ⟨_, _, .nil⟩
  | cons argument arguments induction =>
    cases shared with
    | nil => simp at arity
    | cons tail =>
      obtain ⟨leftEnd, rightEnd, domains⟩ := induction
        (tail.instantiate1' argument 0) (by simpa using arity)
      exact ⟨leftEnd, rightEnd, .cons domains⟩

/-- Closing the same selected declarations gives identical index domains,
regardless of the two terminal bodies. No semantic index typing is assumed. -/
theorem mkForall_selected_prefix {lctx : LocalContext} {left right : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope)
    (leftClosed : left.looseBVarRange' = 0) (rightClosed : right.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    NativeTelescopePrefix (lctx.mkForall (ids.map Expr.fvar).toArray left)
      (lctx.mkForall (ids.map Expr.fvar).toArray right) ids.length := by
  rw [mkForall_selected_fold ids scope leftClosed distinct bindings,
    mkForall_selected_fold ids scope rightClosed distinct bindings]
  clear distinct
  induction ids with
  | nil => exact .nil
  | cons identifier ids induction =>
    obtain ⟨_, _, _, _, _, lookup⟩ := bindings identifier (by simp)
    have tail := induction (bindings.subset (fun selected member => List.mem_cons_of_mem identifier member))
    simpa only [List.foldr_cons, LocalContext.mkBindingList1, lookup,
      Bool.false_eq_true, if_false, Expr.abstractList, List.length_cons] using
      NativeTelescopePrefix.cons (tail.abstract1 identifier 0)

/-- The generated index telescope and the reconstructed family signature have
the same domains, including after changed dependent indices are substituted.
Only selected declaration agreement is required across the two contexts. -/
theorem mkForall_selected_domains {leftContext rightContext : LocalContext} {left right : Expr}
    (ids : List FVarId) (leftScope : leftContext.BindingScope) (rightScope : rightContext.BindingScope)
    (leftClosed : left.looseBVarRange' = 0) (rightClosed : right.looseBVarRange' = 0)
    (distinct : ids.Nodup) (agreement : SelectedCDeclBindingAgreement leftContext rightContext ids)
    (arguments : List Expr) (arity : arguments.length = ids.length) :
    ∃ leftEnd rightEnd,
      NativeTelescopeDomains (leftContext.mkForall (ids.map Expr.fvar).toArray left)
        (rightContext.mkForall (ids.map Expr.fvar).toArray right) arguments leftEnd rightEnd := by
  rw [mkForall_congr_selected_cdecl ids leftScope rightScope leftClosed distinct agreement]
  exact (mkForall_selected_prefix ids rightScope leftClosed rightClosed distinct agreement.right).domains
    arguments arity

/-- Recover changed dependent indices for the generated selected telescope.
The partial-family input is converted using the actual translated opening
trace. Domain correspondence follows from selected binding agreement, rather
than being supplied as a complete native correspondence premise. The terminal
major/motive shape is a separate obligation. -/
theorem UArgModelEndpoint.indexArgumentsFromSelectedTrace
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source sortTerminal terminal argument : Expr} {index finalIndex : Nat}
    {indices arguments : Array Expr} {reader indexReader fieldReader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr}
    {base initial final : TypeChecker.MLCtx}
    {trace : RecursorIndexTrace stats source index #[] reader sortTerminal finalIndex indices indexReader}
    {opening : RecursorUArgOpeningTrace argument fieldReader terminal arguments finalReader}
    (endpoint : UArgModelEndpoint env universes opening initial final)
    (input : FamilyIndexInput env universes base stats terminal source)
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (native : base.lctx = reader.lctx) (converted : base.vlctx = virtual)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (insertion : VLCtx.FVLift' base.vlctx final.vlctx 0 lift 0)
    (full : LocalContext) (fullScope : full.BindingScope)
    (agreement : SelectedCDeclBindingAgreement indexReader.lctx full (binderArrayIds indices))
    (tail : Expr) (tailClosed : tail.looseBVarRange' = 0)
    (arity : (getIIndices stats terminal).2.size = indices.size) :
    ∃ targetEnd,
      NativeTelescopeArguments env universes final (full.mkForall indices tail)
        (getIIndices stats terminal).2.toList targetEnd := by
  obtain ⟨indexModel, ids, indexWF, indexNative, indexVirtual, array, telescope, ⟨family⟩⟩ :=
    input.reconstruct history envWF baseWF native converted reserved
  simp only [List.nil_append] at array
  have selected := binderArrayIds_of_toList_eq array
  have actualArray : indices = (ids.map Expr.fvar).toArray := by
    rw [← array, Array.toArray_toList]
  have sourceClosed : sortTerminal.looseBVarRange' = 0 := by
    have translated := indexVirtual.symm ▸ history.finalTranslation.2
    exact (indexModel.noBV ▸ translated.closed).looseBVarRange_zero
  have sourceScope : indexReader.lctx.BindingScope := indexNative ▸ indexWF.bindingScope
  have count : (getIIndices stats terminal).2.toList.length = ids.length := by
    have length := congrArg List.length array
    simp only [Array.length_toList, List.length_map] at length ⊢
    omega
  obtain ⟨sourceEnd, targetEnd, domains⟩ := mkForall_selected_domains ids sourceScope fullScope
    sourceClosed tailClosed (telescope.distinct baseWF) (selected ▸ agreement)
    (getIIndices stats terminal).2.toList count
  exact ⟨targetEnd, by simpa only [actualArray] using
    endpoint.indexArguments envWF (family.weakFV envWF endpoint.context.1 insertion) domains⟩

end Lean4Lean.AddInductive
