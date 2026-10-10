import Lean4Lean.Verify.InductiveRecursorTypeNative

namespace Lean.Expr

theorem instantiate1'_abstract1 (expression : Expr) (identifier : FVarId) (depth : Nat) :
    (expression.abstract1 identifier depth).instantiate1' (.fvar identifier) depth = expression := by
  induction expression generalizing depth with
  | bvar index =>
    by_cases inside : index < depth
    · simp [Expr.abstract1, Expr.instantiate1', inside]
    · have beyond : ¬ index + 1 < depth := by omega
      have different : ¬ index + 1 = depth := by omega
      simp [Expr.abstract1, Expr.instantiate1', inside, beyond, different]
  | fvar selected =>
    by_cases equal : identifier = selected
    · subst selected
      simp [Expr.abstract1, Expr.instantiate1', Expr.liftLooseBVars']
    · simp [Expr.abstract1, Expr.instantiate1', equal]
  | _ => simp_all [Expr.abstract1, Expr.instantiate1']

end Lean.Expr

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem mkForall_selected_cons {lctx : LocalContext} {body : Expr}
    (identifier : FVarId) (ids : List FVarId)
    (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (distinct : (identifier :: ids).Nodup) (bindings : SelectedCDeclBindings lctx (identifier :: ids))
    (index : Nat) (name : Name) (domain : Expr) (binder : BinderInfo) (kind : LocalDeclKind)
    (lookup : lctx.find? identifier = some (.cdecl index identifier name domain binder kind)) :
    lctx.mkForall ((identifier :: ids).map Expr.fvar).toArray body =
      .forallE name domain ((lctx.mkForall (ids.map Expr.fvar).toArray body).abstract1 identifier) binder := by
  have tailBindings := bindings.subset
    (fun selected member => List.mem_cons_of_mem identifier member)
  rw [mkForall_selected_fold (identifier :: ids) scope bodyClosed distinct bindings,
    mkForall_selected_fold ids scope bodyClosed distinct.tail tailBindings]
  simp [List.foldr_cons, LocalContext.mkBindingList1, lookup]

end Lean4Lean.AddInductive
