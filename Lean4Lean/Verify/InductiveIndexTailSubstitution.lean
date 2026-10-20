import Lean4Lean.Verify.InductiveIndexDomainCorrespondence

namespace Lean.Expr

/-- Remove the outer argument before the inner arguments. Closed replacements
cannot acquire or capture any of the intervening binder variables. -/
theorem instantiateMany_append_last (expression replacement : Expr) (remaining : List Expr)
    (depth : Nat) (closed : replacement.looseBVarRange' = 0) :
    expression.instantiateMany (remaining ++ [replacement]) depth =
      (expression.instantiate1' replacement (depth + remaining.length)).instantiateMany remaining depth := by
  induction expression generalizing depth <;> simp_all only [instantiateMany, instantiate1', Nat.add_right_comm]
  rename_i index
  by_cases inner : index < depth
  · have outer : index < depth + remaining.length := by omega
    simp [inner, outer, instantiateMany]
  · by_cases before : index < depth + remaining.length
    · have bound : index - depth < remaining.length := by omega
      simp [inner, before, instantiateMany, List.getElem?_append_left bound,
        List.getElem?_eq_getElem bound]
    · by_cases selected : index = depth + remaining.length
      · subst index
        simp only [Nat.lt_irrefl, if_false, if_true]
        rw [liftLooseBVars_eq_self (by omega), instantiateMany_eq_self _ _ _ (by omega)]
        simp only [inner, if_false, Nat.add_sub_cancel_left,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
        exact liftLooseBVars_eq_self (by omega)
      · have lower : ¬ index - 1 < depth := by omega
        have beyond : remaining.length ≤ index - depth := by omega
        have missing : remaining[index - 1 - depth]? = none := by
          apply List.getElem?_eq_none_iff.mpr
          omega
        have missingLast : ([replacement] : List Expr)[index - depth - remaining.length]? = none := by
          apply List.getElem?_eq_none_iff.mpr
          simp only [List.length_singleton]
          omega
        simp only [inner, before, selected, if_false, instantiateMany, lower, missing,
          List.getElem?_append_right beyond, missingLast, List.length_append, List.length_singleton]
        congr 1
        omega

end Lean.Expr

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

/-- The body below exactly `count` native Pi binders, retaining its bound
variables. It records no argument typing or endpoint equality. -/
inductive NativeForallTail : Expr → Nat → Expr → Prop where
  | nil : NativeForallTail body 0 body
  | cons (tail : NativeForallTail body count terminal) :
      NativeForallTail (.forallE name domain body binder) (count + 1) terminal

theorem NativeForallTail.abstract1
    (tail : NativeForallTail source count terminal) (identifier : FVarId) (depth : Nat) :
    NativeForallTail (source.abstract1 identifier depth) count
      (terminal.abstract1 identifier (depth + count)) := by
  induction tail generalizing depth with
  | nil => exact .nil
  | cons _ induction => simpa only [Expr.abstract1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      NativeForallTail.cons (induction (depth + 1))

theorem NativeForallTail.instantiate1'
    (tail : NativeForallTail source count terminal) (argument : Expr) (depth : Nat) :
    NativeForallTail (source.instantiate1' argument depth) count
      (terminal.instantiate1' argument (depth + count)) := by
  induction tail generalizing depth with
  | nil => exact .nil
  | cons _ induction => simpa only [Expr.instantiate1', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      NativeForallTail.cons (induction (depth + 1))

/-- Recover the actual terminal after dependent argument application. -/
theorem NativeTelescopeArguments.terminalOfTail
    (arguments : NativeTelescopeArguments env universes model source replacements actualTerminal)
    (tail : NativeForallTail source replacements.length body)
    (closed : ∀ replacement ∈ replacements, replacement.looseBVarRange' = 0) :
    actualTerminal = body.instantiateMany replacements.reverse := by
  induction arguments generalizing body with
  | nil => cases tail; simp
  | @cons name domain source argument binder replacements terminal domainSemantic argumentSemantic
      domainTranslated argumentTranslated argumentTyped remaining induction =>
    cases tail with
    | cons tail =>
      have tail' := tail.instantiate1' argument 0
      have equation := induction tail' (fun selected member => closed selected (by simp [member]))
      rw [List.reverse_cons, Expr.instantiateMany_append_last _ _ _ _ (closed argument (by simp))]
      simpa only [Nat.zero_add, List.length_reverse] using equation

/-- Native abstraction closes the body under all selected Pi declarations. -/
theorem mkForall_selected_tail {lctx : LocalContext} {body : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope) (closed : body.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    NativeForallTail (lctx.mkForall (ids.map Expr.fvar).toArray body) ids.length
      (body.abstractList ids) := by
  rw [mkForall_selected_fold ids scope closed distinct bindings]
  induction ids with
  | nil => exact .nil
  | cons identifier ids induction =>
    obtain ⟨index, name, domain, binder, kind, lookup⟩ := bindings identifier (by simp)
    have inner := induction distinct.tail
      (bindings.subset (fun selected member => List.mem_cons_of_mem identifier member))
    have abstracted := inner.abstract1 identifier 0
    simp only [List.foldr_cons, LocalContext.mkBindingList1, lookup,
      Bool.false_eq_true, if_false, Expr.abstractList, List.length_cons]
    apply NativeForallTail.cons
    have equation := Expr.abstract1_abstractList' (e := body) (k := 0) distinct
    rw [Nat.zero_add] at abstracted equation
    rw [← equation]
    exact abstracted

end Lean4Lean.AddInductive
