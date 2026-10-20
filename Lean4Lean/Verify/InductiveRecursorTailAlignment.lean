import Lean4Lean.Verify.InductiveIndexTailSubstitution

namespace Lean.Expr

theorem abstractFVarIndex_eq_none_iff {identifier : FVarId} {ids : List FVarId} :
    abstractFVarIndex identifier ids = none ↔ identifier ∉ ids := by
  induction ids with
  | nil => simp [abstractFVarIndex]
  | cons head ids induction =>
    simp only [abstractFVarIndex]
    cases found : abstractFVarIndex identifier ids with
    | none =>
      have absent := induction.mp found
      by_cases equal : head = identifier
      · subst head; simp only [beq_self_eq_true, if_true, reduceCtorEq, List.mem_cons_self, not_true_eq_false]
      · have reverse : identifier ≠ head := Ne.symm equal
        simp only [beq_eq_false_iff_ne.mpr equal, Bool.false_eq_true, if_false,
          List.mem_cons, reverse, false_or, absent, not_false_eq_true]
    | some index =>
      have member : identifier ∈ ids := by
        by_contra absent
        rw [induction.mpr absent] at found
        cases found
      simp [member]

theorem abstractFVarIndex_getElem {ids : List FVarId} (distinct : ids.Nodup)
    (position : Nat) (bound : position < ids.length) :
    abstractFVarIndex ids[position] ids = some (ids.length - 1 - position) := by
  induction ids generalizing position with
  | nil => simp at bound
  | cons head ids induction =>
    cases position with
    | zero =>
      simp only [List.getElem_cons_zero, abstractFVarIndex,
        abstractFVarIndex_eq_none_iff.mpr (List.nodup_cons.mp distinct).1]
      simp
    | succ position =>
      have next := induction distinct.tail position (by simpa using bound)
      simp only [List.getElem_cons_succ, abstractFVarIndex, next]
      simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_sub, Nat.add_comm]

/-- Simultaneous replacement of selected free variables, represented by the
same native abstraction and bound-variable substitution used by telescopes. -/
def instantiateSelected (expression : Expr) (ids : List FVarId) (arguments : List Expr)
    (depth : Nat := 0) : Expr :=
  (expression.abstractFVars ids depth).instantiateMany arguments.reverse depth

theorem abstractFVars_eq_self_of_disjoint (expression : Expr) (ids : List FVarId) (depth : Nat)
    (disjoint : ∀ identifier ∈ expression.fvarsList, identifier ∉ ids) :
    expression.abstractFVars ids depth = expression := by
  induction expression generalizing depth <;>
    simp_all [fvarsList, abstractFVars]
  exact abstractFVarIndex_eq_none_iff.mpr disjoint ▸ rfl

theorem instantiateSelected_eq_self (expression : Expr) (ids : List FVarId) (arguments : List Expr)
    (depth : Nat) (closed : expression.looseBVarRange' ≤ depth)
    (disjoint : ∀ identifier ∈ expression.fvarsList, identifier ∉ ids) :
    expression.instantiateSelected ids arguments depth = expression := by
  rw [instantiateSelected, abstractFVars_eq_self_of_disjoint expression ids depth disjoint,
    instantiateMany_eq_self _ _ _ closed]

theorem instantiateSelected_fvar {ids : List FVarId} {arguments : List Expr}
    (distinct : ids.Nodup) (arity : arguments.length = ids.length)
    (closed : ∀ argument ∈ arguments, argument.looseBVarRange' = 0)
    (position : Nat) (bound : position < ids.length) (depth : Nat) :
    (Expr.fvar ids[position]).instantiateSelected ids arguments depth =
      arguments[position]'(by omega) := by
  have reversedBound : ids.length - 1 - position < arguments.length := by omega
  have reversedPosition : arguments.length - 1 - (ids.length - 1 - position) = position := by omega
  have lookup : arguments.reverse[ids.length - 1 - position]? = some arguments[position] := by
    rw [List.getElem?_reverse reversedBound, reversedPosition, List.getElem?_eq_getElem (by omega)]
  simp only [instantiateSelected, abstractFVars, abstractFVarIndex_getElem distinct position bound,
    instantiateMany, Nat.not_lt.mpr (Nat.le_add_right _ _), if_false, Nat.add_sub_cancel_left, lookup]
  exact liftLooseBVars_eq_self (by have := closed arguments[position] (List.getElem_mem (by omega)); omega)

theorem instantiateSelected_mkAppList (head : Expr) (values : List Expr)
    (ids : List FVarId) (arguments : List Expr) (depth : Nat) :
    (head.mkAppList values).instantiateSelected ids arguments depth =
      (head.instantiateSelected ids arguments depth).mkAppList
        (values.map (fun value => value.instantiateSelected ids arguments depth)) := by
  induction values generalizing head with
  | nil => rfl
  | cons value values induction =>
    simpa only [mkAppList, List.map_cons, instantiateSelected, abstractFVars, instantiateMany] using
      induction (.app head value)

theorem instantiateSelected_fvarApplication (head : Expr) (ids : List FVarId) (arguments : List Expr)
    (distinct : ids.Nodup) (arity : arguments.length = ids.length)
    (closed : ∀ argument ∈ arguments, argument.looseBVarRange' = 0)
    (headClosed : head.looseBVarRange' = 0)
    (disjoint : ∀ identifier ∈ head.fvarsList, identifier ∉ ids) (depth : Nat) :
    (head.mkAppList (ids.map Expr.fvar)).instantiateSelected ids arguments depth =
      head.mkAppList arguments := by
  rw [instantiateSelected_mkAppList, instantiateSelected_eq_self _ _ _ _ (by omega) disjoint]
  congr 1
  apply List.ext_getElem (by simpa using arity.symm)
  intro position leftBound rightBound
  simp only [List.getElem_map]
  exact instantiateSelected_fvar distinct arity closed position (by simpa using leftBound) depth

theorem abstract1_eq_self_of_scope (expression : Expr) (identifier : FVarId) (depth : Nat)
    (closed : expression.looseBVarRange' ≤ depth) (fresh : identifier ∉ expression.fvarsList) :
    expression.abstract1 identifier depth = expression := by
  induction expression generalizing depth <;>
    simp_all [abstract1, looseBVarRange', fvarsList, Nat.max_le]
  omega

theorem mkAppList_closed (head : Expr) (arguments : List Expr)
    (closed : head.looseBVarRange' = 0)
    (argumentClosed : ∀ argument ∈ arguments, argument.looseBVarRange' = 0) :
    (head.mkAppList arguments).looseBVarRange' = 0 := by
  induction arguments generalizing head with
  | nil => exact closed
  | cons argument arguments induction =>
    apply induction
    · simp [looseBVarRange', closed, argumentClosed argument (by simp)]
    · intro selected member; exact argumentClosed selected (by simp [member])

theorem mkAppList_fvars_absent (head : Expr) (arguments : List Expr) (identifier : FVarId)
    (fresh : identifier ∉ head.fvarsList)
    (argumentFresh : ∀ argument ∈ arguments, identifier ∉ argument.fvarsList) :
    identifier ∉ (head.mkAppList arguments).fvarsList := by
  induction arguments generalizing head with
  | nil => exact fresh
  | cons argument arguments induction =>
    apply induction
    · simpa only [fvarsList, List.mem_append, not_or] using
        And.intro fresh (argumentFresh argument (by simp))
    · intro selected member; exact argumentFresh selected (by simp [member])

end Lean.Expr

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

/-- The selected major binder, before closing the index declarations. -/
theorem recursorMajorTail_eq {full : LocalContext} (scope : full.BindingScope)
    (major : FVarId) (index : Nat) (name : Name) (domain : Expr) (binder : BinderInfo) (kind : LocalDeclKind)
    (lookup : full.find? major = some (.cdecl index major name domain binder kind))
    (motive : Expr) (indices : List FVarId)
    (closed : motive.looseBVarRange' = 0)
    (fresh : major ∉ motive.fvarsList) (different : major ∉ indices) :
    full.mkForall #[.fvar major] (.app (motive.mkAppList (indices.map Expr.fvar)) (.fvar major)) =
      .forallE name domain (.app (motive.mkAppList (indices.map Expr.fvar)) (.bvar 0)) binder := by
  have appClosed := Expr.mkAppList_closed motive (indices.map Expr.fvar) closed (by
    intro value member
    obtain ⟨identifier, _, rfl⟩ := List.mem_map.mp member
    rfl)
  have appFresh := Expr.mkAppList_fvars_absent motive (indices.map Expr.fvar) major fresh (by
    intro value member
    obtain ⟨identifier, idMember, rfl⟩ := List.mem_map.mp member
    simpa [Expr.fvarsList] using (show major ≠ identifier from fun equality => different (equality ▸ idMember)))
  have bodyClosed : (Expr.app (motive.mkAppList (indices.map Expr.fvar)) (.fvar major)).looseBVarRange' = 0 := by
    simp [Expr.looseBVarRange', appClosed]
  have bindings : SelectedCDeclBindings full [major] := by
    intro identifier member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨index, name, domain, binder, kind, lookup⟩
  change full.mkForall ([major].map Expr.fvar).toArray _ = _
  rw [mkForall_selected_fold [major] scope bodyClosed (by simp) bindings]
  simp only [List.foldr_cons, List.foldr_nil, LocalContext.mkBindingList1, lookup,
    Expr.abstractList, Bool.false_eq_true, if_false, Expr.abstract1, beq_self_eq_true, if_true]
  rw [Expr.abstract1_eq_self_of_scope _ _ _ (Nat.le_of_eq appClosed) appFresh]

/-- Substituting the selected indices into the actual major/motive tail is
simultaneous, so changed arguments may themselves mention selected identifiers. -/
theorem recursorMajorTail_substitution {full : LocalContext} (scope : full.BindingScope)
    (major : FVarId) (index : Nat) (name : Name) (binder : BinderInfo) (kind : LocalDeclKind)
    (head motive : Expr) (ids : List FVarId) (arguments : List Expr)
    (lookup : full.find? major = some (.cdecl index major name
      (head.mkAppList (ids.map Expr.fvar)) binder kind))
    (distinct : ids.Nodup) (arity : arguments.length = ids.length)
    (closed : ∀ argument ∈ arguments, argument.looseBVarRange' = 0)
    (headClosed : head.looseBVarRange' = 0) (motiveClosed : motive.looseBVarRange' = 0)
    (headDisjoint : ∀ identifier ∈ head.fvarsList, identifier ∉ ids)
    (motiveDisjoint : ∀ identifier ∈ motive.fvarsList, identifier ∉ ids)
    (majorFresh : major ∉ motive.fvarsList) (majorDifferent : major ∉ ids) :
    (full.mkForall #[.fvar major] (.app (motive.mkAppList (ids.map Expr.fvar)) (.fvar major))).instantiateSelected
        ids arguments =
      .forallE name (head.mkAppList arguments)
        (.app ((motive.mkAppList arguments).liftLooseBVars' 0 1) (.bvar 0)) binder := by
  rw [recursorMajorTail_eq scope major index name _ binder kind lookup motive ids motiveClosed majorFresh majorDifferent]
  change Expr.forallE name
    ((head.mkAppList (ids.map Expr.fvar)).instantiateSelected ids arguments 0)
    (.app ((motive.mkAppList (ids.map Expr.fvar)).instantiateSelected ids arguments 1) (.bvar 0)) binder = _
  rw [Expr.instantiateSelected_fvarApplication head ids arguments distinct arity closed headClosed headDisjoint 0,
    Expr.instantiateSelected_fvarApplication motive ids arguments distinct arity closed motiveClosed motiveDisjoint 1,
    Expr.liftLooseBVars_eq_self (Nat.le_of_eq (Expr.mkAppList_closed motive arguments motiveClosed closed))]

/-- Identify the terminal of already recovered argument support by actual
native selected binding and simultaneous substitution. -/
theorem NativeTelescopeArguments.terminalOfSelected
    {full : LocalContext} {body : Expr} {ids : List FVarId}
    (arguments : NativeTelescopeArguments env universes model
      (full.mkForall (ids.map Expr.fvar).toArray body) replacements actualTerminal)
    (scope : full.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings full ids)
    (arity : replacements.length = ids.length)
    (closed : ∀ replacement ∈ replacements, replacement.looseBVarRange' = 0) :
    actualTerminal = body.instantiateSelected ids replacements := by
  have tail := mkForall_selected_tail ids scope bodyClosed distinct bindings
  rw [← arity] at tail
  have equation := arguments.terminalOfTail tail closed
  rw [Expr.instantiateSelected, Expr.abstractFVars_eq_abstractList (by omega) distinct]
  exact equation

end Lean4Lean.AddInductive
