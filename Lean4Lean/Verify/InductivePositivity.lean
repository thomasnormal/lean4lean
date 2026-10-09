import Lean4Lean.Verify.ConstructorParams

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats

private theorem scanSome_eq (items : List Nat) (valid : Nat → Bool) :
    (forIn (m := Option) items (⟨none, PUnit.unit⟩ : MProd (Option Nat) PUnit)
      fun index _ => if valid index then pure (ForInStep.done ⟨some index, PUnit.unit⟩)
        else pure (ForInStep.yield ⟨none, PUnit.unit⟩)) =
      some ⟨items.find? valid, PUnit.unit⟩ := by
  induction items with
  | nil => rfl
  | cons index items ih =>
    cases hvalid : valid index with
    | false => simpa [hvalid, Pure.pure, Bind.bind] using ih
    | true => simp [hvalid, Pure.pure, Bind.bind]

theorem isValidIndApp?.valid (stats : InductiveStats) (type : Expr) (parent : Nat)
    (hvalid : isValidIndApp? stats type = some parent) :
    parent < stats.indConsts.size ∧ isValidIndAppIdx stats type parent = true := by
  unfold isValidIndApp? at hvalid
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind] at hvalid
  rw [scanSome_eq] at hvalid
  dsimp only [Bind.bind, Pure.pure] at hvalid
  have hfound : (List.range' 0 stats.indConsts.size).find?
      (isValidIndAppIdx stats type) = some parent := by
    cases hfind : (List.range' 0 stats.indConsts.size).find?
        (isValidIndAppIdx stats type) with
    | none => simp [hfind] at hvalid
    | some actual => simpa [hfind] using hvalid
  exact ⟨by simpa using List.mem_of_find?_eq_some hfound, List.find?_some hfound⟩

def Context.withPositivityArg (ctx : Context) (name : Name) (domain : Expr)
    (bi : BinderInfo) : Context :=
  { ctx with
    ngen := ctx.ngen.next
    lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name domain.consumeTypeAnnotations bi }

inductive PositivityTrace (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) : Context → Expr → Prop where
  | absent {ctx : Context} {type normal : Expr}
      (hwhnf : normalizes ctx type normal)
      (habsent : hasIndOcc stats.indConsts normal = false) :
      PositivityTrace stats normalizes ctx type
  | inductiveApp {ctx : Context} {type normal : Expr} {parent : Nat}
      (hwhnf : normalizes ctx type normal)
      (hocc : hasIndOcc stats.indConsts normal = true)
      (hnotForall : normal.isForall = false)
      (hparent : parent < stats.indConsts.size)
      (hvalid : isValidIndAppIdx stats normal parent = true) :
      PositivityTrace stats normalizes ctx type
  | forallE {ctx : Context} {type : Expr} {name : Name} {domain body : Expr}
      {bi : BinderInfo}
      (hwhnf : normalizes ctx type (.forallE name domain body bi))
      (hocc : hasIndOcc stats.indConsts (.forallE name domain body bi) = true)
      (hdom : hasIndOcc stats.indConsts domain = false)
      (hbody : PositivityTrace stats normalizes (ctx.withPositivityArg name domain bi)
        (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩))) :
      PositivityTrace stats normalizes ctx type

theorem checkPositivity.loop.trace_of_whnf (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (ctor : Name) (index : Nat)
    (type : Expr) (fuel : Nat) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkPositivity.loop stats ctor index type fuel ctx).WF
      fun _ => PositivityTrace stats normalizes ctx type := by
  induction fuel generalizing type ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [checkPositivity.loop.eq_def]
    dsimp only
    refine (hwhnf ctx type).bind ?_
    intro normal hnormal
    cases hocc : hasIndOcc stats.indConsts normal with
    | false =>
      simp only [hocc, Bool.not_false, if_true]
      exact .pure (.absent hnormal hocc)
    | true =>
      simp only [hocc, Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
      cases normal with
      | forallE name domain body bi =>
        cases hdom : hasIndOcc stats.indConsts domain with
        | true =>
          simp only [hdom, if_true]
          exact Except.WF.throw
        | false =>
          simp only [hdom, Bool.false_eq_true, if_false]
          change (checkPositivity.loop stats ctor index
            (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) fuel
            (ctx.withPositivityArg name domain bi)).WF _
          exact (ih _ _).mono fun _ hbody => .forallE hnormal hocc hdom hbody
      | _ =>
        cases hvalid : isValidIndApp? stats _ with
        | none => exact Except.WF.throw
        | some parent =>
          have hparent := isValidIndApp?.valid stats _ parent hvalid
          exact .pure (.inductiveApp hnormal hocc rfl hparent.1 hparent.2)

def PositivityWHNF (ctx : Context) (type normal : Expr) : Prop :=
  (monadLift (TypeChecker.whnf type) : M Expr) ctx = .ok normal

theorem checkPositivity.trace_of_whnf (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (type : Expr)
    (ctor : Name) (index : Nat) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkPositivity stats type ctor index ctx).WF
      fun _ => PositivityTrace stats normalizes ctx type := by
  change (checkPositivity.loop stats ctor index type ctx.fuel.inductiveFuel ctx).WF _
  exact checkPositivity.loop.trace_of_whnf stats normalizes ctor index type
    ctx.fuel.inductiveFuel ctx hwhnf

theorem checkPositivity.trace (stats : InductiveStats) (type : Expr)
    (ctor : Name) (index : Nat) (ctx : Context) :
    (checkPositivity stats type ctor index ctx).WF
      fun _ => PositivityTrace stats PositivityWHNF ctx type := by
  exact checkPositivity.trace_of_whnf stats PositivityWHNF type ctor index ctx
    fun _ _ _ hresult => hresult

inductive SafeConstructorTrace (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (parent : Nat) :
    Context → Nat → Expr → Expr → Prop where
  | terminal {ctx : Context} {index : Nat} {type : Expr}
      (hnotForall : type.isForall = false)
      (hvalid : isValidIndAppIdx stats type parent = true) :
      SafeConstructorTrace stats normalizes parent ctx index type type
  | parameter {ctx : Context} {index : Nat} {name : Name} {domain body : Expr}
      {bi : BinderInfo} {param terminal : Expr}
      (hparam : stats.params[index]? = some param)
      (hbody : SafeConstructorTrace stats normalizes parent ctx (index + 1)
        (body.instantiate1 param) terminal) :
      SafeConstructorTrace stats normalizes parent ctx index
        (.forallE name domain body bi) terminal
  | field {ctx : Context} {index : Nat} {name : Name} {domain body : Expr}
      {bi : BinderInfo} {terminal : Expr}
      (hparam : stats.params[index]? = none)
      (hpositive : PositivityTrace stats normalizes ctx domain)
      (hbody : SafeConstructorTrace stats normalizes parent
        (ctx.withPositivityArg name domain bi) (index + 1)
        (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) terminal) :
      SafeConstructorTrace stats normalizes parent ctx index
        (.forallE name domain body bi) terminal

theorem SafeConstructorTrace.spine {stats : InductiveStats}
    {normalizes : Context → Expr → Expr → Prop} {parent index : Nat}
    {ctx : Context} {type terminal : Expr}
    (htrace : SafeConstructorTrace stats normalizes parent ctx index type terminal) :
    ConstructorSpine type terminal ∧ isValidIndAppIdx stats terminal parent = true := by
  induction htrace with
  | terminal hnotForall hvalid => exact ⟨.refl _, hvalid⟩
  | parameter hparam hbody ih => exact ⟨.forallE _ _ _ _ _ _ ih.1, ih.2⟩
  | field hparam hpositive hbody ih => exact ⟨.forallE _ _ _ _ _ _ ih.1, ih.2⟩

theorem checkConstructors.loop.safeTrace_of_whnf (stats : InductiveStats)
    (normalizes : Context → Expr → Expr → Prop) (parent : Nat) (ctor : Name)
    (type : Expr) (index fuel : Nat) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkConstructors.loop stats false parent ctor type index fuel ctx).WF
      fun _ => ∃ terminal, SafeConstructorTrace stats normalizes parent ctx index type terminal := by
  induction fuel generalizing type index ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    cases type with
    | forallE name domain body bi =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      cases hparam : stats.params[index]? with
      | some param =>
        apply Lean4Lean.AddInductive.bindWF
        intro paramType
        apply Lean4Lean.AddInductive.bindWF
        intro equal
        split
        · apply Lean4Lean.AddInductive.bindWF
          intro _
          refine (ih (body.instantiate1 param) (index + 1) ctx).mono ?_
          rintro _ ⟨terminal, htrace⟩
          exact ⟨terminal, .parameter hparam htrace⟩
        · exact Except.WF.throw
      | none =>
        apply Lean4Lean.AddInductive.bindWF
        intro sort
        split
        · refine (checkPositivity.trace_of_whnf stats normalizes domain ctor index ctx hwhnf).bind ?_
          intro _ hpositive
          change (checkConstructors.loop stats false parent ctor
            (body.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) (index + 1) fuel
            (ctx.withPositivityArg name domain bi)).WF _
          refine (ih _ _ _).mono ?_
          rintro _ ⟨terminal, htrace⟩
          exact ⟨terminal, .field hparam hpositive htrace⟩
        · exact Except.WF.throw
    | _ =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      split
      · exact Except.WF.throw
      · rename_i hvalid
        exact .pure ⟨_, .terminal rfl (by simpa using hvalid)⟩

theorem checkConstructors.loop.safeTrace (stats : InductiveStats) (parent : Nat)
    (ctor : Name) (type : Expr) (index fuel : Nat) (ctx : Context) :
    (checkConstructors.loop stats false parent ctor type index fuel ctx).WF
      fun _ => ∃ terminal, SafeConstructorTrace stats PositivityWHNF parent ctx index type terminal :=
  checkConstructors.loop.safeTrace_of_whnf stats PositivityWHNF parent ctor type index fuel ctx
    fun _ _ _ hresult => hresult

end Lean4Lean.AddInductive
