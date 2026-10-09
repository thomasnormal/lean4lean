import Lean4Lean.Verify.ConstructorParams

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

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

end Lean4Lean.AddInductive
