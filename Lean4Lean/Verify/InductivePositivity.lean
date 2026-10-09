import Lean4Lean.Verify.ConstructorParams

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.forIn'_all Lean4Lean.AddInductive.bindInvariantWF
  from Lean4Lean.Verify.ConstructorParams

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
    lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name (peelTypeAnnotations domain) bi }

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

def InductiveStats.SafeConstructorTraces (stats : InductiveStats)
    (indTypes : Array InductiveType) (normalizes : Context → Expr → Expr → Prop)
    (ctx : Context) : Prop :=
  ∀ parent, ∀ hparent : parent < indTypes.size, ∀ ctor ∈ indTypes[parent].ctors,
    ∃ terminal, SafeConstructorTrace stats normalizes parent ctx 0 ctor.type terminal

theorem InductiveStats.SafeConstructorTraces.spine {stats : InductiveStats}
    {indTypes : Array InductiveType} {normalizes : Context → Expr → Expr → Prop}
    {ctx : Context} (htraces : stats.SafeConstructorTraces indTypes normalizes ctx) :
    ∀ parent, ∀ hparent : parent < indTypes.size, ∀ ctor ∈ indTypes[parent].ctors,
      ∃ terminal, ConstructorSpine ctor.type terminal ∧
        isValidIndAppIdx stats terminal parent = true := by
  intro parent hparent ctor hctor
  obtain ⟨terminal, htrace⟩ := htraces parent hparent ctor hctor
  exact ⟨terminal, htrace.spine⟩

theorem checkConstructors.safeTraces_of_whnf (indTypes : Array InductiveType)
    (stats : InductiveStats) (normalizes : Context → Expr → Expr → Prop) (ctx : Context)
    (hwhnf : ∀ current source,
      ((monadLift (TypeChecker.whnf source) : M Expr) current).WF
        (normalizes current source)) :
    (checkConstructors indTypes stats false ctx).WF fun _ =>
      stats.SafeConstructorTraces indTypes normalizes ctx := by
  unfold checkConstructors
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro env
  refine Lean4Lean.AddInductive.bindInvariantWF (ctx := ctx)
    (post := fun _ => stats.SafeConstructorTraces indTypes normalizes ctx)
    (invariant := fun _ =>
      ∀ parent ∈ List.range' 0 indTypes.size, ∀ hparent : parent < indTypes.size,
        ∀ ctor ∈ indTypes[parent].ctors,
          ∃ terminal, SafeConstructorTrace stats normalizes parent ctx 0 ctor.type terminal)
    ?_ ?_
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply Lean4Lean.AddInductive.forIn'_all
    intro parent hparent state
    have hbound : parent < indTypes.size := by simpa using hparent
    refine Lean4Lean.AddInductive.bindInvariantWF (ctx := ctx)
      (post := fun (result : ForInStep Unit) => ∃ next, result = .yield next ∧
        ∀ hparent : parent < indTypes.size, ∀ ctor ∈ indTypes[parent].ctors,
          ∃ terminal, SafeConstructorTrace stats normalizes parent ctx 0 ctor.type terminal)
      (invariant := fun _ => ∀ ctor ∈ indTypes[parent].ctors,
        ∃ terminal, SafeConstructorTrace stats normalizes parent ctx 0 ctor.type terminal)
      ?_ ?_
    · change (forIn' (m := M) _ _ _ ctx).WF _
      apply Lean4Lean.AddInductive.forIn'_all
      intro ctor _ found
      dsimp only
      split
      · exact Except.WF.throw
      · simp only [pure_bind]
        apply Lean4Lean.AddInductive.bindWF
        intro _
        apply Lean4Lean.AddInductive.bindWF
        intro checkedType
        exact (checkConstructors.loop.safeTrace_of_whnf stats normalizes parent ctor.name
          ctor.type 0 ctx.fuel.inductiveFuel ctx hwhnf).bind fun _ htrace =>
            .pure ⟨_, rfl, htrace⟩
    · intro _ hctors
      exact .pure ⟨_, rfl, fun _ => hctors⟩
  · intro _ hall
    exact .pure fun parent hparent ctor hctor =>
      hall parent (by simp; omega) hparent ctor hctor

theorem checkConstructors.safeTraces (indTypes : Array InductiveType)
    (stats : InductiveStats) (ctx : Context) :
    (checkConstructors indTypes stats false ctx).WF fun _ =>
      stats.SafeConstructorTraces indTypes PositivityWHNF ctx :=
  checkConstructors.safeTraces_of_whnf indTypes stats PositivityWHNF ctx
    fun _ _ _ hresult => hresult

def InductiveStats.RegisteredSafeConstructorTraces (stats : InductiveStats)
    (nparams : Nat) (indTypes : Array InductiveType) (original root : Context) : Prop :=
  stats.HeaderSizes indTypes.size ∧ stats.ParamsCount nparams indTypes.size ∧
    stats.ParamsAreFVars ∧ stats.params.toList.Nodup ∧
    original.HeaderFrame { root with env := original.env } ∧
    stats.SafeConstructorTraces indTypes PositivityWHNF root

theorem checkInductiveTypes.registeredSafeConstructors (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (next : InductiveStats → M α)
    (ctx : Context) (post : α → Prop)
    (hnext : ∀ (stats : InductiveStats) (current : Context) (headers : Kernel.Environment),
      stats.HeaderSizes indTypes.size → stats.ParamsCount nparams indTypes.size →
      stats.ParamsAreFVars → stats.params.toList.Nodup → ctx.HeaderFrame current →
      stats.SafeConstructorTraces indTypes PositivityWHNF { current with env := headers } →
      (next stats { current with env := headers }).WF post) :
    (checkInductiveTypes nparams indTypes (fun stats => do
      withEnv (← declareInductiveTypes stats nparams indTypes numNested false) do
        checkConstructors indTypes stats false
        next stats) ctx).WF post := by
  apply checkInductiveTypes.frameHeaderSizesParamsCountDistinct
  intro stats current hsizes hcount hfvars hnodup hframe
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro headers
  refine (checkConstructors.safeTraces indTypes stats { current with env := headers }).bind ?_
  intro _ htraces
  exact hnext stats current headers hsizes hcount hfvars hnodup hframe htraces

theorem checkInductiveTypes.getRegisteredSafeConstructorTraces (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (ctx : Context) :
    (checkInductiveTypes nparams indTypes (fun stats => do
      withEnv (← declareInductiveTypes stats nparams indTypes numNested false) do
        checkConstructors indTypes stats false
        return (stats, ← readThe Context)) ctx).WF fun result =>
      result.1.RegisteredSafeConstructorTraces nparams indTypes ctx result.2 := by
  apply checkInductiveTypes.registeredSafeConstructors
  intro stats current headers hsizes hcount hfvars hnodup hframe htraces
  exact .pure ⟨hsizes, hcount, hfvars, hnodup,
    ⟨rfl, hframe.lparams, hframe.safety, hframe.allowPrimitive, hframe.fuel⟩, htraces⟩

end Lean4Lean.AddInductive
