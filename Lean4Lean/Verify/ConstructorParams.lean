import Lean4Lean.Verify.ConstructorArity
import Lean4Lean.Verify.Environment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.withLocalDeclWF from Lean4Lean.Verify.InductiveStats

private theorem scanFalse_eq (items : List α) (invalid : α → Bool) :
    (forIn (m := Id) items (⟨none, PUnit.unit⟩ : MProd (Option Bool) PUnit) fun item _ =>
      if invalid item then ForInStep.done ⟨some false, PUnit.unit⟩ else
        ForInStep.yield ⟨none, PUnit.unit⟩) =
      ⟨if items.any invalid then some false else none, PUnit.unit⟩ := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases hinvalid : invalid item <;>
      simp [hinvalid, ih, Pure.pure, Bind.bind]

theorem isValidIndAppIdx.parameterMatches (stats : InductiveStats) (type : Expr)
    (parent : Nat) (hvalid : isValidIndAppIdx stats type parent = true) :
    stats.params.size ≤ type.getAppArgs.size ∧
      ∀ index, index < stats.params.size →
        (stats.params[index]! == type.getAppArgs[index]!) = true := by
  simp only [isValidIndAppIdx, Expr.withApp_eq] at hvalid
  dsimp only [Id.run] at hvalid
  split at hvalid
  · rename_i hheader
    have hguards : (type.getAppFn == stats.indConsts[parent]!) = true ∧
        type.getAppArgs.size = stats.params.size + stats.nindices[parent]! := by
      simpa using hheader
    have hsize := hguards.2
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', pure_bind,
      Std.Legacy.Range.size] at hvalid
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hvalid
    dsimp only [Bind.bind, Pure.pure, Id.instMonad, Id.hasBind] at hvalid
    rw [scanFalse_eq (List.range' 0 stats.params.size)
      (fun index => stats.params[index]! != type.getAppArgs[index]!)] at hvalid
    dsimp only [MProd.fst] at hvalid
    by_cases hparams : (List.range' 0 stats.params.size).any
        (fun index => stats.params[index]! != type.getAppArgs[index]!) = true
    · simp [hparams] at hvalid
    ·
      refine ⟨by omega, ?_⟩
      intro index hindex
      have hmem : index ∈ List.range' 0 stats.params.size := by simp; omega
      have hmatch := List.any_eq_false.mp (by simpa using hparams) index hmem
      simpa [bne] using hmatch
  · simp at hvalid

theorem isValidIndAppIdx.indexNoIndOcc (stats : InductiveStats) (type : Expr)
    (parent : Nat) (hvalid : isValidIndAppIdx stats type parent = true) :
    ∀ index, stats.params.size ≤ index → index < type.getAppArgs.size →
      hasIndOcc stats.indConsts type.getAppArgs[index]! = false := by
  simp only [isValidIndAppIdx, Expr.withApp_eq] at hvalid
  dsimp only [Id.run] at hvalid
  split at hvalid
  · rename_i hheader
    have hguards : (type.getAppFn == stats.indConsts[parent]!) = true ∧
        type.getAppArgs.size = stats.params.size + stats.nindices[parent]! := by
      simpa using hheader
    have hsize := hguards.2
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', pure_bind,
      Std.Legacy.Range.size] at hvalid
    simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at hvalid
    dsimp only [Bind.bind, Pure.pure, Id.instMonad, Id.hasBind] at hvalid
    rw [scanFalse_eq (List.range' 0 stats.params.size)
      (fun index => stats.params[index]! != type.getAppArgs[index]!)] at hvalid
    dsimp only [MProd.fst] at hvalid
    by_cases hparams : (List.range' 0 stats.params.size).any
        (fun index => stats.params[index]! != type.getAppArgs[index]!) = true
    · simp [hparams] at hvalid
    · simp [hparams] at hvalid
      rw [scanFalse_eq (List.range' stats.params.size (type.getAppArgs.size - stats.params.size))
        (fun index => hasIndOcc stats.indConsts type.getAppArgs[index]!)] at hvalid
      dsimp only [MProd.fst] at hvalid
      by_cases hindices : (List.range' stats.params.size
          (type.getAppArgs.size - stats.params.size)).any
          (fun index => hasIndOcc stats.indConsts type.getAppArgs[index]!) = true
      · simp [hindices] at hvalid
      · simp [hindices] at hvalid
        intro index hbound hindex
        have hmem : index ∈ List.range' stats.params.size
            (type.getAppArgs.size - stats.params.size) := by
          simp
          omega
        have hnot := List.any_eq_false.mp (by simpa using hindices) index hmem
        simpa using hnot
  · simp at hvalid

private theorem eq_of_beq_fvar {type : Expr} {fvar : FVarId}
    (hmatch : (Expr.fvar fvar == type) = true) : type = .fvar fvar := by
  cases type with
  | fvar actual =>
    change (Expr.fvar fvar).eqv (.fvar actual) = true at hmatch
    rw [Expr.eqv_eq] at hmatch
    change (fvar == actual) = true at hmatch
    exact congrArg Expr.fvar (LawfulBEq.eq_of_beq hmatch).symm
  | _ => simp [(· == ·), Expr.eqv'] at hmatch

private theorem fvarsIn_appArg {predicate : FVarId → Prop} {type arg : Expr}
    (htype : FVarsIn predicate type) (harg : arg ∈ type.getAppArgs) :
    FVarsIn predicate arg := by
  have happ : FVarsIn predicate (type.getAppFn.mkAppList type.getAppArgsList) := by
    simpa only [Expr.mkAppList_getAppArgsList] using htype
  apply (FVarsIn.mkAppList.mp happ).2 arg
  simpa only [← Expr.getAppArgs_toList, Array.mem_toList_iff] using harg

theorem isValidIndAppIdx.parameterFVar (stats : InductiveStats) (type : Expr)
    (parent : Nat) (hvalid : isValidIndAppIdx stats type parent = true)
    (index : Nat) (hindex : index < stats.params.size) (fvar : FVarId)
    (hparam : stats.params[index] = .fvar fvar) :
    type.getAppArgs[index]! = .fvar fvar := by
  have hmatch := (parameterMatches stats type parent hvalid).2 index hindex
  simp only [getElem!_pos stats.params index hindex, hparam] at hmatch
  exact eq_of_beq_fvar hmatch

theorem isValidIndAppIdx.parameterFVarsIn (stats : InductiveStats) (type : Expr)
    (parent : Nat) (hvalid : isValidIndAppIdx stats type parent = true)
    (hfvars : stats.ParamsAreFVars) {predicate : FVarId → Prop}
    (htype : FVarsIn predicate type) (index : Nat) (hindex : index < stats.params.size) :
    FVarsIn predicate stats.params[index] := by
  have hargindex : index < type.getAppArgs.size :=
    Nat.lt_of_lt_of_le hindex (parameterMatches stats type parent hvalid).1
  have hparam := hfvars _ (Array.getElem_mem hindex)
  generalize heq : stats.params[index] = param at hparam ⊢
  cases param <;> simp [Expr.isFVar] at hparam
  rename_i fvar
  have harg := parameterFVar stats type parent hvalid index hindex fvar heq
  have hargtype := fvarsIn_appArg htype (Array.getElem_mem hargindex)
  simp only [getElem!_pos type.getAppArgs index hargindex] at harg
  simpa only [harg] using hargtype

def InductiveStats.RemainingParamsAbsent (stats : InductiveStats) (index : Nat)
    (type : Expr) : Prop :=
  ∀ paramIndex (hbound : paramIndex < stats.params.size), index ≤ paramIndex →
    FVarsIn (fun fvar => stats.params[paramIndex] ≠ .fvar fvar) type

theorem InductiveStats.RemainingParamsAbsent.of_noFVars {stats : InductiveStats}
    {type : Expr} (htype : FVarsIn (fun _ => False) type) (index : Nat) :
    stats.RemainingParamsAbsent index type :=
  fun _ _ _ => htype.mono fun _ hfalse => False.elim hfalse

theorem InductiveStats.RemainingParamsAbsent.mono {stats : InductiveStats}
    {type : Expr} {index next : Nat} (htype : stats.RemainingParamsAbsent index type)
    (hindex : index ≤ next) : stats.RemainingParamsAbsent next type :=
  fun _ hbound hnext => htype _ hbound (Nat.le_trans hindex hnext)

theorem InductiveStats.RemainingParamsAbsent.instantiate1 {stats : InductiveStats}
    {type arg : Expr} {index next : Nat} (htype : stats.RemainingParamsAbsent index type)
    (hindex : index ≤ next)
    (harg : ∀ paramIndex (hbound : paramIndex < stats.params.size), next ≤ paramIndex →
      FVarsIn (fun fvar => stats.params[paramIndex] ≠ .fvar fvar) arg) :
    stats.RemainingParamsAbsent next (type.instantiate1 arg) := by
  intro paramIndex hbound hnext
  rw [Expr.instantiate1_eq]
  exact (htype paramIndex hbound (Nat.le_trans hindex hnext)).instantiate1
    (harg paramIndex hbound hnext)

theorem InductiveStats.RemainingParamsAbsent.forallBody {stats : InductiveStats}
    {name : Name} {domain body : Expr} {bi : BinderInfo} {index : Nat}
    (htype : stats.RemainingParamsAbsent index (.forallE name domain body bi)) :
    stats.RemainingParamsAbsent index body :=
  fun paramIndex hbound hindex => (htype paramIndex hbound hindex).2

private theorem params_ne_of_nodup {stats : InductiveStats}
    (hnodup : stats.params.toList.Nodup) {first second : Nat}
    (hfirst : first < stats.params.size) (hsecond : second < stats.params.size)
    (hne : first ≠ second) : stats.params[first] ≠ stats.params[second] := by
  intro heq
  apply hne
  apply List.getElem?_inj (by simpa using hfirst) hnodup
  simp only [Array.getElem?_toList, Array.getElem?_eq_getElem hfirst,
    Array.getElem?_eq_getElem hsecond, heq]

theorem InductiveStats.RemainingParamsAbsent.consume_param {stats : InductiveStats}
    {name : Name} {domain body : Expr} {bi : BinderInfo} {index : Nat}
    (htype : stats.RemainingParamsAbsent index (.forallE name domain body bi))
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (hindex : index < stats.params.size) :
    stats.RemainingParamsAbsent (index + 1) (body.instantiate1 stats.params[index]) := by
  apply htype.forallBody.instantiate1 (Nat.le_succ _)
  intro paramIndex hbound hnext
  have hdifferent := params_ne_of_nodup hnodup hbound hindex (by omega)
  have hfvar := hfvars _ (Array.getElem_mem hindex)
  generalize heq : stats.params[index] = param at hfvar ⊢
  cases param <;> simp [Expr.isFVar] at hfvar
  simpa only [FVarsIn, heq] using hdifferent

theorem InductiveStats.RemainingParamsAbsent.validIndAppIdx {stats : InductiveStats}
    {type : Expr} {index parent : Nat} (htype : stats.RemainingParamsAbsent index type)
    (hfvars : stats.ParamsAreFVars) (hvalid : isValidIndAppIdx stats type parent = true) :
    stats.params.size ≤ index := by
  by_contra hbound
  have hindex : index < stats.params.size := by omega
  have hparam := isValidIndAppIdx.parameterFVarsIn stats type parent hvalid hfvars
    (htype index hindex (Nat.le_refl _)) index hindex
  have hfvar := hfvars _ (Array.getElem_mem hindex)
  generalize heq : stats.params[index] = param at hparam hfvar
  cases param <;> simp [Expr.isFVar, FVarsIn, ← heq] at hparam hfvar

inductive ConstructorSpine : Expr → Expr → Prop where
  | refl (type : Expr) : ConstructorSpine type type
  | forallE (name : Name) (domain body : Expr) (bi : BinderInfo)
      (arg terminal : Expr)
      (h : ConstructorSpine (body.instantiate1 arg) terminal) :
      ConstructorSpine (.forallE name domain body bi) terminal

theorem checkConstructors.loop_spine (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (ctor : Name) (type : Expr) (index fuel : Nat) (ctx : Context) :
    (checkConstructors.loop stats isUnsafe parent ctor type index fuel ctx).WF fun _ =>
      ∃ terminal, ConstructorSpine type terminal ∧
        isValidIndAppIdx stats terminal parent = true := by
  induction fuel generalizing isUnsafe type index ctx with
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
          refine (ih isUnsafe (body.instantiate1 param) (index + 1) ctx).mono ?_
          rintro _ ⟨terminal, hspine, hvalid⟩
          exact ⟨terminal, .forallE name domain body bi param terminal hspine, hvalid⟩
        · exact Except.WF.throw
      | none =>
        apply Lean4Lean.AddInductive.bindWF
        intro sort
        split
        · by_cases hunsafe : isUnsafe
          · simp [hunsafe]
            apply Lean4Lean.AddInductive.withLocalDeclWF
            intro arg ctx' hfvar harg hgen hframe
            refine (ih true (body.instantiate1' arg) (index + 1) ctx').mono ?_
            rintro _ ⟨terminal, hspine, hvalid⟩
            have hspine' : ConstructorSpine (body.instantiate1 arg) terminal := by
              rw [Expr.instantiate1_eq]
              exact hspine
            exact ⟨terminal, .forallE name domain body bi arg terminal hspine', hvalid⟩
          · simp [hunsafe]
            apply Lean4Lean.AddInductive.bindWF
            intro _
            apply Lean4Lean.AddInductive.withLocalDeclWF
            intro arg ctx' hfvar harg hgen hframe
            refine (ih false (body.instantiate1' arg) (index + 1) ctx').mono ?_
            rintro _ ⟨terminal, hspine, hvalid⟩
            have hspine' : ConstructorSpine (body.instantiate1 arg) terminal := by
              rw [Expr.instantiate1_eq]
              exact hspine
            exact ⟨terminal, .forallE name domain body bi arg terminal hspine', hvalid⟩
        · exact Except.WF.throw
    | _ =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      split
      · exact Except.WF.throw
      · rename_i hvalid
        intro _ _
        exact ⟨_, .refl _, by simpa using hvalid⟩

theorem checkConstructors.loop_arity (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (ctor : Name) (type : Expr) (index fuel : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (habsent : stats.RemainingParamsAbsent index type) :
    (checkConstructors.loop stats isUnsafe parent ctor type index fuel ctx).WF fun _ =>
      stats.params.size ≤ declareConstructors.arity index type := by
  induction fuel generalizing type index ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    cases type with
    | forallE name domain body bi =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      cases hparam : stats.params[index]? with
      | some param =>
        have hindex : index < stats.params.size := by
          by_contra hbound
          simp [Array.getElem?_eq_none (show stats.params.size ≤ index by omega)] at hparam
        have heq : stats.params[index] = param := by
          simpa only [Array.getElem?_eq_getElem hindex, Option.some.injEq] using hparam
        have hmem : param ∈ stats.params := heq ▸ Array.getElem_mem hindex
        have hnext := habsent.consume_param hfvars hnodup hindex
        rw [heq] at hnext
        apply Lean4Lean.AddInductive.bindWF
        intro paramType
        apply Lean4Lean.AddInductive.bindWF
        intro equal
        split
        · apply Lean4Lean.AddInductive.bindWF
          intro _
          refine (ih _ (index + 1) ctx hnext).mono ?_
          intro _ hbound
          rw [hfvars.arity_consume hmem name domain body bi index]
          exact hbound
        · exact Except.WF.throw
      | none =>
        have hindex : stats.params.size ≤ index := by
          simpa using ‹stats.params[index]? = none›
        intro _ _
        rw [declareConstructors.arity_eq_add]
        omega
    | _ =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      split
      · exact Except.WF.throw
      · rename_i hvalid
        intro _ _
        have hindex := habsent.validIndAppIdx hfvars (by simpa using hvalid)
        rw [declareConstructors.arity_eq_add]
        omega

theorem checkConstructors.loop_arity_of_noFVars (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (ctor : Name) (type : Expr) (fuel : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup)
    (htype : FVarsIn (fun _ => False) type) :
    (checkConstructors.loop stats isUnsafe parent ctor type 0 fuel ctx).WF fun _ =>
      stats.params.size ≤ declareConstructors.arity 0 type :=
  checkConstructors.loop_arity stats isUnsafe parent ctor type 0 fuel ctx hfvars hnodup
    (InductiveStats.RemainingParamsAbsent.of_noFVars htype 0)

theorem checkConstructors.checked_loop_arity (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (ctor : Name) (type : Expr) (fuel : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (hnodup : stats.params.toList.Nodup) :
    (ctx.env.checkNoMVarNoFVar ctor type >>= fun _ =>
      checkConstructors.loop stats isUnsafe parent ctor type 0 fuel ctx).WF fun _ =>
        stats.params.size ≤ declareConstructors.arity 0 type :=
  (Lean4Lean.checkNoMVarNoFVar.WF ctx.env ctor type).bind fun _ htype =>
    checkConstructors.loop_arity_of_noFVars stats isUnsafe parent ctor type fuel ctx
      hfvars hnodup htype

theorem checkInductiveTypes.checkedConstructorArity (nparams : Nat)
    (indTypes : Array InductiveType) (isUnsafe : Bool) (parent : Nat) (ctor : Name)
    (type : Expr) (ctx : Context) :
    (checkInductiveTypes nparams indTypes (fun stats current =>
      (current.env.checkNoMVarNoFVar ctor type >>= fun _ =>
        checkConstructors.loop stats isUnsafe parent ctor type 0
          current.fuel.inductiveFuel current) >>= fun _ => pure stats) ctx).WF fun stats =>
            stats.params.size ≤ declareConstructors.arity 0 type := by
  apply checkInductiveTypes.frameHeaderSizesParamsDistinct
  intro stats current _ hfvars hnodup _
  exact (checkConstructors.checked_loop_arity stats isUnsafe parent ctor type
    current.fuel.inductiveFuel current hfvars hnodup).bind fun _ hbound => .pure hbound

private theorem forIn'_all (items : List α) (initial : β) (ctx : Context)
    (step : (item : α) → item ∈ items → β → M (ForInStep β)) (property : α → Prop)
    (hstep : ∀ item hmem state, (step item hmem state ctx).WF fun result =>
      ∃ next, result = .yield next ∧ property item) :
    (forIn' items initial step ctx).WF fun _ => ∀ item ∈ items, property item := by
  induction items generalizing initial with
  | nil => exact .pure (by simp)
  | cons item items ih =>
    rw [List.forIn'_cons]
    refine (hstep item (by simp) initial).bind ?_
    rintro _ ⟨next, rfl, hitem⟩
    refine (ih next (fun entry hmem state => step entry (by simp [hmem]) state)
      (fun entry hmem state => hstep entry (by simp [hmem]) state)).mono ?_
    intro _ hrest entry hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hitem
    · exact hrest entry hmem

private theorem bindInvariantWF {ctx : Context} {action : M α} {next : α → M β}
    {invariant : α → Prop} {post : β → Prop} (haction : (action ctx).WF invariant)
    (hnext : ∀ result, invariant result → (next result ctx).WF post) :
    ((action >>= next) ctx).WF post :=
  haction.bind hnext

theorem checkConstructors.arity (indTypes : Array InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (ctx : Context) (hfvars : stats.ParamsAreFVars)
    (hnodup : stats.params.toList.Nodup) :
    (checkConstructors indTypes stats isUnsafe ctx).WF fun _ =>
      ∀ indType ∈ indTypes, ∀ ctor ∈ indType.ctors,
        stats.params.size ≤ declareConstructors.arity 0 ctor.type := by
  unfold checkConstructors
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro env
  refine bindInvariantWF (ctx := ctx)
    (post := fun _ => ∀ indType ∈ indTypes, ∀ ctor ∈ indType.ctors,
      stats.params.size ≤ declareConstructors.arity 0 ctor.type)
    (invariant := fun _ =>
      ∀ index ∈ List.range' 0 indTypes.size, ∀ hindex : index < indTypes.size,
        ∀ ctor ∈ indTypes[index].ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type) ?_ ?_
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_all
    intro index hindex state
    have hbound : index < indTypes.size := by simpa using hindex
    refine bindInvariantWF (ctx := ctx)
      (post := fun (result : ForInStep Unit) => ∃ next, result = .yield next ∧
        ∀ hindex : index < indTypes.size, ∀ ctor ∈ indTypes[index].ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type)
      (invariant := fun _ =>
        ∀ ctor ∈ indTypes[index].ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type) ?_ ?_
    · change (forIn' (m := M) _ _ _ ctx).WF _
      apply forIn'_all
      intro ctor _ found
      dsimp only
      split
      · exact Except.WF.throw
      · simp only [pure_bind]
        refine (Lean4Lean.checkNoMVarNoFVar.WF env ctor.name ctor.type).bind ?_
        intro _ hclosed
        apply Lean4Lean.AddInductive.bindWF
        intro checkedType
        exact (checkConstructors.loop_arity_of_noFVars stats isUnsafe index ctor.name
          ctor.type ctx.fuel.inductiveFuel ctx hfvars hnodup hclosed).bind fun _ hbound =>
            .pure ⟨_, rfl, hbound⟩
    · intro _ hctors
      exact .pure ⟨_, rfl, fun _ => hctors⟩
  · intro _ hall
    refine .pure ?_
    intro indType htype ctor hctor
    obtain ⟨index, hindex, rfl⟩ := Array.mem_iff_getElem.mp htype
    exact hall index (by simp; omega) hindex ctor hctor

theorem checkInductiveTypes.checkedConstructorsArity (nparams : Nat)
    (indTypes : Array InductiveType) (isUnsafe : Bool) (ctx : Context) :
    (checkInductiveTypes nparams indTypes (fun stats =>
      checkConstructors indTypes stats isUnsafe >>= fun _ => pure stats) ctx).WF fun stats =>
        ∀ indType ∈ indTypes, ∀ ctor ∈ indType.ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type := by
  apply checkInductiveTypes.frameHeaderSizesParamsDistinct
  intro stats current _ hfvars hnodup _
  exact (checkConstructors.arity indTypes stats isUnsafe current hfvars hnodup).bind
    fun _ hbound => .pure hbound

end Lean4Lean.AddInductive
