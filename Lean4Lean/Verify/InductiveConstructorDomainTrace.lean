import Lean4Lean.Verify.InductiveHeaderDomainAgreement
import Lean4Lean.Verify.InductivePositivity

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix ContextReserved)
open private bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.forIn'_all Lean4Lean.AddInductive.bindInvariantWF
  from Lean4Lean.Verify.ConstructorParams

inductive AcceptedConstructorTrace (stats : InductiveStats) (isUnsafe : Bool) (parent : Nat) :
    Context → Nat → Expr → Context → Nat → Expr → Prop where
  | terminal (notForall : type.isForall = false) (valid : isValidIndAppIdx stats type parent = true) :
      AcceptedConstructorTrace stats isUnsafe parent reader index type reader index type
  | parameter
      (selected : stats.params[index]? = some parameter)
      {storedType : getType parameter reader = .ok stored}
      (accepted : (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true)
      (tail : AcceptedConstructorTrace stats isUnsafe parent reader (index + 1)
        (Expr.instantiate1 body parameter) finalReader finalIndex terminal) :
      AcceptedConstructorTrace stats isUnsafe parent reader index
        (.forallE name domain body binder) finalReader finalIndex terminal
  | field
      (notParameter : stats.params[index]? = none)
      (domainChecked : (monadLift (TypeChecker.ensureType domain) : M Expr) reader = .ok sort)
      (universeAccepted : (stats.resultLevel.isZero || stats.resultLevel.geq' sort.sortLevel!) = true)
      (positive : isUnsafe = false → PositivityTrace stats PositivityWHNF reader domain)
      (tail : AcceptedConstructorTrace stats isUnsafe parent (reader.withPositivityArg name domain binder)
        (index + 1) (Expr.instantiate1 body (.fvar ⟨reader.ngen.curr⟩)) finalReader finalIndex terminal) :
      AcceptedConstructorTrace stats isUnsafe parent reader index
        (.forallE name domain body binder) finalReader finalIndex terminal

section NativeTrace

variable {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
  {reader finalReader : Context} {type terminal : Expr}
  {trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal}

theorem AcceptedConstructorTrace.index_le
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal) :
    index ≤ finalIndex := by
  induction trace with
  | terminal => omega
  | parameter _ _ _ induction => omega
  | field _ _ _ _ _ induction => omega

theorem AcceptedConstructorTrace.safe
    (trace : AcceptedConstructorTrace stats false parent reader index type finalReader finalIndex terminal) :
    SafeConstructorTrace stats PositivityWHNF parent reader index type terminal := by
  induction trace with
  | terminal notForall valid => exact .terminal notForall valid
  | parameter selected _ _ induction => exact .parameter selected induction
  | field notParameter _ _ positive _ induction => exact .field notParameter (positive rfl) induction

theorem AcceptedConstructorTrace.scope
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    (readerWF : reader.lctx.WF) (reserved : ContextReserved reader.lctx reader.ngen) :
    reader.RecursorScopeFrame finalReader := by
  revert readerWF reserved
  induction trace with
  | terminal => intro readerWF reserved; exact .refl _ readerWF reserved
  | parameter _ _ _ induction => exact induction
  | @field index domain reader sort name binder body finalReader finalIndex terminal
      notParameter domainChecked universeAccepted positive tail induction =>
    intro readerWF reserved
    have extended := Context.RecursorScopeFrame.push reader readerWF reserved name binder (peelTypeAnnotations domain)
    exact extended.trans (induction extended.wf extended.reserved)

theorem checkConstructors.loop.acceptedTrace (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (constructor : Name) (type : Expr) (index fuel : Nat) (reader : Context) :
    (checkConstructors.loop stats isUnsafe parent constructor type index fuel reader).WF fun _ =>
      ∃ finalReader finalIndex terminal,
        AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal := by
  induction fuel generalizing type index reader with
  | zero => exact Except.WF.throw
  | succ fuel induction =>
    cases type with
    | forallE name domain body binder =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      cases selected : stats.params[index]? with
      | some parameter =>
        apply bindHeaderResultWF
        intro stored storedType
        apply bindHeaderResultWF
        intro equal accepted
        split
        · apply Lean4Lean.AddInductive.bindWF
          intro _
          have same : equal = true := by simpa using ‹equal = true›
          subst equal
          refine (induction (body.instantiate1 parameter) (index + 1) reader).mono ?_
          rintro _ ⟨finalReader, finalIndex, terminal, tail⟩
          exact ⟨_, _, _, .parameter selected (storedType := storedType) accepted tail⟩
        · exact Except.WF.throw
      | none =>
        apply bindHeaderResultWF
        intro sort domainChecked
        split
        · rename_i universeAccepted
          cases isUnsafe with
          | false =>
            refine (checkPositivity.trace stats domain constructor index reader).bind ?_
            intro _ positive
            change (checkConstructors.loop stats false parent constructor
              (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) (index + 1) fuel
              (reader.withPositivityArg name domain binder)).WF _
            refine (induction _ _ _).mono ?_
            rintro _ ⟨finalReader, finalIndex, terminal, tail⟩
            exact ⟨_, _, _, .field selected domainChecked universeAccepted (fun _ => positive) tail⟩
          | true =>
            change (checkConstructors.loop stats true parent constructor
              (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) (index + 1) fuel
              (reader.withPositivityArg name domain binder)).WF _
            refine (induction _ _ _).mono ?_
            rintro _ ⟨finalReader, finalIndex, terminal, tail⟩
            exact ⟨_, _, _, .field selected domainChecked universeAccepted (by intro impossible; cases impossible) tail⟩
        · exact Except.WF.throw
    | _ =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      split
      · exact Except.WF.throw
      · rename_i valid
        exact .pure ⟨_, _, _, .terminal rfl (by simpa using valid)⟩

def InductiveStats.AcceptedConstructorTraces (stats : InductiveStats)
    (types : Array InductiveType) (isUnsafe : Bool) (reader : Context) : Prop :=
  ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
    ∃ sourceType finalReader finalIndex terminal,
      reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
      (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType ∧
      AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type finalReader finalIndex terminal

theorem InductiveStats.AcceptedConstructorTraces.safe
    (traces : stats.AcceptedConstructorTraces types false reader) :
    stats.SafeConstructorTraces types PositivityWHNF reader := by
  intro parent bound constructor member
  obtain ⟨_, _, _, terminal, _, _, trace⟩ := traces parent bound constructor member
  exact ⟨terminal, trace.safe⟩

theorem checkConstructors.acceptedTraces (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (reader : Context) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      stats.AcceptedConstructorTraces types isUnsafe reader := by
  unfold checkConstructors
  dsimp only
  apply bindHeaderResultWF
  intro environment environmentChecked
  have environmentEq : reader.env = environment := Except.ok.inj environmentChecked
  subst environment
  refine Lean4Lean.AddInductive.bindInvariantWF (ctx := reader)
    (post := fun _ => stats.AcceptedConstructorTraces types isUnsafe reader)
    (invariant := fun _ =>
      ∀ parent ∈ List.range' 0 types.size, ∀ bound : parent < types.size,
        ∀ constructor ∈ types[parent].ctors,
          ∃ sourceType finalReader finalIndex terminal,
            reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
            (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType ∧
            AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type finalReader finalIndex terminal)
    ?_ ?_
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply Lean4Lean.AddInductive.forIn'_all
    intro parent member found
    have bound : parent < types.size := by simpa using member
    refine Lean4Lean.AddInductive.bindInvariantWF (ctx := reader)
      (post := fun (result : ForInStep Unit) => ∃ next, result = .yield next ∧
        ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
          ∃ sourceType finalReader finalIndex terminal,
            reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
            (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType ∧
            AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type finalReader finalIndex terminal)
      (invariant := fun _ => ∀ constructor ∈ types[parent].ctors,
        ∃ sourceType finalReader finalIndex terminal,
          reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () ∧
          (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType ∧
          AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type finalReader finalIndex terminal)
      ?_ ?_
    · change (forIn' (m := M) _ _ _ reader).WF _
      apply Lean4Lean.AddInductive.forIn'_all
      intro constructor _ found
      dsimp only
      split
      · exact Except.WF.throw
      · simp only [pure_bind]
        apply bindHeaderResultWF
        intro guarded sourceGuard
        have sourceGuard : reader.env.checkNoMVarNoFVar constructor.name constructor.type = .ok () :=
          sourceGuard
        apply bindHeaderResultWF
        intro sourceType sourceChecked
        exact (checkConstructors.loop.acceptedTrace stats isUnsafe parent constructor.name
          constructor.type 0 reader.fuel.inductiveFuel reader).bind fun _ ⟨finalReader, finalIndex, terminal, trace⟩ =>
            .pure ⟨_, rfl, sourceType, finalReader, finalIndex, terminal, sourceGuard, sourceChecked, trace⟩
    · intro _ constructors
      exact .pure ⟨_, rfl, fun _ => constructors⟩
  · intro _ all
    exact .pure fun parent bound constructor member => all parent (by simp; omega) bound constructor member

end NativeTrace

inductive CheckedConstructorDomainReceipts (env : VEnv) (universes : List Name) :
    {stats : InductiveStats} → {isUnsafe : Bool} → {parent index finalIndex : Nat} →
    {reader finalReader : Context} → {type terminal : Expr} →
    AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal →
    List VExpr → List VExpr → List VExpr → List VExpr → Prop where
  | terminal (notForall : type.isForall = false) (valid : isValidIndAppIdx stats type parent = true) :
      CheckedConstructorDomainReceipts env universes
        (AcceptedConstructorTrace.terminal (isUnsafe := isUnsafe) (reader := reader) (index := index) notForall valid)
        source target source target
  | parameter
      (selected : stats.params[index]? = some parameter)
      {storedType : getType parameter reader = .ok stored}
      (accepted : (monadLift (TypeChecker.isDefEq domain stored) : M Bool) reader = .ok true)
      {trace : AcceptedConstructorTrace stats isUnsafe parent reader (index + 1)
        (Expr.instantiate1 body parameter) finalReader finalIndex terminal}
      (domainReceipt : ReducedParameterDomainReceipt env universes reader domain stored
        source storedSemantic candidateSemantic)
      (tail : CheckedConstructorDomainReceipts env universes trace
        (storedSemantic :: source) (candidateSemantic :: target) finalSource finalTarget) :
      CheckedConstructorDomainReceipts env universes
        (AcceptedConstructorTrace.parameter (name := name) (binder := binder) selected
          (storedType := storedType) accepted trace)
        source target finalSource finalTarget
  | field
      (notParameter : stats.params[index]? = none)
      (domainChecked : (monadLift (TypeChecker.ensureType domain) : M Expr) reader = .ok sort)
      (universeAccepted : (stats.resultLevel.isZero || stats.resultLevel.geq' sort.sortLevel!) = true)
      (positive : isUnsafe = false → PositivityTrace stats PositivityWHNF reader domain)
      {trace : AcceptedConstructorTrace stats isUnsafe parent (reader.withPositivityArg name domain binder)
        (index + 1) (Expr.instantiate1 body (.fvar ⟨reader.ngen.curr⟩)) finalReader finalIndex terminal}
      (tail : CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget) :
      CheckedConstructorDomainReceipts env universes
        (AcceptedConstructorTrace.field notParameter domainChecked universeAccepted positive trace)
        source target finalSource finalTarget

variable {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
  {reader finalReader : Context} {type terminal : Expr}
  {trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal}
  {env : VEnv} {universes : List Name} {base source target finalSource finalTarget : List VExpr}

private theorem selectedParameterBound {parameters : Array Expr} {index : Nat} {parameter : Expr}
    (selected : parameters[index]? = some parameter) : index < parameters.size := by
  by_contra notBound
  simp only [getElem?_neg parameters index notBound] at selected
  cases selected

private theorem absentParameterBound {parameters : Array Expr} {index : Nat}
    (absent : parameters[index]? = none) : parameters.size ≤ index := by
  by_contra notBound
  have within : index < parameters.size := by omega
  simp only [getElem?_pos parameters index within] at absent
  cases absent

theorem CheckedConstructorDomainReceipts.index_le
    (_receipts : CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget) :
    index ≤ finalIndex := trace.index_le

theorem CheckedConstructorDomainReceipts.agreement
    (receipts : CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget)
    (contexts : env.IsDefEqCtx universes.length base source target) :
    env.IsDefEqCtx universes.length base finalSource finalTarget := by
  induction receipts with
  | terminal => exact contexts
  | parameter _ accepted domainReceipt _ induction =>
    obtain ⟨_, equality⟩ := domainReceipt.accepted accepted
    exact induction (.succ contexts equality)
  | field _ _ _ _ _ induction => exact induction contexts

theorem CheckedConstructorDomainReceipts.growth
    (receipts : CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget) :
    finalSource.length = source.length + (min finalIndex stats.params.size - min index stats.params.size) ∧
      finalTarget.length = target.length + (min finalIndex stats.params.size - min index stats.params.size) := by
  induction receipts with
  | terminal => simp
  | parameter selected _ _ tail induction =>
    have bound := selectedParameterBound selected
    have monotone := tail.index_le
    simp only [List.length_cons] at induction
    omega
  | field notParameter _ _ _ _ induction =>
    have bound := absentParameterBound notParameter
    omega

theorem CheckedConstructorDomainReceipts.completeGrowth
    (receipts : CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget)
    (complete : stats.params.size ≤ finalIndex) :
    finalSource.length = source.length + (stats.params.size - index) ∧
      finalTarget.length = target.length + (stats.params.size - index) := by
  have growth := receipts.growth
  omega

theorem CheckedConstructorDomainReceipts.rebindPrefix
    {base source target : MLCtx} {identifiers targetIdentifiers : List FVarId}
    (receipts : CheckedConstructorDomainReceipts env universes trace base.vlctx.toCtx base.vlctx.toCtx
      source.vlctx.toCtx target.vlctx.toCtx)
    (envWF : env.WF) (sourceWF : source.WF env universes) (targetWF : target.WF env universes)
    (parameters : ParameterPrefix base source identifiers)
    (targetParameters : ParameterPrefix base target targetIdentifiers)
    {body : Expr} {semantic semanticType : VExpr}
    (translated : TrExprS env universes source.vlctx body semantic)
    (typed : env.HasType universes.length source.vlctx.toCtx semantic semanticType)
    (nativeEnv : Kernel.Environment) (state : ElimNestedInductive.State) :
    (ElimNestedInductive.replaceParams (targetIdentifiers.map Expr.fvar).toArray body
      (identifiers.map Expr.fvar).toArray nativeEnv state).WF fun returned =>
        returned.2 = state ∧
        returned.1 = (body.abstractList identifiers).instantiateRevList (targetIdentifiers.map Expr.fvar) ∧
        Closed returned.1 0 ∧ returned.1.looseBVarRange' = 0 ∧
        returned.1.FVarsIn (· ∈ target.vlctx.fvars) ∧
        ∃ resultSemantic, TrExprS env universes target.vlctx returned.1 resultSemantic ∧
          env.HasType universes.length target.vlctx.toCtx resultSemantic semanticType := by
  have contexts := receipts.agreement (base := base.vlctx.toCtx) .zero
  have length : identifiers.length = targetIdentifiers.length := by
    have sameLength := contexts.length_eq
    rw [parameters.toCtx_length, targetParameters.toCtx_length] at sameLength
    omega
  exact ElimNestedInductive.replaceParams.prefix_rename_defeq_typed envWF sourceWF targetWF
    parameters targetParameters length contexts translated typed nativeEnv state

theorem checkConstructors.domainAgreement (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (reader : Context)
    (contexts : env.IsDefEqCtx universes.length base source target)
    (receiptProvider : ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
      ∀ sourceType finalReader finalIndex terminal,
      (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType →
      ∀ trace : AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type
        finalReader finalIndex terminal,
      CheckedConstructorDomainReceipts env universes trace source target finalSource finalTarget) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ sourceType finalReader finalIndex terminal,
          (monadLift (TypeChecker.checkType constructor.type) : M Expr) reader = .ok sourceType ∧
          AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type
            finalReader finalIndex terminal ∧
          env.IsDefEqCtx universes.length base finalSource finalTarget ∧
          finalSource.length = source.length + min finalIndex stats.params.size ∧
          finalTarget.length = target.length + min finalIndex stats.params.size := by
  refine (checkConstructors.acceptedTraces types stats isUnsafe reader).mono ?_
  intro _ traces parent bound constructor member
  obtain ⟨sourceType, finalReader, finalIndex, terminal, _, sourceChecked, trace⟩ :=
    traces parent bound constructor member
  have model := receiptProvider parent bound constructor member sourceType finalReader finalIndex terminal
    sourceChecked trace
  have growth := model.growth
  simp only [Nat.zero_min, Nat.sub_zero] at growth
  exact ⟨sourceType, finalReader, finalIndex, terminal, sourceChecked, trace,
    model.agreement contexts, growth.1, growth.2⟩

end Lean4Lean.AddInductive
