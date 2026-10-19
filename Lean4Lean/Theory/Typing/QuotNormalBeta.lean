import Lean4Lean.Theory.Typing.QuotBetaSimulation

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
variable {environment : VEnv} {universes : Nat} {environmentWF : environment.WF}

/-- A proof-valued function stays proof-valued after application. This handles
EVERY actual core successor, including beta and checked rewriting. -/
theorem CoreSimulates.proof_application
    (localsWF : OnCtx locals (environment.IsType universes))
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (leftProof : environment.HasType universes locals left proposition)
    (rightProof : environment.HasType universes locals right proposition)
    (functionTyped : environment.HasType universes locals left (.forallE domain body))
    (argumentTyped : environment.HasType universes locals argument domain)
    (argumentNormal : @NormalEq (environmentWF.reductionParams universes) locals argument argument') :
    CoreSimulates environmentWF universes locals (.app left argument) (.app right argument') := by
  letI := environmentWF.reductionParams universes
  have functionProposition := propositionTyped.defeqU_l environmentWF localsWF
    (leftProof.uniqU environmentWF localsWF functionTyped)
  obtain ⟨⟨domainLevel, domainTyped⟩, bodyLevel, bodyTyped⟩ := functionProposition.forallE_inv environmentWF.ordered
  have levels := ((domainTyped.forallE bodyTyped).uniqU environmentWF localsWF functionProposition).sort_inv
    environmentWF localsWF
  have extendedWF : OnCtx (domain :: locals) (environment.IsType universes) := ⟨localsWF, _, domainTyped⟩
  obtain ⟨_, bodySort⟩ := bodyTyped.isType environmentWF.ordered extendedWF
  have bodyZero : bodyLevel ≈ .zero := VLevel.equiv_def.mpr fun values => by
    have evaluated := VLevel.equiv_def.mp levels values
    change (if bodyLevel.eval values = 0 then 0 else
      max (domainLevel.eval values) (bodyLevel.eval values)) = 0 at evaluated
    change bodyLevel.eval values = 0
    cases bodyValue : bodyLevel.eval values with
    | zero => rfl
    | succ value =>
      simp only [bodyValue, Nat.succ_ne_zero, if_false] at evaluated
      exact Nat.le_zero.mp (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_of_eq evaluated))
  have bodyProposition := IsDefEq.defeq
    (.sortDF (bodySort.sort_inv environmentWF.ordered) (by trivial) bodyZero) bodyTyped
  have functionNormal : NormalEq locals left right := .proofIrrel propositionTyped leftProof rightProof
  have rightFunction := ((functionNormal.defeq localsWF).of_l environmentWF localsWF functionTyped).hasType.2
  have rightArgument := ((argumentNormal.defeq localsWF).of_l environmentWF localsWF argumentTyped).hasType.2
  have applicationNormal := NormalEq.appDF functionTyped rightFunction argumentTyped rightArgument
    functionNormal argumentNormal
  have leftTyped := functionTyped.app argumentTyped
  have rightTyped := ((applicationNormal.defeq localsWF).of_l environmentWF localsWF leftTyped).hasType.2
  intro result reduction
  exact ⟨_, .rfl, .proofIrrel (bodyProposition.instN environmentWF.ordered Ctx.InstN.zero argumentTyped)
    leftTyped (reduction.hasType localsWF rightTyped)⟩

/-- Forward beta beneath retained binders and eta applications. No term or
typing is transported out of a binder. -/
theorem ParRedExt.beta_forward (extension : ParRedExt)
    (bound : extension.depth ≤ locals.length) :
    @ParRed (environmentWF.reductionParams universes) locals
      (extension.apply (.app (VExpr.lam domain body).lift (.bvar 0))) (extension.apply body) := by
  letI := environmentWF.reductionParams universes
  induction extension generalizing locals with
  | base =>
    have beta := ParRed.beta (A := domain.lift) (Γ := locals)
      (ParRed.rfl (e := body.liftN 1 1)) (ParRed.rfl (e := .bvar 0))
    rw [VExpr.instN_bvar0] at beta
    simpa only [ParRedExt.apply, VExpr.lift, VExpr.liftN] using beta
  | lift extension induction =>
    cases locals with
    | nil => simp [ParRedExt.depth] at bound
    | cons domain locals =>
      exact (induction (by simpa [ParRedExt.depth] using bound)).weakN Ctx.LiftN.one
  | app extension induction =>
    cases locals with
    | nil => simp [ParRedExt.depth] at bound
    | cons domain locals =>
      exact .app ((induction (by simpa [ParRedExt.depth] using bound)).weakN Ctx.LiftN.one) .bvar

private theorem lambdaArgumentTyped (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (.app (.lam domain body) argument) type) :
    ∃ level bodyType, environment.HasType universes locals domain (.sort level) ∧
      environment.HasType universes (domain :: locals) body bodyType ∧
      environment.HasType universes locals argument domain := by
  obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  obtain ⟨⟨_, domainTyped⟩, _, bodyTyped⟩ := functionTyped.lam_inv environmentWF.ordered localsWF
  obtain ⟨⟨_, domainEqual⟩, _⟩ :=
    ((domainTyped.lam bodyTyped).uniqU environmentWF localsWF functionTyped).forallE_inv environmentWF localsWF
  exact ⟨_, _, domainTyped, bodyTyped, domainEqual.symm.defeq argumentTyped⟩

/-- Normally related functions can follow a root beta on the right even when
the left function has an arbitrary eta-related shape. Both arguments may differ.
The proof recurses on the LEFT syntax and uses only forward binder transport. -/
theorem normal_beta_join {Γ : List VExpr} {f A e' a a' B : VExpr}
    (registered : environment.defeqs quotDefEq)
    (hΓ : OnCtx Γ (environment.IsType universes))
    (functionNormal : @NormalEq (environmentWF.reductionParams universes) Γ f (.lam A e'))
    (argumentNormal : @NormalEq (environmentWF.reductionParams universes) Γ a a')
    (sourceTyped : environment.HasType universes Γ (.app f a) B) :
    ∃ result, Steps environmentWF universes Γ (.app f a) result ∧
      @NormalEq (environmentWF.reductionParams universes) Γ result (e'.inst a') := by
  letI := environmentWF.reductionParams universes
  suffices
      (∀ {a a' B}, NormalEq Γ f (.lam A e') → NormalEq Γ a a' →
        environment.HasType universes Γ (.app f a) B →
        ∃ result, Steps environmentWF universes Γ (.app f a) result ∧ NormalEq Γ result (e'.inst a')) ∧
      (∀ (extension : ParRedExt), extension.depth ≤ Γ.length →
        NormalEq Γ f (extension.apply (.app (VExpr.lam A e').lift (.bvar 0))) →
        ∃ result, Steps environmentWF universes Γ f result ∧ NormalEq Γ result (extension.apply e')) from
    this.1 functionNormal argumentNormal sourceTyped
  clear functionNormal argumentNormal sourceTyped
  induction f using VExpr.brecOn generalizing Γ A e' with | _ f f_ih => ?_
  revert f_ih
  change let motive := ?_; ∀ _ : f.below (motive := motive), _
  intro motive f_ih
  refine ⟨fun normal arguments typed => ?_, fun extension bound normal => ?_⟩
  · cases normal with
    | refl functionTyped =>
      obtain ⟨_, _, domainTyped, bodyTyped, argumentTyped⟩ := lambdaArgumentTyped environmentWF hΓ typed
      exact ⟨_, .tail .rfl (.core (.beta .rfl .rfl)),
        NormalEq.instDF hΓ domainTyped argumentTyped arguments (.refl bodyTyped)⟩
    | lamDF leftDomain rightDomain bodies =>
      obtain ⟨_, _, _, _, argumentTyped⟩ := lambdaArgumentTyped environmentWF hΓ typed
      exact ⟨_, .tail .rfl (.core (.beta .rfl .rfl)),
        NormalEq.instDF hΓ leftDomain.hasType.1 (leftDomain.symm.defeq argumentTyped) arguments bodies⟩
    | @etaL _ _ domain _ _ functionTyped bodies =>
      obtain ⟨_, _, domainTyped, _, argumentTyped⟩ := lambdaArgumentTyped environmentWF hΓ typed
      obtain ⟨result, bodySteps, bodyNormal⟩ :=
        (f_ih.2.1 (by exact ⟨hΓ, _, domainTyped⟩)).2 .base (Nat.zero_le _) bodies
      exact ⟨_, (ReflTransGen.tail .rfl (.core (.beta .rfl .rfl))).trans
        (bodySteps.instN Ctx.InstN.zero argumentTyped),
        NormalEq.instDF hΓ domainTyped argumentTyped arguments bodyNormal⟩
    | etaR functionTyped bodies =>
      obtain ⟨_, _, actualFunction, argumentTyped⟩ := typed.app_inv environmentWF.ordered hΓ
      obtain ⟨⟨_, domainEqual⟩, _⟩ :=
        (actualFunction.uniqU environmentWF hΓ functionTyped).forallE_inv environmentWF hΓ
      obtain ⟨_, functionType⟩ := functionTyped.isType environmentWF.ordered hΓ
      obtain ⟨⟨_, domainTyped⟩, _, _⟩ := functionType.forallE_inv environmentWF.ordered
      have joined := NormalEq.instDF hΓ domainTyped (domainEqual.defeq argumentTyped) arguments bodies
      exact ⟨_, .rfl, by simpa [VExpr.inst, VExpr.inst_lift] using joined⟩
    | proofIrrel propositionTyped leftTyped rightTyped =>
      obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv environmentWF.ordered hΓ
      exact CoreSimulates.proof_application hΓ propositionTyped leftTyped rightTyped functionTyped
        argumentTyped arguments (.beta .rfl .rfl)
  · generalize equation : extension.apply _ = source at normal
    cases normal with
    | refl typed =>
      subst equation
      have reduction := ParRedExt.beta_forward (environmentWF := environmentWF) (universes := universes) (domain := A) (body := e') extension bound
      exact ⟨_, .tail .rfl (.core reduction), .refl (reduction.hasType hΓ typed)⟩
    | @appDF _ _ _ _ function _ argument leftFunction rightFunction leftArgument rightArgument functions arguments =>
      obtain ⟨n, rfl, ⟨rfl, bodyEquation⟩ | ⟨smaller, smallerBound, rfl, bodyEquation⟩⟩ :
          ∃ n, argument = .bvar n ∧
            (function = (VExpr.lam A e').liftN (n+1) ∧ extension.apply e' = e'.liftN n ∨
              ∃ smaller : ParRedExt, smaller.depth ≤ extension.depth ∧
                function = smaller.apply (.app (VExpr.lam A e').lift (.bvar 0)) ∧
                extension.apply e' = .app (smaller.apply e') (.bvar n)) := by
        clear bound rightFunction rightArgument functions arguments
        induction extension generalizing function argument with
        | base => cases equation; exact ⟨_, rfl, .inl ⟨rfl, by simp [ParRedExt.apply]⟩⟩
        | lift extension induction =>
          simp [ParRedExt.apply] at equation
          generalize inner : ParRedExt.apply _ _ = term at equation
          cases term <;> cases equation
          obtain ⟨n, rfl, ⟨rfl, bodyEquation⟩ | ⟨smaller, smallerBound, rfl, bodyEquation⟩⟩ := induction inner
          · refine ⟨_, rfl, .inl ⟨by simp [VExpr.liftN_liftN], ?_⟩⟩
            have lifted := congrArg VExpr.lift bodyEquation
            simpa [ParRedExt.apply, VExpr.lift_inst_hi, VExpr.liftN'_liftN'] using lifted
          · exact ⟨_, rfl, .inr ⟨.lift smaller, Nat.succ_le_succ smallerBound, rfl,
              congrArg VExpr.lift bodyEquation⟩⟩
        | app extension induction => cases equation; exact ⟨_, rfl, .inr ⟨.lift _, Nat.le_refl _, rfl, rfl⟩⟩
      · obtain ⟨result, steps, joined⟩ := (f_ih.1.1 hΓ).1 functions arguments (.app leftFunction leftArgument)
        have identity := congrArg (VExpr.liftN n) (VExpr.instN_bvar0 e' 0)
        simp [VExpr.liftN_inst_hi, VExpr.liftN'_liftN', VExpr.liftN] at identity
        rw [Nat.add_comm, identity, ← bodyEquation] at joined
        exact ⟨_, steps, joined⟩
      · obtain ⟨result, steps, joined⟩ := (f_ih.1.1 hΓ).2 smaller (Nat.le_trans smallerBound bound) functions
        rw [bodyEquation]
        have resultTyped := steps.hasType registered hΓ leftFunction
        have otherTyped := ((joined.defeq hΓ).of_l environmentWF hΓ resultTyped).hasType.2
        exact ⟨_, steps.app .rfl, .appDF resultTyped otherTyped leftArgument rightArgument joined arguments⟩
    | etaL functionTyped bodies =>
      subst equation
      obtain ⟨_, functionType⟩ := functionTyped.isType environmentWF.ordered hΓ
      obtain ⟨⟨_, domainTyped⟩, _, _⟩ := functionType.forallE_inv environmentWF.ordered
      have extendedWF : OnCtx (_ :: Γ) (environment.IsType universes) := ⟨hΓ, _, domainTyped⟩
      obtain ⟨result, steps, joined⟩ := (f_ih.2.1 extendedWF).2
        (.app extension) (Nat.succ_le_succ bound) bodies
      have targetTyped := (ParRedExt.beta_forward (environmentWF := environmentWF) (universes := universes) (domain := A) (body := e') extension bound).hasType
        hΓ functionTyped
      exact ⟨_, steps.lam, .etaL targetTyped joined⟩
    | proofIrrel propositionTyped leftTyped rightTyped =>
      subst equation
      exact ⟨_, .rfl, .proofIrrel propositionTyped leftTyped
        ((ParRedExt.beta_forward (environmentWF := environmentWF) (universes := universes) (domain := A) (body := e') extension bound).hasType hΓ rightTyped)⟩
    | _ => cases extension.isApp equation

/-- The GENERAL application beta branch. The function simulation hypothesis
may return any normally related shape; normal_beta_join handles its eta cases.
No recursive body simulation or lambda shape is required of the left function. -/
theorem CoreSimulates.app_beta
    (registered : environment.defeqs quotDefEq)
    (localsWF : OnCtx locals (environment.IsType universes))
    (sourceTyped : environment.HasType universes locals (.app function argument) type)
    (functionSimulation : CoreSimulates environmentWF universes locals function (.lam domain body))
    (argumentSimulation : CoreSimulates environmentWF universes locals argument rightArgument)
    (bodyReduction : @ParRed (environmentWF.reductionParams universes) (domain :: locals) body bodyResult)
    (argumentReduction : @ParRed (environmentWF.reductionParams universes) locals rightArgument argumentResult) :
    ∃ result,
      @ParRed (environmentWF.reductionParams universes) locals
        (.app (.lam domain body) rightArgument) (bodyResult.inst argumentResult) ∧
      Steps environmentWF universes locals (.app function argument) result ∧
      @NormalEq (environmentWF.reductionParams universes) locals result (bodyResult.inst argumentResult) ∧
      environment.HasType universes locals result type ∧
      environment.HasType universes locals (bodyResult.inst argumentResult) type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨functionResult, functionSteps, functionNormal⟩ := functionSimulation (.lam .rfl bodyReduction)
  obtain ⟨argumentResult', argumentSteps, argumentNormal⟩ := argumentSimulation argumentReduction
  have applicationSteps := functionSteps.app argumentSteps
  obtain ⟨result, betaSteps, normal⟩ := normal_beta_join registered localsWF functionNormal argumentNormal
    (applicationSteps.hasType registered localsWF sourceTyped)
  have steps : Steps environmentWF universes locals (.app function argument) result :=
    applicationSteps.trans betaSteps
  have typed := steps.hasType registered localsWF sourceTyped
  exact ⟨result, .beta bodyReduction argumentReduction, steps, normal, typed,
    ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2⟩

end Lean4Lean.VEnv.QuotPropReduction
