import Lean4Lean.Theory.Typing.QuotNormalExtra

namespace Lean4Lean.VEnv.QuotPropReduction

open VExpr
open private substituteLift from Lean4Lean.Theory.Typing.SimultaneousNormalSubstitution
open private lambdaArgumentTyped from Lean4Lean.Theory.Typing.QuotNormalBeta

variable {environment : VEnv} {universes : Nat} {locals : List VExpr}
  {environmentWF : environment.WF}

theorem applyArguments_subst (function : VExpr) (arguments : List VExpr) (substitution : VExpr.Subst) :
    (applyArguments function arguments).subst substitution =
      applyArguments (function.subst substitution) (arguments.map (·.subst substitution)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument arguments induction => exact induction (.app function argument)

theorem applyArguments_liftN (function : VExpr) (arguments : List VExpr) (count depth : Nat) :
    (applyArguments function arguments).liftN count depth =
      applyArguments (function.liftN count depth) (arguments.map (·.liftN count depth)) := by
  induction arguments generalizing function with
  | nil => rfl
  | cons argument arguments induction => exact induction (.app function argument)

theorem applyArguments_inst (function : VExpr) (arguments : List VExpr) (argument : VExpr) :
    (applyArguments function arguments).inst argument =
      applyArguments (function.inst argument) (arguments.map (·.inst argument)) := by
  simpa only [VExpr.inst_eq] using applyArguments_subst function arguments (.one argument)

include environmentWF in
theorem HasType.spine_head {function type : VExpr} {arguments : List VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments function arguments) type) :
    ∃ headType, environment.HasType universes locals function headType := by
  induction arguments generalizing function with
  | nil => exact ⟨_, typed⟩
  | cons argument arguments induction =>
    obtain ⟨_, applicationTyped⟩ := induction typed
    obtain ⟨_, _, functionTyped, _⟩ := applicationTyped.app_inv environmentWF.ordered localsWF
    exact ⟨_, functionTyped⟩

theorem normal_spine_congr
    {function function' type : VExpr} {arguments arguments' : List VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments function arguments) type)
    (functions : @NormalEq (environmentWF.reductionParams universes) locals function function')
    (argumentsNormal : List.Forall₂
      (@NormalEq (environmentWF.reductionParams universes) locals) arguments arguments') :
    @NormalEq (environmentWF.reductionParams universes) locals
      (applyArguments function arguments) (applyArguments function' arguments') := by
  letI := environmentWF.reductionParams universes
  induction argumentsNormal generalizing function function' with
  | nil => exact functions
  | @cons argument argument' arguments arguments' normal normals induction =>
    obtain ⟨_, applicationTyped⟩ := HasType.spine_head (environmentWF := environmentWF)
      (function := .app function argument) (arguments := arguments) localsWF typed
    obtain ⟨_, _, functionTyped, argumentTyped⟩ := applicationTyped.app_inv environmentWF.ordered localsWF
    have next := NormalEq.appDF functionTyped
      ((functions.defeq localsWF).of_l environmentWF localsWF functionTyped).hasType.2
      argumentTyped ((normal.defeq localsWF).of_l environmentWF localsWF argumentTyped).hasType.2
      functions normal
    exact induction typed next

/-- An actual constant spine, a proof, or finitely many retained eta binders.
The body is itself exposed, so substituting an argument does not require a
new normal-equality search or an assumption about preservation of matching. -/
inductive RigidSpine (environmentWF : environment.WF) (universes : Nat)
    (name : Lean.Name) (levels : List VLevel) : List VExpr → VExpr → List VExpr → Prop where
  | proof {locals : List VExpr}
      (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
      (leftTyped : environment.HasType universes locals left proposition)
      (rightTyped : environment.HasType universes locals
        (applyArguments (.const name levels) arguments) proposition) :
      RigidSpine environmentWF universes name levels locals left arguments
  | spine {locals : List VExpr}
      (typed : environment.HasType universes locals
        (applyArguments (.const name leftLevels) leftArguments) type)
      (heads : @NormalEq (environmentWF.reductionParams universes) locals
        (.const name leftLevels) (.const name levels))
      (argumentsNormal : List.Forall₂
        (@NormalEq (environmentWF.reductionParams universes) locals) leftArguments arguments) :
      RigidSpine environmentWF universes name levels locals
        (applyArguments (.const name leftLevels) leftArguments) arguments
  | lam {locals : List VExpr}
      (functionTyped : environment.HasType universes locals
        (applyArguments (.const name levels) arguments) (.forallE domain bodyType))
      (body : RigidSpine environmentWF universes name levels (domain :: locals) leftBody
        (arguments.map VExpr.lift ++ [.bvar 0])) :
      RigidSpine environmentWF universes name levels locals (.lam domain leftBody) arguments

theorem RigidSpine.normalEq
    (localsWF : OnCtx locals (environment.IsType universes))
    (exposed : RigidSpine environmentWF universes name levels locals left arguments) :
    @NormalEq (environmentWF.reductionParams universes) locals left
      (applyArguments (.const name levels) arguments) := by
  letI := environmentWF.reductionParams universes
  revert localsWF
  induction exposed with
  | proof propositionTyped leftTyped rightTyped => intro _; exact .proofIrrel propositionTyped leftTyped rightTyped
  | spine typed heads argumentsNormal => intro localsWF; exact normal_spine_congr localsWF typed heads argumentsNormal
  | lam functionTyped body induction =>
    intro localsWF
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    apply NormalEq.etaL functionTyped
    simpa only [applyArguments_append, applyArguments, VExpr.lift, applyArguments_liftN,
      VExpr.liftN] using induction (by exact ⟨localsWF, _, domainTyped⟩)

theorem RigidSpine.substDF
    {source target : List VExpr} {leftSubstitution rightSubstitution : VExpr.Subst}
    (targetWF : OnCtx target (environment.IsType universes))
    (substitution : @NormalSubstitution (environmentWF.reductionParams universes)
      target leftSubstitution rightSubstitution source)
    (exposed : RigidSpine environmentWF universes name levels source left arguments) :
    RigidSpine environmentWF universes name levels target (left.subst leftSubstitution)
      (arguments.map (·.subst rightSubstitution)) := by
  letI := environmentWF.reductionParams universes
  induction exposed generalizing target leftSubstitution rightSubstitution with
  | proof propositionTyped leftTyped rightTyped =>
    refine .proof (propositionTyped.subst environmentWF.ordered substitution.typed.left targetWF)
      (leftTyped.subst environmentWF.ordered substitution.typed.left targetWF) ?_
    simpa only [applyArguments_subst, VExpr.subst, Params.univs, WF.reductionParams] using
      (rightTyped.substDF environmentWF.ordered substitution.typed.wf targetWF substitution.typed).hasType.2
  | spine typed heads argumentsNormal =>
    simp only [applyArguments_subst, VExpr.subst]
    have typedSubstituted := typed.subst environmentWF.ordered substitution.typed.left targetWF
    simp only [applyArguments_subst, VExpr.subst] at typedSubstituted
    refine .spine typedSubstituted
      (by simpa only [VExpr.subst] using heads.substDF targetWF substitution) ?_
    clear typed typedSubstituted
    induction argumentsNormal with
    | nil => exact .nil
    | cons normal normals induction => exact .cons (normal.substDF targetWF substitution) induction
  | lam functionTyped body induction =>
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered substitution.typed.wf
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    have substitutedDomain := domainTyped.subst environmentWF.ordered substitution.typed.left targetWF
    have functionSubstituted :=
      (functionTyped.substDF environmentWF.ordered substitution.typed.wf targetWF substitution.typed).hasType.2
    simp only [applyArguments_subst, VExpr.subst] at functionSubstituted
    apply RigidSpine.lam (universes := universes) functionSubstituted
    have bodySubstituted := induction (by exact ⟨targetWF, _, substitutedDomain⟩)
      (substitution.lift targetWF domainTyped)
    simpa only [List.map_append, List.map_cons, List.map_nil, List.map_map,
      VExpr.subst, VExpr.Subst.lift, substituteLift, Function.comp_def] using bodySubstituted

theorem RigidSpine.instDF
    (localsWF : OnCtx locals (environment.IsType universes))
    (domainTyped : environment.HasType universes locals domain (.sort level))
    (argumentTyped : environment.HasType universes locals argument domain)
    (normal : @NormalEq (environmentWF.reductionParams universes) locals argument argument')
    (exposed : RigidSpine environmentWF universes name levels (domain :: locals) left arguments) :
    RigidSpine environmentWF universes name levels locals (left.inst argument)
      (arguments.map (·.inst argument')) := by
  letI := environmentWF.reductionParams universes
  simpa only [VExpr.inst_eq] using exposed.substDF localsWF
    (NormalSubstitution.one localsWF domainTyped argumentTyped normal)

include environmentWF in
private theorem proofApplicationType
    (localsWF : OnCtx locals (environment.IsType universes))
    (propositionTyped : environment.HasType universes locals proposition (.sort .zero))
    (proofTyped : environment.HasType universes locals function proposition)
    (typed : environment.HasType universes locals (.app function argument) type) :
    environment.HasType universes locals type (.sort .zero) := by
  obtain ⟨_, _, functionTyped, argumentTyped⟩ := typed.app_inv environmentWF.ordered localsWF
  have functionProposition := propositionTyped.defeqU_l environmentWF localsWF
    (proofTyped.uniqU environmentWF localsWF functionTyped)
  obtain ⟨⟨domainLevel, domainTyped⟩, bodyLevel, bodyTyped⟩ := functionProposition.forallE_inv environmentWF.ordered
  have levels := ((domainTyped.forallE bodyTyped).uniqU environmentWF localsWF functionProposition).sort_inv
    environmentWF localsWF
  have extendedWF : OnCtx (_ :: locals) (environment.IsType universes) := ⟨localsWF, _, domainTyped⟩
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
  have naturalType := bodyProposition.instN environmentWF.ordered Ctx.InstN.zero argumentTyped
  exact naturalType.defeqU_l environmentWF localsWF
    ((functionTyped.app argumentTyped).uniqU environmentWF localsWF typed)

private theorem normalList_append {relation : VExpr → VExpr → Prop}
    (first : List.Forall₂ relation left right) (second : List.Forall₂ relation left' right') :
    List.Forall₂ relation (left ++ left') (right ++ right') := by
  induction first with
  | nil => exact second
  | cons normal normals induction => exact .cons normal induction

/-- Consume a related argument using an actual beta when an eta binder is
exposed. Simultaneous substitution preserves the entire exposed body. -/
theorem RigidSpine.apply
    (localsWF : OnCtx locals (environment.IsType universes))
    (exposed : RigidSpine environmentWF universes name levels locals function arguments)
    (argumentNormal : @NormalEq (environmentWF.reductionParams universes) locals argument argument')
    (typed : environment.HasType universes locals (.app function argument) type) :
    ∃ result, @ParRedS (environmentWF.reductionParams universes) locals (.app function argument) result ∧
      RigidSpine environmentWF universes name levels locals result (arguments ++ [argument']) := by
  letI := environmentWF.reductionParams universes
  cases exposed with
  | proof propositionTyped leftTyped rightTyped =>
    have normal := normal_spine_congr (arguments := [argument]) (arguments' := [argument']) localsWF typed
      (.proofIrrel propositionTyped leftTyped rightTyped) (.cons argumentNormal .nil)
    have finalTyped := ((normal.defeq localsWF).of_l environmentWF localsWF typed).hasType.2
    exact ⟨_, .rfl, .proof (proofApplicationType (environmentWF := environmentWF) localsWF propositionTyped leftTyped typed) typed
      (by simpa only [applyArguments_append, applyArguments] using finalTyped)⟩
  | spine sourceTyped heads argumentsNormal =>
    refine ⟨_, .rfl, ?_⟩
    simpa only [applyArguments_append, applyArguments] using
      RigidSpine.spine (environmentWF := environmentWF) (type := type)
        (by simpa only [applyArguments_append, applyArguments] using typed)
        heads (normalList_append argumentsNormal (.cons argumentNormal .nil))
  | lam functionTyped body =>
    obtain ⟨_, _, domainTyped, _, argumentTyped⟩ := lambdaArgumentTyped environmentWF localsWF typed
    refine ⟨_, .tail .rfl (.beta .rfl .rfl), ?_⟩
    simpa [List.map_map, Function.comp_def, VExpr.inst_lift, VExpr.inst, VExpr.instVar] using
      body.instDF localsWF domainTyped argumentTyped argumentNormal

include environmentWF in
private theorem spineArgumentsTyped
    {function type : VExpr} {arguments : List VExpr}
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals (applyArguments function arguments) type) :
    ∀ argument ∈ arguments, ∃ argumentType, environment.HasType universes locals argument argumentType := by
  induction arguments generalizing function with
  | nil => simp
  | cons argument arguments induction =>
    obtain ⟨_, applicationTyped⟩ := HasType.spine_head (environmentWF := environmentWF)
      (function := .app function argument) (arguments := arguments) localsWF typed
    obtain ⟨_, _, _, argumentTyped⟩ := applicationTyped.app_inv environmentWF.ordered localsWF
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, argumentTyped⟩
    · exact induction typed value member

theorem RigidSpine.refl
    (localsWF : OnCtx locals (environment.IsType universes))
    (typed : environment.HasType universes locals
      (applyArguments (.const name levels) arguments) type) :
    RigidSpine environmentWF universes name levels locals
      (applyArguments (.const name levels) arguments) arguments := by
  letI := environmentWF.reductionParams universes
  obtain ⟨_, headTyped⟩ := HasType.spine_head (environmentWF := environmentWF) localsWF typed
  refine .spine typed (.refl headTyped) ?_
  have allTyped := spineArgumentsTyped (environmentWF := environmentWF) localsWF typed
  clear typed headTyped
  induction arguments with
  | nil => exact .nil
  | cons argument arguments induction =>
    obtain ⟨_, argumentTyped⟩ := allTyped argument (by simp)
    exact .cons (.refl argumentTyped) (induction fun value member => allTyped value (List.mem_cons_of_mem _ member))

/-- Universal constructive exposure of a normal comparison to a constant
spine. Eta bodies are exposed beneath their retained binders; applied binders
take actual beta steps. No recursive simulation hypothesis is needed. -/
theorem normal_spine_expose
    (localsWF : OnCtx locals (environment.IsType universes))
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left
      (applyArguments (.const name levels) arguments)) :
    ∃ result, @ParRedS (environmentWF.reductionParams universes) locals left result ∧
      RigidSpine environmentWF universes name levels locals result arguments := by
  letI := environmentWF.reductionParams universes
  induction left using VExpr.brecOn generalizing locals name levels arguments with | _ left leftIH => ?_
  revert leftIH
  change let motive := ?_; ∀ _ : left.below (motive := motive), _
  intro motive leftIH
  generalize equation : applyArguments (.const name levels) arguments = right at normal
  cases normal with
  | refl typed =>
    subst equation
    exact ⟨_, .rfl, RigidSpine.refl localsWF typed⟩
  | constDF constantRegistered leftWF rightWF arity levelsEqual =>
    rcases List.eq_nil_or_concat arguments with rfl | ⟨front, argument, rfl⟩
    · cases equation
      exact ⟨_, .rfl, .spine (HasType.const constantRegistered leftWF arity)
        (.constDF constantRegistered leftWF rightWF arity levelsEqual) .nil⟩
    · simp only [List.concat_eq_append, applyArguments_append, applyArguments] at equation
      cases equation

  | @appDF _ function _ _ _ argument _ leftFunction rightFunction leftArgument rightArgument functions argumentsNormal =>
    rcases List.eq_nil_or_concat arguments with rfl | ⟨front, rightLast, rfl⟩
    · cases equation
    · simp only [List.concat_eq_append, applyArguments_append, applyArguments] at equation
      cases equation
      obtain ⟨functionResult, functionSteps, functionExposed⟩ := (leftIH.1.1 localsWF) functions
      have path := functionSteps.app (show ParRedS locals argument argument from .rfl)
      have typed := path.hasType localsWF (leftFunction.app leftArgument)
      obtain ⟨result, applicationSteps, exposed⟩ := functionExposed.apply localsWF argumentsNormal typed
      exact ⟨result, path.trans applicationSteps, by simpa only [List.concat_eq_append] using exposed⟩
  | etaL functionTyped bodies =>
    rename_i domain bodyType leftBody
    subst equation
    obtain ⟨_, typeTyped⟩ := functionTyped.isType environmentWF.ordered localsWF
    obtain ⟨⟨_, domainTyped⟩, _, _⟩ := typeTyped.forallE_inv environmentWF.ordered
    have extendedWF : OnCtx (_ :: locals) (environment.IsType universes) := ⟨localsWF, _, domainTyped⟩
    have bodyNormal : NormalEq (domain :: locals) leftBody
        (applyArguments (.const name levels) (arguments.map VExpr.lift ++ [.bvar 0])) := by
      simpa only [applyArguments_append, applyArguments, VExpr.lift, applyArguments_liftN,
        VExpr.liftN] using bodies
    obtain ⟨bodyResult, bodySteps, exposed⟩ := (leftIH.2.1 extendedWF) bodyNormal
    exact ⟨_, ParRedS.lam .rfl bodySteps, .lam functionTyped exposed⟩
  | proofIrrel propositionTyped leftTyped rightTyped =>
    subst equation
    exact ⟨_, .rfl, .proof propositionTyped leftTyped rightTyped⟩
  | sortDF | lamDF | forallEDF | etaR =>
    rcases List.eq_nil_or_concat arguments with rfl | ⟨front, argument, rfl⟩
    · cases equation
    · simp only [List.concat_eq_append, applyArguments_append, applyArguments] at equation
      cases equation

theorem _root_.Lean4Lean.VEnv.ParRedS.applyArguments
    (path : @ParRedS (environmentWF.reductionParams universes) locals function result)
    (arguments : List VExpr) :
    @ParRedS (environmentWF.reductionParams universes) locals
      (applyArguments function arguments) (applyArguments result arguments) := by
  letI := environmentWF.reductionParams universes
  induction arguments generalizing function result with
  | nil => exact path
  | cons argument arguments induction => exact induction (path.app .rfl)

theorem RigidSpine.applyArguments
    (localsWF : OnCtx locals (environment.IsType universes))
    (exposed : RigidSpine environmentWF universes name levels locals function arguments)
    (argumentsNormal : List.Forall₂
      (@NormalEq (environmentWF.reductionParams universes) locals) pending pending')
    (typed : environment.HasType universes locals (applyArguments function pending) type) :
    ∃ result, @ParRedS (environmentWF.reductionParams universes) locals
        (applyArguments function pending) result ∧
      RigidSpine environmentWF universes name levels locals result (arguments ++ pending') := by
  letI := environmentWF.reductionParams universes
  induction argumentsNormal generalizing function arguments with
  | nil => exact ⟨function, .rfl, by simpa only [List.append_nil] using exposed⟩
  | @cons argument argument' pending pending' normal normals induction =>
    obtain ⟨_, applicationTyped⟩ := HasType.spine_head (environmentWF := environmentWF)
      (function := .app function argument) (arguments := pending) localsWF typed
    obtain ⟨applicationResult, path, next⟩ := exposed.apply localsWF normal applicationTyped
    have lifted := ParRedS.applyArguments path pending
    obtain ⟨result, rest, exposed⟩ := induction next (lifted.hasType localsWF typed)
    exact ⟨result, lifted.trans rest, by simpa only [List.append_assoc, List.singleton_append] using exposed⟩

/-- Expose a rigid comparison beneath any finite list of related arguments.
The path is an ACTUAL original core reduction, and both endpoints keep the
original supplied type. There are no simulation or shape-certificate premises. -/
theorem normal_spine_expose_applications
    (localsWF : OnCtx locals (environment.IsType universes))
    (normal : @NormalEq (environmentWF.reductionParams universes) locals left
      (applyArguments (.const name levels) arguments))
    (argumentsNormal : List.Forall₂
      (@NormalEq (environmentWF.reductionParams universes) locals) pending pending')
    (typed : environment.HasType universes locals (applyArguments left pending) type) :
    ∃ result, @ParRedS (environmentWF.reductionParams universes) locals
        (applyArguments left pending) result ∧
      RigidSpine environmentWF universes name levels locals result (arguments ++ pending') ∧
      @NormalEq (environmentWF.reductionParams universes) locals result
        (applyArguments (.const name levels) (arguments ++ pending')) ∧
      environment.HasType universes locals result type ∧
      environment.HasType universes locals
        (applyArguments (.const name levels) (arguments ++ pending')) type := by
  letI := environmentWF.reductionParams universes
  obtain ⟨functionResult, functionPath, exposed⟩ := normal_spine_expose localsWF normal
  have initial := ParRedS.applyArguments functionPath pending
  obtain ⟨result, applicationPath, final⟩ := exposed.applyArguments localsWF argumentsNormal
    (initial.hasType localsWF typed)
  have path : ParRedS locals (applyArguments left pending) result := initial.trans applicationPath
  have resultTyped := path.hasType localsWF typed
  have finalNormal := final.normalEq localsWF
  exact ⟨result, path, final, finalNormal, resultTyped,
    ((finalNormal.defeq localsWF).of_l environmentWF localsWF resultTyped).hasType.2⟩

end Lean4Lean.VEnv.QuotPropReduction
