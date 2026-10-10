import Lean4Lean.Verify.RestrictedContext

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker

namespace RestrictedContext

def RunWF {safety : DefinitionSafety} {env : Kernel.Environment} {venv : VEnv}
    (context : RestrictedContext safety env venv) (methods : Methods) (valid : State → Prop)
    (action : RecM Result) (post : Result → Prop) : Prop :=
  ∀ initial, valid initial → (action methods context.toContext initial).WF fun returned =>
    valid returned.2 ∧ post returned.1

theorem RunWF.pure {context : RestrictedContext safety env venv}
    {methods : Methods}
    {valid : State → Prop} {post : Result → Prop} (accepted : post result) :
    context.RunWF methods valid (pure result) post := by
  intro initial initialValid returned success
  cases success
  exact ⟨initialValid, accepted⟩

theorem RunWF.throw {context : RestrictedContext safety env venv}
    {methods : Methods}
    {valid : State → Prop} {post : Result → Prop} :
    context.RunWF methods valid (throw exception) post := by
  intro initial initialValid returned success
  cases success

theorem RunWF.bind {context : RestrictedContext safety env venv}
    {methods : Methods}
    {valid : State → Prop} {first : RecM Input} {next : Input → RecM Result}
    {intermediate : Input → Prop} {post : Result → Prop}
    (firstWF : context.RunWF methods valid first intermediate)
    (nextWF : ∀ result, intermediate result → context.RunWF methods valid (next result) post) :
    context.RunWF methods valid (first >>= next) post := by
  intro initial initialValid returned success
  change ((first methods context.toContext initial).bind fun middle =>
    next middle.1 methods context.toContext middle.2) = .ok returned at success
  cases firstSuccess : first methods context.toContext initial with
  | error exception =>
    simp only [firstSuccess, Except.bind] at success
    cases success
  | ok middle =>
    obtain ⟨middleValid, middlePost⟩ := firstWF initial initialValid middle firstSuccess
    exact nextWF middle.1 middlePost middle.2 middleValid returned (by simpa [firstSuccess] using success)

theorem RunWF.mono {context : RestrictedContext safety env venv}
    {methods : Methods}
    {valid : State → Prop} {action : RecM Result} {post stronger : Result → Prop}
    (actionWF : context.RunWF methods valid action post) (implication : ∀ result, post result → stronger result) :
    context.RunWF methods valid action stronger := by
  intro initial initialValid returned success
  obtain ⟨finalValid, finalPost⟩ := actionWF initial initialValid returned success
  exact ⟨finalValid, implication returned.1 finalPost⟩

structure ApplicationMethods {safety : DefinitionSafety} {env : Kernel.Environment} {venv : VEnv}
    (context : RestrictedContext safety env venv) (methods : Methods) (valid : State → Prop) : Prop where
  whnf : ∀ {expression semantic}, TrExprS venv context.lparams context.scope expression semantic →
    context.RunWF methods valid (Inner.whnf expression) fun result =>
      FVarsBelow context.scope expression result ∧ TrExpr venv context.lparams context.scope result semantic
  inferType : ∀ {expression semantic}, TrExprS venv context.lparams context.scope expression semantic →
    context.RunWF methods valid (Inner.inferType expression true) fun result =>
      ∃ type, TrTyping venv context.lparams context.scope expression result semantic type

theorem ensureForall {context : RestrictedContext safety env venv}
    {methods : Methods} {valid : State → Prop}
    (contracts : context.ApplicationMethods methods valid)
    (translated : TrExpr venv context.lparams context.scope expression semantic) :
    context.RunWF methods valid (Inner.ensureForallCore expression source) fun result =>
      FVarsBelow context.scope expression result ∧ TrExpr venv context.lparams context.scope result semantic ∧
        ∃ name domain body binder, result = .forallE name domain body binder := by
  obtain ⟨model, strict, equal⟩ := translated
  simp [Inner.ensureForallCore]
  split
  · let .forallE .. := expression
    exact .pure ⟨.rfl, ⟨model, strict, equal⟩, _, _, _, _, rfl⟩
  · refine (contracts.whnf strict).bind fun result ⟨below, resultTr⟩ => ?_
    split
    · let .forallE .. := result
      exact .pure ⟨below, resultTr.defeq context.checker.wf context.scope_wf equal,
        _, _, _, _, rfl⟩
    · intro initial initialValid returned success
      cases success

theorem inferAppLoop {context : RestrictedContext safety env venv}
    {methods : Methods} {valid : State → Prop}
    (contracts : context.ApplicationMethods methods valid)
    {previous delayed remaining : List Expr}
    (stack : AppStack venv context.lparams context.scope (.mkAppRevList head delayed) semantic remaining)
    (below : FVarsBelow context.scope head functionType)
    (typeTr : TrExpr venv context.lparams context.scope (functionType.instantiateList delayed) semanticType)
    (typed : venv.HasType context.lparams.length context.scope.toCtx semantic semanticType)
    (arguments : args = previous ++ delayed.reverse ++ remaining)
    (start : first = previous.length) (position : index = previous.length + delayed.length) :
    context.RunWF methods valid (Inner.inferApp.loop source ⟨args⟩ functionType first index) fun result =>
      ∃ model type, TrTyping venv context.lparams context.scope
        (head.mkAppRevList delayed |>.mkAppList remaining) result model type := by
  subst index first
  rw [Inner.inferApp.loop.eq_def]
  have closed := Expr.mkAppRevList_args_noLooseBVars head delayed
    (context.noBV ▸ stack.tr.closed).looseBVarRange_zero
  have many (expression : Expr) (depth : Nat) :=
    Expr.instantiateMany_eq_instantiateList expression delayed depth closed
  simp [arguments]
  have envWF := context.checker.wf
  have scopeWF := context.scope_wf
  cases remaining with simp
  | cons argument remaining =>
    let .app functionTyped argumentTyped functionTr argumentTr stack := stack
    have typeEqual := functionTyped.uniqU envWF scopeWF typed
    split
    · rw [Expr.instantiateList_forallE] at typeTr
      let ⟨_, .forallE _ _ domainTr bodyTr, equality⟩ := typeTr
      have ⟨⟨_, domainEqual⟩, _, bodyEqual⟩ :=
        equality.trans envWF scopeWF typeEqual.symm |>.forallE_inv envWF scopeWF
      refine inferAppLoop contracts (delayed := argument :: delayed) stack ?_ ?_
        (.app functionTyped argumentTyped) (by simp) rfl rfl
      · exact fun _ upward supported => (below _ upward supported).2
      have argumentClosed := context.noBV ▸ argumentTr.closed
      simp [← Expr.instantiateList_instantiate1_comm argumentClosed.looseBVarRange_zero]
      exact .inst envWF scopeWF (argumentTyped.defeqU_r envWF scopeWF ⟨_, domainEqual.symm⟩)
        ⟨_, bodyTr, _, bodyEqual⟩ (argumentTr.trExpr envWF scopeWF)
    · simp [Nat.add_sub_cancel_left, many]
      refine (ensureForall contracts typeTr).bind fun _ ⟨normalizedBelow, ⟨_, normalizedTr, equality⟩, shape⟩ => ?_
      obtain ⟨name, domain, body, binder, rfl⟩ := shape
      simp [Expr.bindingBody!]
      let .forallE _ _ domainTr bodyTr := normalizedTr
      have ⟨⟨_, domainEqual⟩, _, bodyEqual⟩ :=
        equality.trans envWF scopeWF typeEqual.symm |>.forallE_inv envWF scopeWF
      refine inferAppLoop contracts (previous := previous ++ delayed.reverse) (delayed := [argument])
        stack ?_ ?_ (.app functionTyped argumentTyped) (by simp) (by simp) (by simp)
      · intro _ upward supported
        have ⟨headSupported, delayedSupported⟩ := FVarsIn.appRevList.1 supported
        exact (normalizedBelow _ upward <| (below _ upward headSupported).instantiateList delayedSupported).2
      exact .inst envWF scopeWF (argumentTyped.defeqU_r envWF scopeWF ⟨_, domainEqual.symm⟩)
        ⟨_, bodyTr, _, bodyEqual⟩ (argumentTr.trExpr envWF scopeWF)
  | nil =>
    rw [← List.length_reverse, List.take_length]
    simp only [List.reverse_reverse, many]
    have ⟨_, typeTr, equality⟩ := typeTr
    refine .pure ⟨_, _, fun _ upward supported => ?_, stack.tr, typeTr,
      typed.defeqU_r envWF scopeWF equality.symm⟩
    have ⟨headSupported, delayedSupported⟩ := FVarsIn.appRevList.1 supported
    exact (below _ upward headSupported).instantiateList delayedSupported

theorem inferApp {context : RestrictedContext safety env venv}
    {methods : Methods} {valid : State → Prop}
    (contracts : context.ApplicationMethods methods valid)
    (translated : TrExprS venv context.lparams context.scope expression semantic) :
    context.RunWF methods valid (Inner.inferApp expression) fun result =>
      ∃ type, TrTyping venv context.lparams context.scope expression result semantic type := by
  rw [Inner.inferApp, Expr.withApp_eq, Expr.getAppArgs_eq]
  obtain ⟨_, stack⟩ := AppStack.build <| expression.mkAppList_getAppArgsList ▸ translated
  refine (contracts.inferType stack.tr).bind fun result ⟨type, below, _, typeTr, typed⟩ => ?_
  have envWF := context.checker.wf
  have scopeWF := context.scope_wf
  refine (inferAppLoop contracts (previous := []) (delayed := []) stack below
    (typeTr.trExpr envWF scopeWF) typed rfl rfl rfl).mono fun _ ⟨_, _, below, resultTr, typeTr, typed⟩ => ?_
  have equal := (expression.mkAppList_getAppArgsList ▸ resultTr).uniq envWF (.refl envWF scopeWF) translated
  exact ⟨_, expression.mkAppList_getAppArgsList ▸ below, translated, typeTr,
    typed.defeqU_l envWF scopeWF equal⟩

end RestrictedContext
end Lean4Lean
