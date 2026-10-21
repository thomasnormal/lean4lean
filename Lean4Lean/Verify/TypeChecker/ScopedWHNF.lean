import Lean4Lean.Verify.TypeChecker.HeadScope
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.InductiveParameterPrefixReplacement

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open TypeChecker

theorem TypeChecker.VState.WF.headCacheNames {context : VContext} {state : VState}
    (valid : state.WF context) : HeadCacheNamesWF state.toState :=
  ⟨fun _ _ found => (valid.whnfCore_wf found).2.2.2.1,
    fun _ _ found => (valid.whnf_wf found).2.2.2.1⟩

theorem TypeChecker.VState.WF.localNames {context : VContext} {state : VState}
    (valid : state.WF context) : NativeLocalNamesWF context.lctx' state.ngen := by
  intro declaration member
  apply valid.ngen_wf
  rw [← context.trlctx.fvars_eq]
  exact List.mem_map.mpr ⟨declaration, member, rfl⟩

def TypeChecker.M.ScopeWF (context : VContext) (state : VState) (action : M Result)
    (post : Result → VState → Prop) : Prop :=
  HeadScopeCacheWF context.lctx' state.toState →
    action.WF context state (fun result finalState =>
      HeadScopeCacheWF context.lctx' finalState.toState ∧ post result finalState)

structure TypeChecker.Methods.ScopeWF (methods : Methods) : Prop where
  base : methods.WF
  whnfCore : context.TrExprS expression translated →
    (methods.whnfCore expression cheapProj).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized translated ∧
      NativeHeadScoped context.lctx' normalized
  whnf : context.TrExprS expression translated →
    (methods.whnf expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized translated ∧
      NativeHeadScoped context.lctx' normalized
  inferType : expression.FVarsIn (· ∈ context.vlctx.fvars) →
    (inferOnly = true → ∃ translated, context.TrExprS expression translated) →
    (methods.inferType expression inferOnly).ScopeWF context state fun type _ =>
      ∃ translated semanticType, context.TrTyping expression type translated semanticType
  isDefEqCore : context.TrExprS first firstSemantic → context.TrExprS second secondSemantic →
    (methods.isDefEqCore first second).ScopeWF context state fun equal _ =>
      equal → context.IsDefEqU firstSemantic secondSemantic

def TypeChecker.RecM.ScopeWF (context : VContext) (state : VState) (action : RecM Result)
    (post : Result → VState → Prop) : Prop :=
  ∀ methods, methods.ScopeWF → (action methods).ScopeWF context state post

theorem TypeChecker.RecM.ScopeWF.pure {context : VContext} {state : VState}
    {result : Result} {post : Result → VState → Prop} (valid : post result state) :
    (pure result : RecM Result).ScopeWF context state post :=
  fun _ _ caches => M.WF.pure ⟨caches, valid⟩

theorem TypeChecker.RecM.ScopeWF.bind {context : VContext} {state : VState}
    {action : RecM First} {continuation : First → RecM Result} {post finalPost}
    (initial : action.ScopeWF context state post)
    (next : ∀ first middleState, state ≤ middleState → post first middleState →
      (continuation first).ScopeWF context middleState finalPost) :
    (action >>= continuation).ScopeWF context state finalPost := by
  intro methods valid caches
  exact (initial methods valid caches).bind fun first middleState increasing intermediate =>
    next first middleState increasing intermediate.2 methods valid intermediate.1

theorem TypeChecker.RecM.ScopeWF.mono {context : VContext} {state : VState}
    {action : RecM Result} {post finalPost}
    (valid : action.ScopeWF context state post)
    (implication : ∀ result finalState, state ≤ finalState → post result finalState → finalPost result finalState) :
    action.ScopeWF context state finalPost := by
  intro methods callbacks caches
  exact (valid methods callbacks caches).mono fun result finalState increasing final =>
    ⟨final.1, implication result finalState increasing final.2⟩

theorem TypeChecker.RecM.ScopeWF.throw {context : VContext} {state : VState} {error : Exception} {post} :
    (throw error : RecM Result).ScopeWF context state post := fun _ _ _ => M.WF.throw

theorem TypeChecker.RecM.ScopeWF.of_rejects {context : VContext} {state : VState}
    {action : RecM Result} {post : Result → VState → Prop}
    (rejected : action.WF context state (fun _ _ => False)) :
    action.ScopeWF context state post := by
  intro methods valid caches
  exact (rejected methods valid.base).mono fun _ _ _ impossible => impossible.elim

theorem TypeChecker.RecM.ScopeWF.get {context : VContext} {state : VState}
    {continuation : State → RecM Result} {post}
    (valid : (continuation state.toState).ScopeWF context state post) :
    (get >>= continuation).ScopeWF context state post := fun methods callbacks => valid methods callbacks

theorem TypeChecker.RecM.ScopeWF.getEnv {context : VContext} {state : VState}
    {continuation : Environment → RecM Result} {post}
    (valid : (continuation context.env).ScopeWF context state post) :
    ((liftM TypeChecker.getEnv : RecM Environment) >>= continuation).ScopeWF context state post :=
  fun methods callbacks => valid methods callbacks

theorem TypeChecker.RecM.ScopeWF.getLCtx {context : VContext} {state : VState}
    {continuation : LocalContext → RecM Result} {post}
    (valid : (continuation context.lctx').ScopeWF context state post) :
    (getLCtx >>= continuation).ScopeWF context state post := by
  intro methods callbacks caches
  change M.WF context state ((Lean.getLCtx : M LocalContext) >>= fun locals => continuation locals methods) _
  exact (TypeChecker.getLCtx.WF (c := context) (s := state)).bind fun _ _ _ equal => by
    rcases equal with ⟨rfl, rfl⟩
    exact valid methods callbacks caches

theorem TypeChecker.RecM.ScopeWF.readThe {context : VContext} {state : VState}
    {continuation : Context → RecM Result} {post}
    (valid : (continuation context.toContext).ScopeWF context state post) :
    (readThe Context >>= continuation).ScopeWF context state post := fun methods callbacks => valid methods callbacks

theorem TypeChecker.RecM.ScopeWF.stateWF {context : VContext} {state : VState}
    {action : RecM Result} {post}
    (valid : state.WF context → action.ScopeWF context state post) :
    action.ScopeWF context state post := fun methods callbacks caches wellFormed =>
  valid wellFormed methods callbacks caches wellFormed

theorem TypeChecker.RecM.ScopeWF.cacheWF {context : VContext} {state : VState}
    {action : RecM Result} {post}
    (valid : HeadScopeCacheWF context.lctx' state.toState → action.ScopeWF context state post) :
    action.ScopeWF context state post := fun methods callbacks caches => valid caches methods callbacks caches

theorem TypeChecker.RecM.ScopeWF.pureBind {context : VContext} {state : VState}
    {continuation : First → RecM Result} {first : First} {post}
    (valid : (continuation first).ScopeWF context state post) :
    ((Pure.pure first : RecM First) >>= continuation).ScopeWF context state post := valid

theorem TypeChecker.RecM.ScopeWF.liftExcept {context : VContext} {state : VState}
    {action : Except Exception Result} {post : Result → Prop} (valid : action.WF post) :
    (liftM action : RecM Result).ScopeWF context state (fun result _ => post result) := by
  intro methods callbacks caches wellFormed result finalState accepted
  change (action >>= fun actual => Except.ok (actual, state.toState)) = .ok (result, finalState) at accepted
  cases evaluated : action with
  | error error => simp [evaluated, Bind.bind, Except.bind] at accepted
  | ok actual =>
    simp only [evaluated, Bind.bind, Except.bind] at accepted
    cases accepted
    exact ⟨state, rfl, .rfl, wellFormed, caches, valid _ evaluated⟩

theorem TypeChecker.RecM.ScopeWF.andWF {context : VContext} {state : VState}
    {action : RecM Result} {post semanticPost}
    (scopes : action.ScopeWF context state post) (semantics : action.WF context state semanticPost) :
    action.ScopeWF context state (fun result finalState => post result finalState ∧ semanticPost result finalState) := by
  intro methods callbacks caches wellFormed result finalState accepted
  obtain ⟨scopedState, scopedEqual, increasing, scopedWellFormed, scopedCaches, scopedPost⟩ :=
    scopes methods callbacks caches wellFormed result finalState accepted
  obtain ⟨semanticState, semanticEqual, _, _, semanticResult⟩ :=
    semantics methods callbacks.base wellFormed result finalState accepted
  have equal : scopedState = semanticState := by
    cases scopedState
    cases semanticState
    cases scopedEqual.trans semanticEqual.symm
    rfl
  subst semanticState
  exact ⟨scopedState, scopedEqual, increasing, scopedWellFormed, scopedCaches, scopedPost, semanticResult⟩

theorem NativeHeadScoped.ofNotFVar {locals : LocalContext} {expression : Expr}
    (clean : NativeHeadClean expression) (notFVar : expression.isFVar = false) :
    NativeHeadScoped locals expression := by
  refine ⟨clean, fun identifier equal => ?_⟩
  subst expression
  cases notFVar

theorem TypeChecker.RecM.ScopeWF.fromHeadScopeWF {context : VContext} {state : VState}
    {action : RecM Result} {post}
    (semantics : action.WF context state post)
    (native : ∀ methods, (action methods).HeadScopeWF) : action.ScopeWF context state post := by
  intro methods callbacks caches wellFormed result finalState accepted
  obtain ⟨semanticState, equal, increasing, semanticWellFormed, semanticPost⟩ :=
    semantics methods callbacks.base wellFormed result finalState accepted
  have final := native methods context.toContext state.toState
    (context.lctx_eq ▸ context.trlctx.1) (context.lctx_eq ▸ wellFormed.localNames)
    (context.lctx_eq ▸ caches) wellFormed.headCacheNames result finalState accepted
  have finalCaches := final.2.1
  rw [← context.lctx_eq, ← equal] at finalCaches
  exact ⟨semanticState, equal, increasing, semanticWellFormed, finalCaches, semanticPost⟩

theorem TypeChecker.Inner.addEquiv.scopeWF {context : VContext} {state : VState}
    {first second : Expr} {semantic : VExpr}
    (firstTranslation : context.TrExprS first semantic)
    (secondTranslation : context.TrExpr second semantic) :
    (modify fun st => { st with eqvManager := st.eqvManager.addEquiv first second } : RecM Unit).ScopeWF
      context state (fun _ _ => True) := by
  intro methods callbacks caches
  rintro wellFormed _ _ ⟨⟩
  let ⟨_, _, levelsWF, contextLift, managerWF, reserved⟩ := wellFormed.ectx
  refine ⟨{ state with toState := _ }, rfl, .rfl,
    { wellFormed with ectx := ⟨_, _, levelsWF, contextLift, ?_, reserved⟩ }, ?_⟩
  · simp [EquivManager.addEquiv]
    split
    · rename_i firstNode
      split
      · rename_i secondNode
        have ⟨managerWF, firstNodeMap, firstNodeEquiv⟩ :=
          EquivManager.toNode.WF managerWF firstNode
        have ⟨managerWF, secondNodeMap, secondNodeEquiv⟩ :=
          EquivManager.toNode.WF managerWF secondNode
        refine (EquivManager.merge.WF managerWF ?_ (secondNodeMap.toNodeMap firstNodeEquiv)
          secondNodeEquiv).1
        exact .defeq (firstTranslation.weakFV' context.Ewf contextLift levelsWF)
          (secondTranslation.weakFV' context.Ewf contextLift levelsWF)
  · constructor
    · exact caches
    · trivial

theorem TypeChecker.Inner.isDefEqCore.scopeWF {context : VContext} {state : VState}
    {first second : Expr} {firstSemantic secondSemantic : VExpr}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEqCore first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) := by
  intro methods callbacks
  exact callbacks.isDefEqCore firstTranslation secondTranslation

theorem TypeChecker.Inner.isDefEq.scopeWF {context : VContext} {state : VState}
    {first second : Expr} {firstSemantic secondSemantic : VExpr}
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (isDefEq first second).ScopeWF context state
      (fun equal _ => equal → context.IsDefEqU firstSemantic secondSemantic) := by
  unfold isDefEq
  refine (isDefEqCore.scopeWF firstTranslation secondTranslation).bind fun equal _ _ equalProof => ?_
  split
  · refine (addEquiv.scopeWF firstTranslation
      ⟨_, secondTranslation, (equalProof ‹_›).symm⟩).bind fun _ _ _ _ => ?_
    exact RecM.ScopeWF.pure equalProof
  · exact RecM.ScopeWF.pure equalProof

theorem TypeChecker.Inner.unfoldDefinition.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.unfoldDefinition expression).ScopeWF context state fun result _ =>
      UnfoldDefinition.WF context expression expression.getAppFn semantic result :=
  RecM.ScopeWF.fromHeadScopeWF (Inner.unfoldDefinition.WF translated)
    (Inner.unfoldDefinition.headScopeWF expression)

theorem TypeChecker.Inner.whnfCore.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.whnfCore expression cheapProj).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized := fun _ valid => valid.whnfCore translated

theorem TypeChecker.Inner.whnf.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.whnf expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized := fun _ valid => valid.whnf translated

theorem TypeChecker.Methods.withFuel.zero_scopeWF : (withFuel 0).ScopeWF := by
  constructor
  · constructor <;> intros <;> exact M.WF.throw
  all_goals intros; intro caches; exact M.WF.throw

private theorem AppStack.translatedArgument
    (stack : AppStack environment levels locals function functionSemantic arguments)
    (member : argument ∈ arguments) :
    ∃ semantic, TrExprS environment levels locals argument semantic := by
  induction stack generalizing argument with
  | head => cases member
  | app functionTyping argumentTyping functionTranslation argumentTranslation tail inductionHypothesis =>
    rcases List.mem_cons.mp member with same | remaining
    · subst argument
      exact ⟨_, argumentTranslation⟩
    · exact inductionHypothesis remaining

private theorem translatedApplicationArgument {context : VContext}
    (translated : context.TrExprS expression semantic)
    (bound : position < expression.getAppArgs.size) :
    ∃ result, context.TrExprS expression.getAppArgs[position] result := by
  obtain ⟨_, stack⟩ := AppStack.build (expression.mkAppList_getAppArgsList ▸ translated)
  apply stack.translatedArgument
  rw [← Expr.getAppArgs_toList]
  exact Array.mem_toList_iff.mpr (Array.getElem_mem bound)

theorem quotReduceRec.scopeFrame {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (quotReduceRec expression Inner.whnf).ScopeWF context state (fun _ _ => True) := by
  unfold quotReduceRec
  cases expression.getAppFn <;> try exact RecM.ScopeWF.pure trivial
  dsimp only
  have continuation (constructorPosition argumentPosition : Nat) :
      (do
        let arguments := expression.getAppArgs
        if bound : constructorPosition < arguments.size then
          let constructor ← Inner.whnf arguments[constructorPosition]
          if !constructor.isAppOfArity ``Quot.mk 3 then return none
          let result := Expr.app arguments[argumentPosition]! constructor.appArg!
          let arity := constructorPosition + 1
          if arity < arguments.size then
            return some (mkAppRange result arity arguments.size arguments)
          else return some result
        else return none).ScopeWF context state (fun _ _ => True) := by
    dsimp only
    split
    ·
      obtain ⟨_, argumentTranslation⟩ := translatedApplicationArgument translated ‹_›
      refine (Inner.whnf.scopeWF argumentTranslation).bind fun constructor _ _ _ => ?_
      split
      · exact RecM.ScopeWF.pure trivial
      · split <;> exact RecM.ScopeWF.pure trivial
    · exact RecM.ScopeWF.pure trivial
  split
  · exact continuation 5 3
  · split
    · exact continuation 4 3
    · exact RecM.ScopeWF.pure trivial

theorem TypeChecker.Inner.reduceRecursor.scopeFrame {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.reduceRecursor expression).ScopeWF context state (fun _ _ => True) := by
  unfold Inner.reduceRecursor
  refine RecM.ScopeWF.getEnv ?_
  have inductiveFrame {state : VState} : (do
      if let some reduced ← inductiveReduceRec context.env expression
          (fun current => Inner.whnf current)
          Inner.inferType Inner.isDefEq then return some reduced
      return none).ScopeWF context state (fun _ _ => True) := by
    rw [inductiveReduceRec.eq_none translated]
    exact RecM.ScopeWF.pureBind (RecM.ScopeWF.pure trivial)
  split
  · refine (quotReduceRec.scopeFrame translated).bind fun reduced _ _ _ => ?_
    cases reduced
    · exact inductiveFrame
    · exact RecM.ScopeWF.pure trivial
  · exact inductiveFrame

theorem TypeChecker.Inner.nativeProjectionFailure.scopeWF {context : VContext} {state : VState}
    {resultType : Type} {post : resultType → VState → Prop}
    (environment : Kernel.Environment) (source : Expr) :
    (nativeProjectionFailure (resultType := resultType) environment source).ScopeWF context state
      post := by
  unfold nativeProjectionFailure
  exact RecM.ScopeWF.getLCtx RecM.ScopeWF.throw

theorem TypeChecker.Inner.nativeProjectionParameter.scopeWF {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (arguments : Array Expr) (index : Nat)
    (current : Expr) (translated : context.TrExprS current semantic) :
    (nativeProjectionParameter environment source arguments index current).ScopeWF context state
      (fun _ _ => True) := by
  unfold nativeProjectionParameter
  dsimp only [Bind.bind, ReaderT.bind]
  refine (Inner.whnf.scopeWF translated).bind fun normalized _ _ _ => ?_
  cases normalized <;> try exact nativeProjectionFailure.scopeWF environment source
  exact RecM.ScopeWF.pure (result := ForInStep.yield _) trivial

theorem TypeChecker.RecM.forInList_scopeWF {context : VContext} {state : VState}
    (elements : List Element) (initial : Value)
    (body : Element → Value → TypeChecker.RecM (ForInStep Value))
    (framed : ∀ {state : VState} element value,
      (body element value).ScopeWF context state (fun _ _ => True)) :
    (forIn elements initial body).ScopeWF context state (fun _ _ => True) := by
  induction elements generalizing state initial with
  | nil => exact RecM.ScopeWF.pure trivial
  | cons element elements inductionHypothesis =>
    rw [List.forIn_cons]
    refine (framed element initial).bind fun step middleState _ _ => ?_
    cases step
    · exact RecM.ScopeWF.pure trivial
    · exact inductionHypothesis (state := middleState) _

theorem TypeChecker.RecM.forInRange_scopeWF {context : VContext} {state : VState}
    (range : Std.Legacy.Range) (initial : Value)
    (body : Nat → Value → TypeChecker.RecM (ForInStep Value))
    (framed : ∀ {state : VState} index value,
      (body index value).ScopeWF context state (fun _ _ => True)) :
    (forIn range initial body).ScopeWF context state (fun _ _ => True) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList_scopeWF _ _ _ framed

theorem TypeChecker.Inner.nativeProjectionParameter.typed_scopeWF
    {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (arguments : Array Expr) (index : Nat)
    {current replacement : Expr} {domain codomain argument : VExpr}
    (translated : context.TrExpr current (.forallE domain codomain))
    (argumentTranslation : context.TrExprS replacement argument)
    (argumentTyping : context.HasType argument domain)
    (selected : arguments[index]! = replacement) :
    (nativeProjectionParameter environment source arguments index current).ScopeWF context state
      (fun step _ => ∃ next, step = .yield next ∧ context.TrExpr next (codomain.inst argument)) := by
  unfold nativeProjectionParameter
  dsimp only [Bind.bind, ReaderT.bind]
  obtain ⟨_, currentTranslation, currentEquality⟩ := translated
  refine (Inner.whnf.scopeWF currentTranslation).bind fun normalized _ _ normalizedWF => ?_
  cases normalized <;> try exact nativeProjectionFailure.scopeWF environment source
  let ⟨_, forallTranslation, normalizedEquality⟩ := normalizedWF.2.1
  let .forallE _ _ domainTranslation bodyTranslation := forallTranslation
  have forallEquality := normalizedEquality.trans context.Ewf context.Δwf currentEquality
  have ⟨⟨_, domainEquality⟩, _, bodyEquality⟩ :=
    forallEquality.forallE_inv context.Ewf context.Δwf
  have instantiated := TrExpr.inst context.Ewf context.Δwf
    (argumentTyping.defeqU_r context.Ewf context.Δwf ⟨_, domainEquality.symm⟩)
    ⟨_, bodyTranslation, _, bodyEquality⟩
    (argumentTranslation.trExpr context.Ewf context.Δwf)
  dsimp only
  rw [selected, Expr.instantiate1_eq]
  exact RecM.ScopeWF.pure ⟨_, rfl, instantiated⟩

theorem TypeChecker.Inner.nativeProjectionParameters.loop_scopeWF
    {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (arguments : Array Expr)
    {initial : Expr} {semantic result : VExpr} {replacements : List Expr} {semantics : List VExpr}
    (typed : ElimNestedInductive.TypedParameterArguments context.venv context.lparams context.mlctx
      semantic replacements semantics result)
    (translated : context.TrExpr initial semantic) (preceding suffix : List Expr)
    (aligned : arguments.toList = preceding ++ replacements ++ suffix) :
    (forIn (List.range' preceding.length replacements.length) initial
      (nativeProjectionParameter environment source arguments)).ScopeWF context state
      (fun final _ => context.TrExpr final result) := by
  induction typed generalizing state initial preceding with
  | nil => exact RecM.ScopeWF.pure translated
  | @cons replacement argument domain codomain replacements semantics result
      argumentTranslation argumentTyping remaining inductionHypothesis =>
    have selected : arguments[preceding.length]! = replacement := by
      have bound : preceding.length < arguments.size := by
        have lengths := congrArg List.length aligned
        simp only [Array.length_toList, List.length_append, List.length_cons] at lengths
        omega
      simp [getElem!_pos, bound, ← Array.getElem_toList, aligned]
    rw [List.length_cons, List.range'_succ, List.forIn_cons]
    refine (nativeProjectionParameter.typed_scopeWF environment source arguments preceding.length
      translated argumentTranslation argumentTyping selected).bind fun step middleState _ stepWF => ?_
    obtain ⟨next, rfl, nextTranslation⟩ := stepWF
    simpa only [List.length_append, List.length_singleton] using
      inductionHypothesis (state := middleState) nextTranslation (preceding ++ [replacement])
        (by simpa [List.append_assoc] using aligned)

theorem TypeChecker.Inner.nativeProjectionParameters.scopeWF {context : VContext} {state : VState}
    (environment : Kernel.Environment) (source : Expr) (arguments : Array Expr) (parameters : Nat)
    {initial : Expr} {semantic result : VExpr} {replacements : List Expr} {semantics : List VExpr}
    (typed : ElimNestedInductive.TypedParameterArguments context.venv context.lparams context.mlctx
      semantic replacements semantics result)
    (translated : context.TrExpr initial semantic) (suffix : List Expr)
    (aligned : arguments.toList = replacements ++ suffix) (count : replacements.length = parameters) :
    (nativeProjectionParameters environment source arguments parameters initial).ScopeWF context state
      (fun final _ => context.TrExpr final result) := by
  unfold nativeProjectionParameters
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa [← count] using nativeProjectionParameters.loop_scopeWF environment source arguments
    typed translated [] suffix aligned

def NativeOptionalHeadScoped (locals : LocalContext) : Option Expr → Prop
  | none => True
  | some expression => NativeHeadScoped locals expression

theorem TypeChecker.Inner.reduceBinNatOp.scopeHeadWF {context : VContext} {state : VState}
    (operation : Nat → Nat → Nat) (first : context.TrExprS firstExpression firstSemantic)
    (second : context.TrExprS secondExpression secondSemantic) :
    (Inner.reduceBinNatOp operation firstExpression secondExpression).ScopeWF context state
      (fun result _ => NativeOptionalHeadScoped context.lctx' result) := by
  unfold Inner.reduceBinNatOp
  refine (Inner.whnf.scopeWF first).bind fun normalized _ _ _ => ?_
  cases Inner.rawNatLitExt? normalized
  · exact RecM.ScopeWF.pure trivial
  · refine (Inner.whnf.scopeWF second).bind fun normalized _ _ _ => ?_
    cases Inner.rawNatLitExt? normalized
    · exact RecM.ScopeWF.pure trivial
    · exact RecM.ScopeWF.pure (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)

theorem TypeChecker.Inner.reducePow.scopeHeadWF {context : VContext} {state : VState}
    (first : context.TrExprS firstExpression firstSemantic)
    (second : context.TrExprS secondExpression secondSemantic) :
    (Inner.reducePow firstExpression secondExpression).ScopeWF context state
      (fun result _ => NativeOptionalHeadScoped context.lctx' result) := by
  unfold Inner.reducePow
  refine (Inner.whnf.scopeWF first).bind fun normalized _ _ _ => ?_
  cases Inner.rawNatLitExt? normalized
  · exact RecM.ScopeWF.pure trivial
  · refine (Inner.whnf.scopeWF second).bind fun normalized _ _ _ => ?_
    cases Inner.rawNatLitExt? normalized
    · exact RecM.ScopeWF.pure trivial
    · dsimp only
      split
      · exact RecM.ScopeWF.pure trivial
      · exact RecM.ScopeWF.pure (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)

theorem TypeChecker.Inner.reduceBinNatPred.scopeHeadWF {context : VContext} {state : VState}
    (operation : Nat → Nat → Bool) (first : context.TrExprS firstExpression firstSemantic)
    (second : context.TrExprS secondExpression secondSemantic) :
    (Inner.reduceBinNatPred operation firstExpression secondExpression).ScopeWF context state
      (fun result _ => NativeOptionalHeadScoped context.lctx' result) := by
  unfold Inner.reduceBinNatPred
  refine (Inner.whnf.scopeWF first).bind fun normalized _ _ _ => ?_
  cases Inner.rawNatLitExt? normalized
  · exact RecM.ScopeWF.pure trivial
  · rename_i firstValue
    refine (Inner.whnf.scopeWF second).bind fun normalized _ _ _ => ?_
    cases Inner.rawNatLitExt? normalized
    · exact RecM.ScopeWF.pure trivial
    · rename_i secondValue
      cases outcome : operation firstValue secondValue <;> simp only [outcome]
      all_goals exact RecM.ScopeWF.pure (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)

set_option backward.split false in
theorem TypeChecker.Inner.reduceNat.scopeHeadWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.reduceNat expression).ScopeWF context state
      (fun result _ => NativeOptionalHeadScoped context.lctx' result) := by
  unfold Inner.reduceNat
  extract_lets argumentCount fallback function
  split
  · split
    · rename_i one successor
      simp [argumentCount, Expr.getAppNumArgs_eq] at one
      subst function
      let .app function argument := expression
      simp [Expr.appFn!, Expr.eqv_const] at successor ⊢
      subst successor
      let .app functionType argumentType functionTranslation argumentTranslation := translated
      refine (Inner.whnf.scopeWF argumentTranslation).bind fun normalized _ _ _ => ?_
      split
      · exact RecM.ScopeWF.pure (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)
      · exact RecM.ScopeWF.pure trivial
    · exact RecM.ScopeWF.pure trivial
  · split
    · split
      · rename_i name levels first second patternEqual
        let .app firstType secondType functionTranslation secondTranslation := translated
        let .app functionType argumentType constantTranslation firstTranslation := functionTranslation
        split
        · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
        · split
          · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
          · split
            · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
            · split
              · exact Inner.reducePow.scopeHeadWF firstTranslation secondTranslation
              · split
                · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                · split
                  · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                  · split
                    · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                    · split
                      · exact Inner.reduceBinNatPred.scopeHeadWF _ firstTranslation secondTranslation
                      · split
                        · exact Inner.reduceBinNatPred.scopeHeadWF _ firstTranslation secondTranslation
                        · split
                          · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                          · split
                            · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                            · split
                              · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                              · split
                                · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                                · split
                                  · exact Inner.reduceBinNatOp.scopeHeadWF _ firstTranslation secondTranslation
                                  · exact RecM.ScopeWF.pure (context := context) (state := state)
                                      (result := (none : Option Expr))
                                      (post := fun result _ => NativeOptionalHeadScoped context.lctx' result)
                                      trivial
      · exact RecM.ScopeWF.pure trivial
    · exact RecM.ScopeWF.pure trivial

theorem TypeChecker.Inner.whnfCore'.save_scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic)
    (below : context.FVarsBelow expression normalized) (result : context.TrExpr normalized semantic)
    (head : NativeHeadScoped context.lctx' normalized) :
    (Inner.whnfCore'.save expression cheapProj normalized).ScopeWF context state fun actual _ =>
      context.FVarsBelow expression actual ∧ context.TrExpr actual semantic ∧
      NativeHeadScoped context.lctx' actual := by
  unfold Inner.whnfCore'.save
  split
  · intro methods callbacks caches wellFormed actual finalState accepted
    cases accepted
    let updated : VState := { state with whnfCoreCache := state.whnfCoreCache.insert expression normalized }
    refine ⟨updated, rfl, .rfl, ?_, caches.insertCore expression normalized head, below, result, head⟩
    have cache : WHNFCache.WF context updated updated.whnfCoreCache := by
      intro key value found
      rw [Std.HashMap.getElem?_insert] at found
      split at found
      · cases found
        rename_i equal
        exact ConditionallyWHNF.mk context.mlctx.noBV (below.eqv equal BEq.rfl) (translated.eqv equal)
          result ((translated.eqv equal).fvarsIn.mono wellFormed.ngen_wf)
          (result.fvarsIn.mono wellFormed.ngen_wf)
      · exact wellFormed.whnfCore_wf found
    exact { wellFormed with whnfCore_wf := cache }
  · exact RecM.ScopeWF.pure ⟨below, result, head⟩

theorem TypeChecker.Inner.whnfFVar.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS (.fvar identifier) semantic) :
    (Inner.whnfFVar (.fvar identifier) cheapProj).ScopeWF context state fun normalized _ =>
      context.FVarsBelow (.fvar identifier) normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized := by
  refine RecM.ScopeWF.getLCtx ?_
  simp only [Expr.fvarId!]
  split
  · rename_i declaration found
    rw [context.trlctx.1.find?_eq_find?_toList] at found
    have equal := List.find?_some found
    simp at equal
    subst equal
    obtain ⟨value, type, lookup, below, _, body, _⟩ :=
      context.trlctx.find?_of_mem context.Ewf (List.mem_of_find?_eq_some found)
    refine (Inner.whnfCore.scopeWF body).mono fun _ _ _ normalized => ?_
    refine ⟨below.trans normalized.1, normalized.2.1.defeq context.Ewf context.Δwf ?_, normalized.2.2⟩
    exact (TrExprS.fvar lookup).uniq context.Ewf (.refl context.Ewf context.Δwf) translated
  · rename_i absent
    refine RecM.ScopeWF.pure ⟨.rfl, translated.trExpr context.Ewf context.Δwf, ⟨⟨rfl, rfl⟩, ?_⟩⟩
    intro current equal
    cases equal
    unfold Inner.isLetFVar
    cases found : context.lctx'.find? identifier with
    | none => rfl
    | some declaration =>
      cases declaration
      · rfl
      · exact False.elim (absent _ _ _ _ _ _ _ found)

theorem TypeChecker.Inner.reduceProj.scopeFrame {context : VContext} {state : VState}
    (translated : context.TrExprS source semantic) :
    (Inner.reduceProj index source cheapProj).ScopeWF context state (fun _ _ => True) := by
  unfold Inner.reduceProj
  have initial : (if cheapProj then Inner.whnfCore source cheapProj else Inner.whnf source)
      |>.ScopeWF context state (fun normalized _ =>
        context.FVarsBelow source normalized ∧ context.TrExpr normalized semantic ∧
        NativeHeadScoped context.lctx' normalized) := by
    cases cheapProj
    · exact Inner.whnf.scopeWF translated
    · exact Inner.whnfCore.scopeWF translated
  refine initial.bind fun normalized middleState _ normalizedResult => ?_
  have finish {state : VState} (expression : Expr) :
      (expression.withApp fun head arguments => do
        let .const name _ := head | return none
        let environment ← TypeChecker.getEnv
        let .ctorInfo information ← environment.get name | return none
        return arguments[information.numParams + index]? : RecM (Option Expr)).ScopeWF
          context state (fun _ _ => True) := by
    rw [Expr.withApp_eq]
    cases expression.getAppFn
    any_goals exact RecM.ScopeWF.pure trivial
    apply RecM.ScopeWF.getEnv
    refine (RecM.ScopeWF.liftExcept (action := context.env.get _) (post := fun _ => True)
      (fun _ _ => trivial)).bind ?_
    intro information finalState increasing valid
    cases information <;> exact RecM.ScopeWF.pure trivial
  unfold Inner.reduceProjCore
  cases h : normalized <;> try exact RecM.ScopeWF.pure trivial
  case const name levels =>
    subst normalized
    obtain ⟨_, structural, _⟩ := normalizedResult.2.1
    change RecM.ScopeWF context middleState
      ((Expr.const name levels).withApp _) (fun _ _ => True)
    exact finish (state := middleState) _
  case app function argument =>
    subst normalized
    obtain ⟨_, structural, _⟩ := normalizedResult.2.1
    change RecM.ScopeWF context middleState
      ((function.app argument).withApp _) (fun _ _ => True)
    exact finish (state := middleState) _
  case lit literal =>
    subst normalized
    cases literal with
    | natVal value => exact RecM.ScopeWF.pure trivial
    | strVal value =>
      obtain ⟨_, structural, _⟩ := normalizedResult.2.1
      cases structural with
      | lit contains constructor =>
        change RecM.ScopeWF context middleState (do
          let constructor ← Inner.whnf (Expr.strLitToConstructor value)
          constructor.withApp _) (fun _ _ => True)
        exact (Inner.whnf.scopeWF (state := middleState) constructor).bind
          (fun expression finalState _ _ => finish (state := finalState) expression)

theorem TypeChecker.Inner.whnfCore'.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.whnfCore' expression cheapProj).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized := by
  unfold Inner.whnfCore'
  extract_lets F
  let full := (· matches Expr.fvar _ | .app .. | .letE .. | .proj ..)
  generalize postEqual : (fun normalized (_ : VState) => _) = post
  have identity {state : VState} (head : NativeHeadScoped context.lctx' expression) :
      (pure expression : RecM Expr).ScopeWF context state post :=
    postEqual ▸ RecM.ScopeWF.pure ⟨.rfl, translated.trExpr context.Ewf context.Δwf, head⟩
  suffices continuation : full expression → (F ⟨⟩).ScopeWF context state post by
    split
    any_goals exact identity (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)
    any_goals exact continuation rfl
    · let .mdata body := translated
      exact (Inner.whnfCore'.scopeWF (cheapProj := cheapProj) body).mono
        (fun normalized finalState _ result => postEqual ▸ result)
    · refine RecM.ScopeWF.getLCtx ?_
      split
      · rename_i identifier notLet
        apply identity
        refine ⟨⟨rfl, rfl⟩, fun current equal => ?_⟩
        cases equal
        simpa using notLet
      · exact continuation rfl
  simp [F]
  refine fun active => RecM.ScopeWF.get ?_
  split
  · rename_i normalized found
    refine RecM.ScopeWF.cacheWF fun caches => RecM.ScopeWF.stateWF fun wellFormed => ?_
    obtain ⟨_, below, source, result⟩ := (wellFormed.whnfCore_wf found).2.2.2.2 translated.fvarsIn
    refine postEqual ▸ RecM.ScopeWF.pure ⟨below, result.defeq context.Ewf context.Δwf ?_, caches.1 _ _ found⟩
    exact source.uniq context.Ewf (.refl context.Ewf context.Δwf) translated
  have save {normalized : Expr} {state : VState}
      (below : context.FVarsBelow expression normalized) (result : context.TrExpr normalized semantic)
      (head : NativeHeadScoped context.lctx' normalized) :
      (Inner.whnfCore'.save expression cheapProj normalized).ScopeWF context state post :=
    postEqual ▸ Inner.whnfCore'.save_scopeWF translated below result head
  split <;> cases active
  · exact postEqual ▸ Inner.whnfFVar.scopeWF translated
  · rename_i function argument _
    generalize expressionEqual : function.app argument = expression at *
    obtain ⟨_, stack⟩ := AppStack.build (expression.mkAppList_getAppArgsList ▸ translated)
    refine (Inner.whnfCore.scopeWF stack.tr).bind fun normalized middleState _ normalizedResult => ?_
    obtain ⟨headBelow, headTranslation, headScoped⟩ := normalizedResult
    split <;> [rename_i increasing currentHead name domain body binder; split]
    · let rec loopResult {current : Expr} {semanticCurrent : Expr} {index : Nat} {arguments : Array Expr}
          {result : Expr} (lambdas : LambdaBodyN index semanticCurrent result) (bound : index ≤ arguments.size) :
          ∃ count finalBody, LambdaBodyN count semanticCurrent finalBody ∧ count ≤ arguments.size ∧
            Inner.whnfCore'.loop current cheapProj arguments index result =
              Inner.whnfCore'.loop.cont current cheapProj arguments count finalBody := by
        unfold Inner.whnfCore'.loop
        split
        · split
          · refine loopResult (by simpa [Nat.add_comm] using lambdas.add (.succ .zero)) ‹_›
          · exact ⟨_, _, lambdas, bound, rfl⟩
        · exact ⟨_, _, lambdas, bound, rfl⟩
      obtain ⟨count, finalBody, lambdas, bound, loopEqual⟩ :=
        loopResult (current := expression) (arguments := expression.getAppRevArgs) (index := 1)
          (semanticCurrent := .lam name domain body binder) (.succ .zero) (by
          simp [← expressionEqual, Expr.getAppRevArgs_eq, Expr.getAppArgsRevList])
      rw [loopEqual]
      simp [Expr.getAppRevArgs_eq] at bound ⊢
      obtain ⟨remaining, consumed, argumentsEqual, countEqual⟩ :
          ∃ remaining consumed, expression.getAppArgsRevList = remaining ++ consumed ∧ consumed.length = count :=
        ⟨_, _, (List.take_append_drop (expression.getAppArgsRevList.length - count) ..).symm, by simp; omega⟩
      subst countEqual
      simp [Inner.whnfCore'.loop.cont, argumentsEqual, List.take_of_length_le]
      rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₂ := remaining) (l₃ := consumed) (by simp) (by simp) (by simp)]
      have consumedScope : ∀ selected ∈ consumed, selected.looseBVarRange' = 0 := by
        have closed := argumentsEqual ▸ (context.mlctx.noBV ▸ translated.closed).getAppArgsRevList
        simp [or_imp, forall_and] at closed
        intro selected member
        exact (closed.2 selected member).looseBVarRange_zero
      rw [Expr.instantiateMany_eq_instantiateList _ _ _ consumedScope]
      have reduction := BetaReduce.inst_reduce (l₁ := consumed.reverse) [] (by simpa using lambdas)
        (Expr.instantiateList_append ..) (h := by
          have closed := argumentsEqual ▸ (context.mlctx.noBV ▸ translated.closed).getAppArgsRevList
          simp [or_imp, forall_and] at closed ⊢
          exact closed.2) |>.mkAppRevList (es := remaining)
      simp [← Expr.mkAppRevList_reverse, ← Expr.mkAppRevList_append, ← argumentsEqual] at reduction
      have rebuilt := headTranslation.rebuild_mkAppRevList context.Ewf context.Δwf stack.tr
        (expression.mkAppRevList_getAppArgsRevList ▸ translated)
      obtain ⟨_, bodyTranslation, bodyEqual⟩ := rebuilt.beta context.Ewf context.Δwf reduction
      refine (Inner.whnfCore.scopeWF bodyTranslation).bind fun _ _ _ result => ?_
      have below := expression.mkAppRevList_getAppArgsRevList ▸ headBelow.mkAppRevList
      exact save (below.trans (.betaReduce reduction) |>.trans result.1)
        (result.2.1.defeq context.Ewf context.Δwf bodyEqual) result.2.2
    · refine ((Inner.reduceRecursor.scopeFrame translated).andWF
        (Inner.reduceRecursor.WF translated)).bind fun reduced finalState _ reduction => ?_
      split
      · obtain ⟨below, _, source, equal⟩ := reduction.2 _ rfl
        refine postEqual ▸ (Inner.whnfCore.scopeWF source).mono fun _ _ _ result => ?_
        exact ⟨below.trans result.1, result.2.1.defeq context.Ewf context.Δwf equal, result.2.2⟩
      · exact identity (NativeHeadScoped.ofNotFVar
          (by rw [← expressionEqual]; exact ⟨rfl, rfl⟩) (by rw [← expressionEqual]; rfl))
    · rw [Expr.mkAppRevRange_eq_rev (l₁ := []) (l₃ := [])
        (by simp [Expr.getAppRevArgs_toList]; rfl) (by rfl) (by simp [Expr.getAppRevArgs_eq])]
      have rebuild {source rebuilt : Expr} (below : context.FVarsBelow source rebuilt)
          {arguments : List Expr} {applicationSemantic headSemantic : VExpr}
          (application : context.TrExprS (source.mkAppRevList arguments) applicationSemantic)
          (head : context.TrExprS source headSemantic) (result : context.TrExpr rebuilt headSemantic) :
          context.FVarsBelow (source.mkAppRevList arguments) (rebuilt.mkAppRevList arguments) ∧
          context.TrExpr (rebuilt.mkAppRevList arguments) applicationSemantic := by
        induction arguments generalizing rebuilt applicationSemantic headSemantic with
        | nil =>
          refine ⟨below, result.defeq context.Ewf context.Δwf ?_⟩
          exact head.uniq context.Ewf (.refl context.Ewf context.Δwf) application
        | cons argument arguments inductionHypothesis =>
          have .app functionType argumentType functionTranslation argumentTranslation := application
          obtain ⟨functionBelow, functionResult⟩ := inductionHypothesis below functionTranslation head result
          exact ⟨fun _ upward original => ⟨functionBelow _ upward original.1, original.2⟩,
            .app context.Ewf context.Δwf functionType argumentType functionResult
              (argumentTranslation.trExpr context.Ewf context.Δwf)⟩
      have originalEqual := expression.mkAppRevList_getAppArgsRevList
      obtain ⟨below, _, source, equal⟩ := originalEqual ▸
        rebuild headBelow (originalEqual ▸ translated) stack.tr headTranslation
      refine (Inner.whnfCore.scopeWF source).bind fun _ _ _ result => ?_
      exact save (below.trans result.1) (result.2.1.defeq context.Ewf context.Δwf equal) result.2.2
  · let .letE valueType domainTranslation valueTranslation bodyTranslation := translated
    refine (Inner.whnfCore.scopeWF (bodyTranslation.inst_let context.Ewf.ordered valueTranslation)).bind
      fun _ _ _ result => ?_
    exact save (.trans (fun _ _ original => original.2.2.instantiate1 original.2.1) result.1)
      result.2.1 result.2.2
  · let .proj sourceTranslation projection := translated
    refine ((Inner.reduceProj.scopeFrame sourceTranslation).andWF (Inner.reduceProj.WF translated)).bind
      fun reduced finalState _ reduction => ?_
    split
    · obtain ⟨below, _, source, equal⟩ := reduction.2 _ rfl
      refine (Inner.whnfCore.scopeWF source).bind fun _ _ _ result => ?_
      exact save (below.trans result.1) (result.2.1.defeq context.Ewf context.Δwf equal) result.2.2
    · exact save .rfl (translated.trExpr context.Ewf context.Δwf)
        (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)

theorem TypeChecker.Inner.whnf'.scopeWF {context : VContext} {state : VState}
    (translated : context.TrExprS expression semantic) :
    (Inner.whnf' expression).ScopeWF context state fun normalized _ =>
      context.FVarsBelow expression normalized ∧ context.TrExpr normalized semantic ∧
      NativeHeadScoped context.lctx' normalized := by
  unfold Inner.whnf'
  extract_lets F
  generalize postEqual : (fun normalized (_ : VState) => _) = post
  have identity {state : VState} (head : NativeHeadScoped context.lctx' expression) :
      (pure expression : RecM Expr).ScopeWF context state post :=
    postEqual ▸ RecM.ScopeWF.pure ⟨.rfl, translated.trExpr context.Ewf context.Δwf, head⟩
  suffices continuation : (F ()).ScopeWF context state post by
    split
    any_goals exact identity (NativeHeadScoped.ofNotFVar ⟨rfl, rfl⟩ rfl)
    any_goals exact continuation
    · let .mdata body := translated
      exact (Inner.whnf'.scopeWF body).mono
        (fun normalized finalState _ result => postEqual ▸ result)
    · refine RecM.ScopeWF.getLCtx ?_
      split
      · apply identity
        rename_i identifier notLet
        refine ⟨⟨rfl, rfl⟩, fun current equal => ?_⟩
        cases equal
        simpa using notLet
      · exact continuation
  simp [F]
  refine RecM.ScopeWF.get ?_
  split
  · rename_i normalized found
    refine RecM.ScopeWF.cacheWF fun caches => RecM.ScopeWF.stateWF fun wellFormed => ?_
    obtain ⟨_, below, source, result⟩ := (wellFormed.whnf_wf found).2.2.2.2 translated.fvarsIn
    refine postEqual ▸ RecM.ScopeWF.pure ⟨below, result.defeq context.Ewf context.Δwf ?_, caches.2 _ _ found⟩
    exact source.uniq context.Ewf (.refl context.Ewf context.Δwf) translated
  have loopScope {current : Expr} {currentSemantic : VExpr} {state : VState} {fuel : Nat}
      (source : context.TrExprS current currentSemantic) :
      (Inner.whnf'.loop current fuel).ScopeWF context state fun normalized _ =>
        context.FVarsBelow current normalized ∧ context.TrExpr normalized currentSemantic ∧
        NativeHeadScoped context.lctx' normalized := by
    induction fuel generalizing state current currentSemantic with
    | zero => exact RecM.ScopeWF.throw
    | succ fuel inductionHypothesis =>
      refine RecM.ScopeWF.getEnv <|
        (Inner.whnfCore'.scopeWF source).bind fun normalized middleState _ normalizedResult => ?_
      obtain ⟨below, ⟨_, structural, equal⟩, head⟩ := normalizedResult
      refine (RecM.ScopeWF.liftExcept Inner.reduceNative.WF).bind fun _ _ _ noNative => ?_
      extract_lets afterDelta afterNat
      split
      · cases noNative _ rfl
      · refine ((Inner.reduceNat.scopeHeadWF structural).andWF (Inner.reduceNat.WF structural)).bind
          fun reduced _ _ naturalReduction => ?_
        split
        · obtain ⟨naturalBelow, naturalTranslation⟩ := naturalReduction.2 _ rfl
          exact RecM.ScopeWF.pure ⟨below.trans naturalBelow,
            naturalTranslation.defeq context.Ewf context.Δwf equal, naturalReduction.1⟩
        · refine (Inner.unfoldDefinition.scopeWF structural).bind fun unfolded _ _ unfolding => ?_
          split
          · obtain ⟨unfoldedBelow, _, unfoldedTranslation, unfoldedEqual⟩ := unfolding
            refine (inductionHypothesis unfoldedTranslation).mono fun _ _ _ result => ?_
            exact ⟨below.trans (unfoldedBelow.trans result.1),
              result.2.1.defeq context.Ewf context.Δwf (unfoldedEqual.trans context.Ewf context.Δwf equal),
              result.2.2⟩
          · exact RecM.ScopeWF.pure ⟨below, ⟨_, structural, equal⟩, head⟩
  refine RecM.ScopeWF.readThe <| (loopScope translated).bind fun normalized middleState _ normalizedResult => ?_
  obtain ⟨below, result, head⟩ := normalizedResult
  intro methods callbacks caches wellFormed actual finalState accepted
  cases accepted
  let updated : VState := { middleState with whnfCache := middleState.whnfCache.insert expression normalized }
  refine postEqual ▸ ⟨updated, rfl, .rfl, ?_, caches.insertFull expression normalized head, below, result, head⟩
  have cache : WHNFCache.WF context updated updated.whnfCache := by
    intro key value found
    rw [Std.HashMap.getElem?_insert] at found
    split at found
    · cases found
      rename_i equal
      exact ConditionallyWHNF.mk context.mlctx.noBV (below.eqv equal BEq.rfl) (translated.eqv equal)
        result ((translated.eqv equal).fvarsIn.mono wellFormed.ngen_wf)
        (result.fvarsIn.mono wellFormed.ngen_wf)
    · exact wellFormed.whnf_wf found
  exact { wellFormed with whnf_wf := cache }

end Lean4Lean
