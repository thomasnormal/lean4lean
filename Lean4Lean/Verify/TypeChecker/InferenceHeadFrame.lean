import Lean4Lean.Verify.TypeChecker.RecursorHeadFrame
import Lean4Lean.Verify.InductiveHeaderProjectionTransport

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TypeChecker.M.HeadWF.withContextReader (update : TypeChecker.Context → TypeChecker.Context)
    {action : TypeChecker.M Result} {post : Result → Prop} (valid : action.HeadWF post) :
    (withTheReader TypeChecker.Context update action).HeadWF post := by
  intro context state caches result finalState accepted
  exact valid (update context) state caches result finalState accepted

theorem TypeChecker.M.HeadWF.withLocalReader (update : LocalContext → LocalContext)
    {action : TypeChecker.M Result} {post : Result → Prop} (valid : action.HeadWF post) :
    (withTheReader LocalContext update action).HeadWF post := by
  intro context state caches result finalState accepted
  exact valid { context with lctx := update context.lctx } state caches result finalState accepted

theorem TypeChecker.M.HeadWF.withFreshId {continuation : Name → TypeChecker.M Result} {post : Result → Prop}
    (valid : ∀ name, (continuation name).HeadWF post) :
    (withFreshId continuation).HeadWF post := by
  intro context state caches result finalState accepted
  exact valid state.ngen.curr context { state with ngen := state.ngen.next }
    caches result finalState accepted

theorem TypeChecker.RecM.bind_headWF {action : TypeChecker.RecM α}
    {continuation : α → TypeChecker.RecM β} {pre : α → Prop} {post : β → Prop}
    (methods : TypeChecker.Methods) (valid : (action methods).HeadWF pre)
    (framed : ∀ value, pre value → (continuation value methods).HeadWF post) :
    ((action >>= continuation) methods).HeadWF post := by
  dsimp only [Bind.bind, ReaderT.bind]
  exact valid.bind fun value proof => framed value proof

theorem withLocalDecl.headWF (name : Name) (binder : BinderInfo) (domain : Expr)
    (continuation : Expr → TypeChecker.RecM Result) (methods : TypeChecker.Methods) (post : Result → Prop)
    (valid : ∀ expression, (continuation expression methods).HeadWF post) :
    (withLocalDecl name binder domain continuation methods).HeadWF post := by
  intro context state caches result finalState accepted
  exact valid (.fvar ⟨state.ngen.curr⟩)
    { context with lctx := context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain binder }
    { state with ngen := state.ngen.next } caches result finalState accepted

theorem withLetDecl.headWF (name : Name) (type value : Expr)
    (continuation : Expr → TypeChecker.RecM Result) (methods : TypeChecker.Methods) (post : Result → Prop)
    (valid : ∀ expression, (continuation expression methods).HeadWF post) :
    (withLetDecl name type value continuation methods).HeadWF post := by
  intro context state caches result finalState accepted
  exact valid (.fvar ⟨state.ngen.curr⟩)
    { context with lctx := context.lctx.mkLetDecl ⟨state.ngen.curr⟩ name type value }
    { state with ngen := state.ngen.next } caches result finalState accepted

theorem TypeChecker.Inner.ensureSortCore.headWF (expression source : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (ensureSortCore expression source methods).HeadWF (fun _ => True) := by
  unfold ensureSortCore
  try simp only [pure_bind]
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, whnf]
    refine (valid.whnf expression).bind fun normalized _ => ?_
    split
    · exact TypeChecker.M.HeadWF.pure trivial
    · dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.HeadWF.getEnv
      intro environment
      apply TypeChecker.M.HeadWF.getLCtx
      intro locals
      exact TypeChecker.M.HeadWF.throw _ _

theorem TypeChecker.Inner.ensureForallCore.headWF (expression source : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (ensureForallCore expression source methods).HeadWF (fun _ => True) := by
  unfold ensureForallCore
  try simp only [pure_bind]
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, whnf]
    refine (valid.whnf expression).bind fun normalized _ => ?_
    split
    · exact TypeChecker.M.HeadWF.pure trivial
    · dsimp only [Bind.bind, ReaderT.bind]
      apply TypeChecker.M.HeadWF.getEnv
      intro environment
      apply TypeChecker.M.HeadWF.getLCtx
      intro locals
      exact TypeChecker.M.HeadWF.throw _ _

theorem TypeChecker.Inner.getSortLevel.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (getSortLevel expression methods).HeadWF (fun _ => True) := by
  unfold getSortLevel
  apply TypeChecker.RecM.bind_headWF methods (valid := valid.inferType expression true)
  intro inferred _
  dsimp only [Bind.bind, ReaderT.bind]
  refine (ensureSortCore.headWF inferred expression methods valid).bind fun normalized _ => ?_
  cases normalized <;> exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.isProp.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isProp expression methods).HeadWF (fun _ => True) := by
  unfold isProp
  dsimp only [Bind.bind, ReaderT.bind]
  exact (getSortLevel.headWF expression methods valid).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.nativeProjectionMaybeProp.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionMaybeProp expression methods).HeadWF (fun _ => True) := by
  unfold nativeProjectionMaybeProp
  apply TypeChecker.RecM.bind_headWF methods (valid := getSortLevel.headWF expression methods valid)
  intro level _
  exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.inferLambda.loop_headWF (inferOnly : Bool) (variables : Array Expr)
    (expression : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferLambda.loop inferOnly variables expression methods).HeadWF (fun _ => True) := by
  induction expression generalizing variables with
  | lam name domain body binder domainIH bodyIH =>
    unfold inferLambda.loop
    simp only [pure_bind]
    cases inferOnly <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    · dsimp only [Bind.bind, ReaderT.bind, inferType]
      refine (valid.inferType _ false).bind fun inferred _ => ?_
      try dsimp only [Bind.bind, ReaderT.bind]
      refine (ensureSortCore.headWF inferred _ methods valid).bind fun _ _ => ?_
      exact withLocalDecl.headWF _ _ _ _ methods _ fun freeVariable => bodyIH (variables.push freeVariable)
    · exact withLocalDecl.headWF _ _ _ _ methods _ fun freeVariable => bodyIH (variables.push freeVariable)
  | _ =>
    unfold inferLambda.loop
    dsimp only [Bind.bind, ReaderT.bind, inferType]
    refine (valid.inferType _ inferOnly).bind fun inferred _ => ?_
    apply TypeChecker.M.HeadWF.getLCtx
    intro locals
    exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.inferLambda.headWF (expression : Expr) (inferOnly : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferLambda expression inferOnly methods).HeadWF (fun _ => True) :=
  inferLambda.loop_headWF inferOnly #[] expression methods valid

theorem TypeChecker.Inner.inferForall.loop_headWF (inferOnly : Bool) (variables : Array Expr)
    (universes : Array Level) (expression : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferForall.loop inferOnly variables universes expression methods).HeadWF (fun _ => True) := by
  induction expression generalizing variables universes with
  | forallE name domain body binder domainIH bodyIH =>
    unfold inferForall.loop
    dsimp only [Bind.bind, ReaderT.bind, inferType]
    refine (valid.inferType _ inferOnly).bind fun inferred _ => ?_
    try dsimp only [Bind.bind, ReaderT.bind]
    refine (ensureSortCore.headWF inferred _ methods valid).bind fun normalized _ => ?_
    exact withLocalDecl.headWF _ _ _ _ methods _
      fun freeVariable => bodyIH (variables.push freeVariable) (universes.push normalized.sortLevel!)
  | _ =>
    unfold inferForall.loop
    dsimp only [Bind.bind, ReaderT.bind, inferType]
    refine (valid.inferType _ inferOnly).bind fun inferred _ => ?_
    try dsimp only [Bind.bind, ReaderT.bind]
    exact (ensureSortCore.headWF inferred _ methods valid).bind fun _ _ => .pure trivial

theorem TypeChecker.Inner.inferForall.headWF (expression : Expr) (inferOnly : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferForall expression inferOnly methods).HeadWF (fun _ => True) :=
  inferForall.loop_headWF inferOnly #[] #[] expression methods valid

theorem TypeChecker.Inner.inferLet.loop_headWF (inferOnly : Bool) (variables : Array Expr)
    (expression : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferLet.loop inferOnly variables expression methods).HeadWF (fun _ => True) := by
  induction expression generalizing variables with
  | letE name type value body nondependent typeIH valueIH bodyIH =>
    unfold inferLet.loop
    simp only [pure_bind]
    cases inferOnly <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    · dsimp only [Bind.bind, ReaderT.bind, inferType]
      refine (valid.inferType _ false).bind fun inferred _ => ?_
      try dsimp only [Bind.bind, ReaderT.bind]
      refine (ensureSortCore.headWF inferred _ methods valid).bind fun _ _ => ?_
      try dsimp only [Bind.bind, ReaderT.bind, inferType]
      refine (valid.inferType _ false).bind fun inferred _ => ?_
      try dsimp only [Bind.bind, ReaderT.bind]
      refine (isDefEq.headWF inferred _ methods valid).bind fun equal _ => ?_
      cases equal <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
      · dsimp only [Bind.bind, ReaderT.bind]
        apply TypeChecker.M.HeadWF.getEnv
        intro environment
        apply TypeChecker.M.HeadWF.getLCtx
        intro locals
        intro context state caches result finalState accepted
        contradiction
      · exact withLetDecl.headWF _ _ _ _ methods _ fun freeVariable => bodyIH (variables.push freeVariable)
    · exact withLetDecl.headWF _ _ _ _ methods _ fun freeVariable => bodyIH (variables.push freeVariable)
  | _ =>
    unfold inferLet.loop
    dsimp only [Bind.bind, ReaderT.bind, inferType]
    refine (valid.inferType _ inferOnly).bind fun inferred _ => ?_
    apply TypeChecker.M.HeadWF.getLCtx
    intro locals
    exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.inferLet.headWF (expression : Expr) (inferOnly : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferLet expression inferOnly methods).HeadWF (fun _ => True) :=
  inferLet.loop_headWF inferOnly #[] expression methods valid

theorem TypeChecker.RecM.forInList_headWF (elements : List Element) (initial : Value)
    (body : Element → Value → TypeChecker.RecM (ForInStep Value)) (methods : TypeChecker.Methods)
    (framed : ∀ element value, (body element value methods).HeadWF (fun _ => True)) :
    (forIn elements initial body methods).HeadWF (fun _ => True) := by
  induction elements generalizing initial with
  | nil => exact TypeChecker.M.HeadWF.pure trivial
  | cons element elements inductionHypothesis =>
    rw [List.forIn_cons]
    try dsimp only [Bind.bind, ReaderT.bind]
    refine (framed element initial).bind fun step _ => ?_
    cases step
    · exact TypeChecker.M.HeadWF.pure trivial
    · exact inductionHypothesis _

theorem TypeChecker.RecM.forInRange_headWF (range : Std.Legacy.Range) (initial : Value)
    (body : Nat → Value → TypeChecker.RecM (ForInStep Value)) (methods : TypeChecker.Methods)
    (framed : ∀ index value, (body index value methods).HeadWF (fun _ => True)) :
    (forIn range initial body methods).HeadWF (fun _ => True) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList_headWF _ _ _ _ framed

theorem TypeChecker.Inner.inferApp.loop_headWF (source : Expr) (arguments : Array Expr)
    (current : Expr) (pending index : Nat) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferApp.loop source arguments current pending index methods).HeadWF (fun _ => True) := by
  generalize distanceEq : arguments.size - index = distance
  induction distance using Nat.strongRecOn generalizing current pending index with
  | ind distance inductionHypothesis =>
    rw [inferApp.loop.eq_def]
    by_cases inRange : index < arguments.size
    · rw [if_pos inRange]
      have closer : arguments.size - (index + 1) < distance := by omega
      cases current with
      | forallE name domain body binder => exact inductionHypothesis _ closer body pending (index + 1) rfl
      | _ =>
        dsimp only [Bind.bind, ReaderT.bind]
        refine (ensureForallCore.headWF _ source methods valid).bind fun normalized _ => ?_
        exact inductionHypothesis _ closer normalized.bindingBody! index (index + 1) rfl
    · rw [if_neg inRange]
      exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.inferApp.headWF (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferApp expression methods).HeadWF (fun _ => True) := by
  rw [inferApp, Expr.withApp_eq]
  dsimp only [Bind.bind, ReaderT.bind, inferType]
  refine (valid.inferType _ true).bind fun inferred _ => ?_
  exact inferApp.loop_headWF _ _ inferred 0 0 methods valid

theorem TypeChecker.Inner.nativeProjectionFailure.bind_headWF
    (environment : Kernel.Environment) (source : Expr) (continuation : Input → TypeChecker.RecM Output)
    (methods : TypeChecker.Methods) :
    ((nativeProjectionFailure environment source >>= continuation) methods).HeadWF (fun _ => True) := by
  intro context state caches result finalState accepted
  change (Except.error _ : Except Kernel.Exception (Output × TypeChecker.State)) = .ok _ at accepted
  contradiction

theorem TypeChecker.Inner.nativeProjectionFailure.headWF
    (environment : Kernel.Environment) (source : Expr) (methods : TypeChecker.Methods) :
    (nativeProjectionFailure (resultType := Output) environment source methods).HeadWF (fun _ => True) := by
  intro context state caches result finalState accepted
  contradiction

theorem TypeChecker.Inner.nativeProjectionParameter.headWF (environment : Kernel.Environment) (source : Expr)
    (arguments : Array Expr) (index : Nat) (current : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionParameter environment source arguments index current methods).HeadWF (fun _ => True) := by
  unfold nativeProjectionParameter
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf current).bind fun normalized _ => ?_
  cases normalized <;> first
    | exact nativeProjectionFailure.bind_headWF _ _ _ methods
    | exact nativeProjectionFailure.headWF _ _ methods
    | exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeProjectionParameters.headWF (environment : Kernel.Environment) (source : Expr)
    (arguments : Array Expr) (parameters : Nat) (initial : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionParameters environment source arguments parameters initial methods).HeadWF (fun _ => True) :=
  TypeChecker.RecM.forInRange_headWF _ _ _ methods
    fun index current => nativeProjectionParameter.headWF environment source arguments index current methods valid

theorem TypeChecker.Inner.nativeProjectionField.headWF (environment : Kernel.Environment) (source : Expr)
    (parent : Name) (structureValue : Expr) (propositional : Bool) (index : Nat) (current : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionField environment source parent structureValue propositional index current methods).HeadWF
      (fun _ => True) := by
  unfold nativeProjectionField
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf current).bind fun normalized _ => ?_
  cases normalized <;> try first
    | exact nativeProjectionFailure.bind_headWF _ _ _ methods
    | exact nativeProjectionFailure.headWF _ _ methods
  case forallE =>
    dsimp only
    split
    · cases propositional <;> simp only [Bool.false_eq_true, if_true, if_false]
      · exact TypeChecker.M.HeadWF.pure trivial
      · dsimp only [Bind.bind, ReaderT.bind]
        refine (isProp.headWF _ methods valid).bind fun domainProposition _ => ?_
        cases domainProposition <;>
          simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        · exact nativeProjectionFailure.bind_headWF _ _ _ methods
        · exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeProjectionFields.headWF (environment : Kernel.Environment) (source : Expr)
    (parent : Name) (structureValue : Expr) (propositional : Bool) (fields : Nat) (initial : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionFields environment source parent structureValue propositional fields initial methods).HeadWF
      (fun _ => True) :=
  TypeChecker.RecM.forInRange_headWF _ _ _ methods
    fun index current =>
      nativeProjectionField.headWF environment source parent structureValue propositional index current methods valid

theorem TypeChecker.Inner.nativeProjectionFinal.headWF (environment : Kernel.Environment) (source : Expr)
    (propositional : Bool) (current : Expr) (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionFinal environment source propositional current methods).HeadWF (fun _ => True) := by
  unfold nativeProjectionFinal
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf current).bind fun normalized _ => ?_
  cases normalized <;> try exact nativeProjectionFailure.headWF _ _ methods
  case forallE =>
    cases propositional <;> simp only [Bool.false_eq_true, if_true, if_false]
    · exact TypeChecker.M.HeadWF.pure trivial
    · dsimp only [Bind.bind, ReaderT.bind]
      refine (isProp.headWF _ methods valid).bind fun domainProposition _ => ?_
      cases domainProposition <;>
        simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
      · exact nativeProjectionFailure.bind_headWF _ _ _ methods
      · exact TypeChecker.M.HeadWF.pure trivial

theorem TypeChecker.Inner.nativeProjectionBody.headWF (parent : Name) (index : Nat) (structureValue normalized : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (nativeProjectionBody parent index structureValue normalized methods).HeadWF (fun _ => True) := by
  unfold nativeProjectionBody
  rw [Expr.withApp_eq]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  cases normalized.getAppFn <;> try exact nativeProjectionFailure.headWF _ _ methods
  rename_i name levels
  dsimp only
  split
  · exact nativeProjectionFailure.bind_headWF _ _ _ methods
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (TypeChecker.M.HeadWF.liftExcept _).bind fun information _ => ?_
    cases information <;> try exact nativeProjectionFailure.headWF _ _ methods
    rename_i info
    dsimp only
    cases info.ctors with
    | nil => exact nativeProjectionFailure.headWF _ _ methods
    | cons constructor remaining =>
      cases remaining with
      | cons second remaining => exact nativeProjectionFailure.headWF _ _ methods
      | nil =>
        dsimp only
        split
        · exact nativeProjectionFailure.bind_headWF _ _ _ methods
        · dsimp only [Bind.bind, ReaderT.bind]
          refine (TypeChecker.M.HeadWF.liftExcept _).bind fun constructorInfo _ => ?_
          try dsimp only [Bind.bind, ReaderT.bind]
          refine (nativeProjectionParameters.headWF _ _ _ _ _ methods valid).bind fun fields _ => ?_
          try dsimp only [Bind.bind, ReaderT.bind]
          refine TypeChecker.RecM.bind_headWF methods
            (action := nativeProjectionMaybeProp normalized)
            (continuation := fun proposition =>
              nativeProjectionFields environment (.proj parent index structureValue) name structureValue proposition index fields >>= fun fields =>
                nativeProjectionFinal environment (.proj parent index structureValue) proposition fields)
            (valid := nativeProjectionMaybeProp.headWF normalized methods valid) ?_
          intro proposition _
          try dsimp only [Bind.bind, ReaderT.bind]
          refine (nativeProjectionFields.headWF _ _ _ _ _ _ _ methods valid).bind fun fields _ => ?_
          exact nativeProjectionFinal.headWF _ _ _ fields methods valid

theorem TypeChecker.Inner.inferProj.headWF (parent : Name) (index : Nat) (structureValue structureType : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferProj parent index structureValue structureType methods).HeadWF (fun _ => True) := by
  rw [inferProj.body_eq]
  dsimp only [Bind.bind, ReaderT.bind, whnf]
  refine (valid.whnf structureType).bind fun normalized _ => ?_
  exact nativeProjectionBody.headWF parent index structureValue normalized methods valid

theorem TypeChecker.Inner.inferType'.headWF (expression : Expr) (inferOnly : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (inferType' expression inferOnly methods).HeadWF (fun _ => True) := by
  unfold inferType'
  lift_lets
  intro finish worker continuation
  split
  · intro state caches result finalState accepted
    change Except.error _ = Except.ok _ at accepted
    contradiction
  · dsimp only [Bind.bind, ReaderT.bind]
    try simp only [pure_bind]
    try dsimp only [Bind.bind, ReaderT.bind]
    apply TypeChecker.M.HeadWF.get
    intro state caches
    dsimp only
    cases found : (cond inferOnly state.inferTypeI state.inferTypeC)[expression]? with
    | some inferred => exact TypeChecker.M.HeadWF.pure trivial
    | none =>
      have finishFrame (inferred : Expr) : (finish inferred methods).HeadWF (fun _ => True) := by
        unfold finish
        dsimp only [Bind.bind, ReaderT.bind]
        refine (TypeChecker.M.HeadWF.modify _ ?_).bind fun _ _ => .pure trivial
        intro current clean
        cases inferOnly <;> exact clean
      try unfold worker
      try simp only [pure_bind]
      dsimp only [Bind.bind, ReaderT.bind]
      cases expression <;> dsimp only [Bind.bind, ReaderT.bind]
      case lit literal closed =>
        cases inferOnly <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        · cases literal
          · dsimp only [Bind.bind, ReaderT.bind]
            apply TypeChecker.M.HeadWF.getEnv
            intro environment
            exact (TypeChecker.M.HeadWF.liftExcept _).bind fun _ _ => finishFrame _
          · dsimp only [Bind.bind, ReaderT.bind]
            apply TypeChecker.M.HeadWF.getEnv
            intro environment
            refine (TypeChecker.M.HeadWF.liftExcept _).bind fun _ _ => ?_
            apply TypeChecker.M.HeadWF.getEnv
            intro environment
            exact (TypeChecker.M.HeadWF.liftExcept _).bind fun _ _ => finishFrame _
        · exact finishFrame _
      case mdata metadata body closed =>
        exact (inferType'.headWF body inferOnly methods valid).bind fun inferred _ => finishFrame inferred
      case proj parent index body closed =>
        refine (inferType'.headWF body inferOnly methods valid).bind fun inferred _ => ?_
        exact (inferProj.headWF parent index body inferred methods valid).bind fun result _ => finishFrame result
      case fvar identifier closed =>
        apply TypeChecker.M.HeadWF.read
        intro context
        exact (TypeChecker.M.HeadWF.liftExcept _).bind fun result _ => finishFrame result
      case mvar identifier closed =>
        intro context current clean result finalState accepted
        contradiction
      case bvar index closed =>
        exact (TypeChecker.M.HeadWF.pure (post := fun _ => True) trivial).bind
          fun inferred _ => finishFrame inferred
      case sort universeLevel closed =>
        cases inferOnly <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
        · dsimp only [Bind.bind, ReaderT.bind]
          apply TypeChecker.M.HeadWF.read
          intro context
          exact (TypeChecker.M.HeadWF.liftExcept _).bind fun _ _ => finishFrame _
        · exact finishFrame _
      case const name levels closed =>
        apply TypeChecker.M.HeadWF.read
        intro context
        exact (TypeChecker.M.HeadWF.liftExcept _).bind fun result _ => finishFrame result
      case lam name domain body binder closed =>
        exact (inferLambda.headWF _ inferOnly methods valid).bind fun result _ => finishFrame result
      case forallE name domain body binder closed =>
        exact (inferForall.headWF _ inferOnly methods valid).bind fun result _ => finishFrame result
      case letE name type value body nondependent closed =>
        exact (inferLet.headWF _ inferOnly methods valid).bind fun result _ => finishFrame result
      case app function argument closed =>
        cases inferOnly <;> simp only [Bool.false_eq_true, if_true, if_false]
        · dsimp only [Bind.bind, ReaderT.bind]
          refine (inferType'.headWF function false methods valid).bind fun functionType _ => ?_
          try dsimp only [Bind.bind, ReaderT.bind]
          refine (ensureForallCore.headWF functionType _ methods valid).bind fun forallType _ => ?_
          try dsimp only [Bind.bind, ReaderT.bind]
          refine (inferType'.headWF argument false methods valid).bind fun argumentType _ => ?_
          split <;> dsimp only [Bind.bind, ReaderT.bind]
          all_goals first
            | refine ((isDefEq.headWF _ _ methods valid).withContextReader
                (fun context => { context with eagerReduce := true })).bind fun equal _ => ?_
            | refine (isDefEq.headWF _ _ methods valid).bind fun equal _ => ?_
          all_goals
            cases equal <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_true, if_false]
            · dsimp only [Bind.bind, ReaderT.bind]
              apply TypeChecker.M.HeadWF.getEnv
              intro environment
              apply TypeChecker.M.HeadWF.getLCtx
              intro locals
              intro context current clean result finalState accepted
              contradiction
            · exact finishFrame _
        · exact (inferApp.headWF _ methods valid).bind fun result _ => finishFrame result
termination_by expression

theorem TypeChecker.Methods.withFuel.inferType_succ_headWF (fuel : Nat) (valid : (withFuel fuel).HeadWF)
    (expression : Expr) (inferOnly : Bool) :
    ((withFuel (fuel + 1)).inferType expression inferOnly).HeadWF (fun _ => True) :=
  TypeChecker.Inner.inferType'.headWF expression inferOnly (withFuel fuel) valid

end Lean4Lean
