import Lean4Lean.Verify.TypeChecker.HeadShape

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TypeChecker.Inner.isDefEq.headWF (first second : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (isDefEq first second methods).HeadWF (fun _ => True) := by
  unfold isDefEq
  dsimp only [Bind.bind, ReaderT.bind, isDefEqCore]
  refine (valid.isDefEqCore first second).bind fun equal _ => ?_
  cases equal
  · exact TypeChecker.M.HeadWF.pure trivial
  · exact (TypeChecker.M.HeadWF.modify (fun state : TypeChecker.State =>
      { state with eqvManager := state.eqvManager.addEquiv first second }) fun _ caches => caches).bind
        (finalPost := fun _ => True) fun _ _ => .pure trivial

theorem quotReduceRec.headWF (expression : Expr) (methods : TypeChecker.Methods)
    (valid : methods.HeadWF) :
    (quotReduceRec expression TypeChecker.Inner.whnf methods).HeadWF (fun _ => True) := by
  unfold quotReduceRec
  cases expression.getAppFn <;> try exact TypeChecker.M.HeadWF.pure trivial
  dsimp only
  have continuation (constructorPosition argumentPosition : Nat) :
      ((do
        let arguments := expression.getAppArgs
        if bound : constructorPosition < arguments.size then
          let constructor ← TypeChecker.Inner.whnf arguments[constructorPosition]
          if !constructor.isAppOfArity ``Quot.mk 3 then return none
          let result := Expr.app arguments[argumentPosition]! constructor.appArg!
          let arity := constructorPosition + 1
          if arity < arguments.size then
            return some (mkAppRange result arity arguments.size arguments)
          else return some result
        else return none) methods).HeadWF (fun _ => True) := by
    dsimp only
    split
    · simp only [pure_bind]
      dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.whnf]
      refine (valid.whnf _).bind fun constructor _ => ?_
      split
      · exact TypeChecker.M.HeadWF.pure trivial
      · split <;> exact TypeChecker.M.HeadWF.pure trivial
    · exact TypeChecker.M.HeadWF.pure trivial
  split
  · exact continuation 5 3
  · split
    · exact continuation 4 3
    · exact TypeChecker.M.HeadWF.pure trivial

theorem toCtorWhenStruct.headWF (environment : Environment)
    (normalize : Expr → TypeChecker.RecM Expr) (parent : Name) (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (normalization : ∀ expression, (normalize expression methods).HeadWF (fun _ => True)) :
    (toCtorWhenStruct environment normalize TypeChecker.Inner.inferType parent expression methods).HeadWF
      (fun _ => True) := by
  unfold toCtorWhenStruct
  simp only [pure_bind]
  split
  · exact TypeChecker.M.HeadWF.pure trivial
  · dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
    refine (valid.inferType expression true).bind fun inferred _ => ?_
    refine (normalization inferred).bind fun normalized _ => ?_
    split
    · exact TypeChecker.M.HeadWF.pure trivial
    · dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
      refine (valid.inferType normalized true).bind fun inferred _ => ?_
      refine (normalization inferred).bind fun sort _ => ?_
      split <;> exact TypeChecker.M.HeadWF.pure trivial

theorem toCtorWhenK.headWF (environment : Environment)
    (normalize : Expr → TypeChecker.RecM Expr) (info : RecursorVal) (expression : Expr)
    (isK : info.k = true) (methods : TypeChecker.Methods) (valid : methods.HeadWF)
    (normalization : ∀ expression, (normalize expression methods).HeadWF (fun _ => True)) :
    (toCtorWhenK environment normalize TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
      info expression methods).HeadWF (fun _ => True) := by
  unfold toCtorWhenK
  simp only [isK, if_true, pure_bind]
  dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
  refine (valid.inferType expression true).bind fun inferred _ => ?_
  refine (normalization inferred).bind fun type _ => ?_
  cases found : type.getAppFn <;> try exact TypeChecker.M.HeadWF.pure trivial
  rename_i parent levels
  dsimp only
  by_cases matching : (parent != info.getMajorInduct) = true
  · simp only [matching, if_true]
    exact TypeChecker.M.HeadWF.pure trivial
  · rw [if_neg matching]
    have finish : ((match mkNullaryCtor environment type info.numParams with
        | some constructor => do
          let inferred ← TypeChecker.Inner.inferType constructor
          let equal ← TypeChecker.Inner.isDefEq type inferred
          pure (if equal then constructor else expression)
        | none => pure expression) methods).HeadWF (fun _ => True) := by
      cases mkNullaryCtor environment type info.numParams with
      | none => exact TypeChecker.M.HeadWF.pure trivial
      | some constructor =>
        dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
        refine (valid.inferType constructor true).bind fun inferred _ => ?_
        refine (TypeChecker.Inner.isDefEq.headWF type inferred methods valid).bind fun equal _ => ?_
        exact TypeChecker.M.HeadWF.pure trivial
    by_cases metavariables : type.hasExprMVar = true
    · simp only [metavariables, if_true, Std.Legacy.Range.forIn'_eq_forIn'_range',
        ← apply_ite, List.forIn'_pure]
      generalize scan : (forIn' (m := Id) (_ : List Nat)
        (⟨none, PUnit.unit⟩ : MProd (Option Expr) PUnit) _) = scanned
      rcases scanned with ⟨result, ignored⟩
      cases result with
      | some result => exact TypeChecker.M.HeadWF.pure trivial
      | none =>
        cases chosen : mkNullaryCtor environment type info.numParams <;> simp only [chosen] at finish ⊢
        all_goals
          dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.pure, StateT.bind,
            Except.pure, Except.bind] at finish ⊢
          exact finish
    · have noMetavariables := Bool.eq_false_iff.mpr metavariables
      simp only [noMetavariables, Bool.false_eq_true, if_false, ← apply_ite]
      cases chosen : mkNullaryCtor environment type info.numParams <;>
        (simp only [chosen] at finish ⊢; exact finish)

theorem inductiveReduceRec.headWF (environment : Environment) (expression : Expr)
    (normalize : Expr → TypeChecker.RecM Expr) (methods : TypeChecker.Methods)
    (valid : methods.HeadWF)
    (normalization : ∀ expression, (normalize expression methods).HeadWF (fun _ => True)) :
    (inductiveReduceRec environment expression normalize TypeChecker.Inner.inferType
      TypeChecker.Inner.isDefEq methods).HeadWF (fun _ => True) := by
  unfold inductiveReduceRec
  cases expression.getAppFn <;> try exact TypeChecker.M.HeadWF.pure trivial
  rename_i name levels
  dsimp only
  cases environment.find? name with
  | none => exact TypeChecker.M.HeadWF.pure trivial
  | some information =>
    cases information <;> try exact TypeChecker.M.HeadWF.pure trivial
    rename_i info
    dsimp only
    cases expression.getAppArgs[info.getMajorIdx]? with
    | none => exact TypeChecker.M.HeadWF.pure trivial
    | some major =>
      simp only [pure_bind]
      dsimp only [Bind.bind, ReaderT.bind]
      by_cases isK : info.k = true
      case' pos =>
        simp only [isK, if_true]
        dsimp only [Bind.bind, ReaderT.bind]
        refine (toCtorWhenK.headWF environment normalize info major isK methods valid normalization).bind
          fun adapted _ => ?_
      case' neg =>
        rw [if_neg isK]
        let adapted := major
      all_goals
        dsimp only [Bind.bind, ReaderT.bind]
        refine (normalization adapted).bind fun normalized _ => ?_
        cases normalized with
        | lit literal =>
          cases literal with
          | natVal value =>
            dsimp only
            cases getRecRuleFor info (.natLitToConstructor value) <;>
              repeat' first | exact TypeChecker.M.HeadWF.pure trivial | dsimp only | split
          | strVal text =>
            dsimp only [Bind.bind, ReaderT.bind]
            refine (normalization (.strLitToConstructor text)).bind fun major _ => ?_
            cases getRecRuleFor info major <;>
              repeat' first | exact TypeChecker.M.HeadWF.pure trivial | dsimp only | split
        | _ =>
          dsimp only [Bind.bind, ReaderT.bind]
          refine (toCtorWhenStruct.headWF environment normalize info.getMajorInduct _ methods valid normalization).bind
            fun major _ => ?_
          cases getRecRuleFor info major <;>
            repeat' first | exact TypeChecker.M.HeadWF.pure trivial | dsimp only | split

theorem TypeChecker.Inner.reduceRecursor.headWF (expression : Expr) (cheapRec cheapProj : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (reduceRecursor expression cheapRec cheapProj methods).HeadWF (fun _ => True) := by
  unfold reduceRecursor
  simp only [pure_bind]
  dsimp only [Bind.bind, ReaderT.bind]
  apply TypeChecker.M.HeadWF.getEnv
  intro environment
  have inductiveFrame : ((do
      if let some reduced ← inductiveReduceRec environment expression
          (fun expression => if cheapRec then whnfCore expression cheapRec cheapProj else whnf expression)
          inferType isDefEq then return some reduced
      return none) methods).HeadWF (fun _ => True) := by
    dsimp only [Bind.bind, ReaderT.bind]
    refine (inductiveReduceRec.headWF environment expression _ methods valid ?_).bind fun reduced _ => ?_
    · intro source
      cases cheapRec
      · exact (valid.whnf source).mono fun _ _ => trivial
      · exact (valid.whnfCore source true cheapProj).mono fun _ _ => trivial
    · cases reduced <;> exact TypeChecker.M.HeadWF.pure trivial
  split
  · dsimp only [Bind.bind, ReaderT.bind]
    refine (quotReduceRec.headWF expression methods valid).bind fun reduced _ => ?_
    cases reduced
    · exact inductiveFrame
    · exact TypeChecker.M.HeadWF.pure trivial
  · exact inductiveFrame

theorem TypeChecker.Inner.whnfCore'.headWFOfMethods (expression : Expr) (cheapRec cheapProj : Bool)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (whnfCore' expression cheapRec cheapProj methods).HeadWF NativeHeadClean :=
  whnfCore'.headWF expression cheapRec cheapProj methods valid
    (fun expression cheapRec cheapProj => reduceRecursor.headWF expression cheapRec cheapProj methods valid)

theorem TypeChecker.Inner.whnf'.headWFOfMethods (expression : Expr)
    (methods : TypeChecker.Methods) (valid : methods.HeadWF) :
    (whnf' expression methods).HeadWF NativeHeadClean :=
  whnf'.headWF expression methods valid
    (fun expression cheapRec cheapProj => reduceRecursor.headWF expression cheapRec cheapProj methods valid)

theorem TypeChecker.Methods.withFuel.zero_headWF : (withFuel 0).HeadWF := by
  constructor
  · intro expression cheapRec cheapProj
    exact TypeChecker.M.HeadWF.throw .deepRecursion _
  · intro expression
    exact TypeChecker.M.HeadWF.throw .deepRecursion _
  · intro expression inferOnly
    exact TypeChecker.M.HeadWF.throw .deepRecursion _
  · intro first second
    exact TypeChecker.M.HeadWF.throw .deepRecursion _

theorem TypeChecker.Methods.withFuel.whnfCore_succ_headWF (fuel : Nat) (valid : (withFuel fuel).HeadWF)
    (expression : Expr) (cheapRec cheapProj : Bool) :
    ((withFuel (fuel + 1)).whnfCore expression cheapRec cheapProj).HeadWF NativeHeadClean :=
  TypeChecker.Inner.whnfCore'.headWFOfMethods expression cheapRec cheapProj (withFuel fuel) valid

theorem TypeChecker.Methods.withFuel.whnf_succ_headWF (fuel : Nat) (valid : (withFuel fuel).HeadWF)
    (expression : Expr) : ((withFuel (fuel + 1)).whnf expression).HeadWF NativeHeadClean :=
  TypeChecker.Inner.whnf'.headWFOfMethods expression (withFuel fuel) valid

end Lean4Lean
