import Lean4Lean.Verify.InductiveHeaderRecursiveTransport

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def M.SuccessTransport (actual shadow : M resultType) (actualReader shadowReader : Context) : Prop :=
  Except.SuccessTransport (actual actualReader) (shadow shadowReader)

theorem M.SuccessTransport.bind (actual shadow : M firstType)
    (actualNext shadowNext : firstType → M resultType) (actualReader shadowReader : Context)
    (initial : M.SuccessTransport actual shadow actualReader shadowReader)
    (continuation : ∀ result, actual actualReader = .ok result →
      M.SuccessTransport (actualNext result) (shadowNext result) actualReader shadowReader) :
    M.SuccessTransport (actual >>= actualNext) (shadow >>= shadowNext) actualReader shadowReader := by
  exact Except.SuccessTransport.bind _ _ _ _ initial continuation

theorem M.SuccessTransport.pure (value : resultType) (actualReader shadowReader : Context) :
    M.SuccessTransport (pure value) (pure value) actualReader shadowReader := .refl _

theorem M.SuccessTransport.throw (error : Kernel.Exception) (actualReader shadowReader : Context) :
    M.SuccessTransport (throw error : M resultType) (throw error) actualReader shadowReader := by
  intro result accepted
  contradiction

def Context.checkerReader (reader : Context) : TypeChecker.Context :=
  { env := reader.env, lctx := reader.lctx, lparams := reader.lparams,
    safety := reader.safety, fuel := reader.fuel }

theorem M.SuccessTransport.typeChecker (actual shadow : TypeChecker.M resultType)
    (reader : Context) (environment : Kernel.Environment)
    (transport : TypeChecker.M.SuccessTransport actual shadow reader.checkerReader
      { reader.checkerReader with env := environment } {}) :
    M.SuccessTransport (monadLift actual) (monadLift shadow) reader { reader with env := environment } := by
  intro result accepted
  change Except.map Prod.fst (actual reader.checkerReader {}) = .ok result at accepted
  change Except.map Prod.fst (shadow { reader.checkerReader with env := environment } {}) = .ok result
  cases found : actual reader.checkerReader {} with
  | error error =>
    simp only [found, Except.map] at accepted
    cases accepted
  | ok returned =>
    rw [transport returned found]
    simpa only [found, Except.map] using accepted

theorem M.SuccessTransport.forIn' (items : List itemType) (initial : resultType)
    (actual shadow : (item : itemType) → item ∈ items → resultType → M (ForInStep resultType))
    (actualReader shadowReader : Context)
    (step : ∀ item member value,
      M.SuccessTransport (actual item member value) (shadow item member value) actualReader shadowReader) :
    M.SuccessTransport (forIn' items initial actual) (forIn' items initial shadow)
      actualReader shadowReader := by
  induction items generalizing initial with
  | nil => exact .pure _ _ _
  | cons first items induction =>
    rw [List.forIn'_cons, List.forIn'_cons]
    apply M.SuccessTransport.bind _ _ _ _ _ _ (step first (by simp) initial)
    intro selected accepted
    cases selected with
    | done value => exact .pure _ _ _
    | yield value => exact induction value _ _ (fun item member value => step item (by simp [member]) value)

theorem checkPositivity.loop.headerAxiomTransport (stats : InductiveStats) (constructor : Name)
    (index : Nat) (type : Expr) (fuel : Nat) (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow) :
    M.SuccessTransport (checkPositivity.loop stats constructor index type fuel)
      (checkPositivity.loop stats constructor index type fuel) reader { reader with env := shadow } := by
  induction fuel generalizing type reader with
  | zero => exact .throw _ _ _
  | succ fuel induction =>
    rw [checkPositivity.loop.eq_def]
    dsimp only
    apply M.SuccessTransport.bind _ _ _ _ _ _
      (.typeChecker _ _ _ _ (TypeChecker.whnf.headerAxiomTransport reader.checkerReader shadow metadata {} type))
    intro normal accepted
    cases occurrence : hasIndOcc stats.indConsts normal with
    | false => simp only [Bool.not_false, if_true]; exact .pure _ _ _
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false, pure_bind]
      cases normal with
      | forallE name domain body binder =>
        cases domainOccurrence : hasIndOcc stats.indConsts domain with
        | true => simp only [domainOccurrence, if_true]; exact .throw _ _ _
        | false =>
          simp only [domainOccurrence, Bool.false_eq_true, if_false]
          change M.SuccessTransport
            (checkPositivity.loop stats constructor index (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) fuel)
            (checkPositivity.loop stats constructor index (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) fuel)
            { reader with
              ngen := reader.ngen.next
              lctx := reader.lctx.mkLocalDecl ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) binder }
            _
          exact induction _ _ metadata
      | _ =>
        cases valid : isValidIndApp? stats _ with
        | none => exact .throw _ _ _
        | some parent => exact .pure _ _ _

theorem checkPositivity.headerAxiomTransport (stats : InductiveStats) (type : Expr)
    (constructor : Name) (index : Nat) (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow) :
    M.SuccessTransport (checkPositivity stats type constructor index)
      (checkPositivity stats type constructor index) reader { reader with env := shadow } :=
  checkPositivity.loop.headerAxiomTransport stats constructor index type reader.fuel.inductiveFuel reader shadow metadata

theorem checkConstructors.loop.headerAxiomTransport (stats : InductiveStats) (isUnsafe : Bool)
    (parent : Nat) (constructor : Name) (type : Expr) (index fuel : Nat)
    (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow) :
    M.SuccessTransport (checkConstructors.loop stats isUnsafe parent constructor type index fuel)
      (checkConstructors.loop stats isUnsafe parent constructor type index fuel)
      reader { reader with env := shadow } := by
  induction fuel generalizing type index reader with
  | zero => exact .throw _ _ _
  | succ fuel induction =>
    cases type with
    | forallE name domain body binder =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      cases selected : stats.params[index]? with
      | some parameter =>
        dsimp only
        apply M.SuccessTransport.bind _ _ _ _ _ _ (.refl _)
        intro stored accepted
        apply M.SuccessTransport.bind _ _ _ _ _ _
          (.typeChecker _ _ _ _ (TypeChecker.isDefEq.headerAxiomTransport reader.checkerReader shadow metadata {} domain stored))
        intro equal accepted
        cases equal with
        | false => simp only [Bool.false_eq_true, if_false]; exact .throw _ _ _
        | true =>
          simp only [if_true, pure_bind]
          exact induction _ _ reader metadata
      | none =>
        dsimp only
        apply M.SuccessTransport.bind _ _ _ _ _ _
          (.typeChecker _ _ _ _ (TypeChecker.ensureType.headerAxiomTransport reader.checkerReader shadow metadata {} domain))
        intro sort accepted
        by_cases universeAccepted : (stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' sort.sortLevel!) = true
        · simp only [universeAccepted, if_true, pure_bind]
          have opened : M.SuccessTransport
              (withLocalDecl name binder (peelTypeAnnotations domain) fun argument =>
                checkConstructors.loop stats isUnsafe parent constructor (body.instantiate1 argument) (index + 1) fuel)
              (withLocalDecl name binder (peelTypeAnnotations domain) fun argument =>
                checkConstructors.loop stats isUnsafe parent constructor (body.instantiate1 argument) (index + 1) fuel)
              reader { reader with env := shadow } := by
            change M.SuccessTransport
              (checkConstructors.loop stats isUnsafe parent constructor (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) (index + 1) fuel)
              (checkConstructors.loop stats isUnsafe parent constructor (body.instantiate1 (.fvar ⟨reader.ngen.curr⟩)) (index + 1) fuel)
              { reader with
                ngen := reader.ngen.next
                lctx := reader.lctx.mkLocalDecl ⟨reader.ngen.curr⟩ name (peelTypeAnnotations domain) binder }
              _
            exact induction _ _ _ metadata
          cases isUnsafe with
          | false =>
            simp only [Bool.not_false, if_true]
            apply M.SuccessTransport.bind _ _ _ _ _ _
              (checkPositivity.headerAxiomTransport stats domain constructor index reader shadow metadata)
            intro _ accepted
            exact opened
          | true => simp only [Bool.not_true, Bool.false_eq_true, if_false]; exact opened
        · simp only [universeAccepted]; exact .throw _ _ _
    | _ =>
      rw [checkConstructors.loop.eq_def]
      dsimp only
      cases valid : isValidIndAppIdx stats _ parent with
      | false => exact .throw _ _ _
      | true => exact .pure _ _ _

theorem checkNoMVarNoFVar.headerAxiomTransport (actual shadow : Kernel.Environment)
    (name : Name) (type : Expr) :
    Except.SuccessTransport (actual.checkNoMVarNoFVar name type) (shadow.checkNoMVarNoFVar name type) := by
  intro result accepted
  cases metavariables : type.hasMVar <;> cases variables : type.hasFVar <;>
    simp [Kernel.Environment.checkNoMVarNoFVar, Kernel.Environment.checkNoMVar,
      Kernel.Environment.checkNoFVar, metavariables, variables, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at accepted ⊢

def nativeConstructorCheck (types : Array InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (environment : Kernel.Environment) : M Unit := do
  for bound : parent in [:types.size] do
    let type := types[parent]
    let mut found : NameSet := {}
    for constructor in type.ctors do
      if found.contains constructor.name then
        throw <| .other s!"duplicate constructor name '{constructor.name}'"
      found := found.insert constructor.name
      environment.checkNoMVarNoFVar constructor.name constructor.type
      _ ← TypeChecker.checkType constructor.type
      checkConstructors.loop stats isUnsafe parent constructor.name constructor.type 0
        (← readThe Context).fuel.inductiveFuel

theorem checkConstructors.nativeConstructorCheck (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (reader : Context) :
    checkConstructors types stats isUnsafe reader =
      AddInductive.nativeConstructorCheck types stats isUnsafe reader.env reader := rfl

theorem nativeConstructorCheck.headerAxiomTransport (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow) :
    M.SuccessTransport (nativeConstructorCheck types stats isUnsafe reader.env)
      (nativeConstructorCheck types stats isUnsafe shadow) reader { reader with env := shadow } := by
  unfold nativeConstructorCheck
  apply M.SuccessTransport.bind _ _ _ _ _ _
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply M.SuccessTransport.forIn'
    intro parent bound value
    apply M.SuccessTransport.bind _ _ _ _ _ _
    · change M.SuccessTransport (forIn' (m := M) _ _ _) (forIn' (m := M) _ _ _) _ _
      apply M.SuccessTransport.forIn'
      intro constructor member found
      dsimp only
      by_cases duplicate : found.contains constructor.name = true
      · simp only [duplicate, if_true]
        exact .throw _ _ _
      · simp only [duplicate, pure_bind]
        apply M.SuccessTransport.bind _ _ _ _ _ _
          (by
            change Except.SuccessTransport (reader.env.checkNoMVarNoFVar constructor.name constructor.type)
              (shadow.checkNoMVarNoFVar constructor.name constructor.type)
            exact checkNoMVarNoFVar.headerAxiomTransport reader.env shadow constructor.name constructor.type)
        intro _ accepted
        apply M.SuccessTransport.bind _ _ _ _ _ _
          (.typeChecker _ _ _ _ (TypeChecker.checkType.headerAxiomTransport reader.checkerReader shadow metadata {} constructor.type))
        intro checked accepted
        apply M.SuccessTransport.bind _ _ _ _ _ _
          (checkConstructors.loop.headerAxiomTransport stats isUnsafe parent constructor.name constructor.type 0
            reader.fuel.inductiveFuel reader shadow metadata)
        intro _ accepted
        exact .pure _ _ _
    · intro found accepted
      exact .pure _ _ _
  · intro _ accepted
    exact .pure _ _ _

theorem checkConstructors.headerAxiomTransport (types : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (reader : Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed reader.env shadow) :
    M.SuccessTransport (checkConstructors types stats isUnsafe)
      (checkConstructors types stats isUnsafe) reader { reader with env := shadow } := by
  intro result accepted
  rw [checkConstructors.nativeConstructorCheck] at accepted ⊢
  exact nativeConstructorCheck.headerAxiomTransport types stats isUnsafe reader shadow metadata result accepted

end Lean4Lean.AddInductive
