import Lean4Lean.Verify.InductiveHeaderWHNFTransport

namespace Lean4Lean
open Lean hiding Environment Exception

structure NativeMethodTransport (actualMethods shadowMethods : TypeChecker.Methods)
    (actualContext shadowContext : TypeChecker.Context) : Prop where
  isDefEqCore : ∀ state first second,
    TypeChecker.M.SuccessTransport (actualMethods.isDefEqCore first second)
      (shadowMethods.isDefEqCore first second) actualContext shadowContext state
  whnfCore : ∀ state expression cheapRec cheapProj,
    TypeChecker.M.SuccessTransport (actualMethods.whnfCore expression cheapRec cheapProj)
      (shadowMethods.whnfCore expression cheapRec cheapProj) actualContext shadowContext state
  whnf : ∀ state expression,
    TypeChecker.M.SuccessTransport (actualMethods.whnf expression)
      (shadowMethods.whnf expression) actualContext shadowContext state
  inferType : ∀ state expression inferOnly,
    TypeChecker.M.SuccessTransport (actualMethods.inferType expression inferOnly)
      (shadowMethods.inferType expression inferOnly) actualContext shadowContext state

theorem NativeMethodTransport.refl (methods : TypeChecker.Methods) (context : TypeChecker.Context) :
    NativeMethodTransport methods methods context context := by
  constructor <;> intros <;> exact Except.SuccessTransport.refl _

def NativeRecursorParentFrame (actual shadow : Kernel.Environment) : Prop :=
  ∀ name info, actual.find? name = some (.recInfo info) →
    actual.find? info.getMajorInduct = shadow.find? info.getMajorInduct

theorem NativeRecursorParentFrame.ofShadowParents
    (agreement : HeaderAxiomLookupAgreement changed actual shadow)
    (parents : ∀ name info, actual.find? name = some (.recInfo info) →
      ∃ header, shadow.find? info.getMajorInduct = some (.inductInfo header)) :
    NativeRecursorParentFrame actual shadow := by
  intro name info found
  obtain ⟨header, parent⟩ := parents name info found
  exact agreement.stableInductiveParent _ header parent

def NativeRecursorParentsClosed (environment : Kernel.Environment) : Prop :=
  ∀ name info, environment.find? name = some (.recInfo info) →
    ∃ header, environment.find? info.getMajorInduct = some (.inductInfo header)

theorem NativeRecursorParentFrame.ofNativeOrigins
    (agreement : HeaderAxiomLookupAgreement changed actual shadow)
    (parents : NativeRecursorParentsClosed original)
    (origins : ∀ name info, actual.find? name = some (.recInfo info) →
      original.find? name = some (.recInfo info))
    (retained : ∀ name header, original.find? name = some (.inductInfo header) →
      shadow.find? name = some (.inductInfo header)) : NativeRecursorParentFrame actual shadow := by
  apply NativeRecursorParentFrame.ofShadowParents agreement
  intro name info found
  obtain ⟨header, parent⟩ := parents name info (origins name info found)
  exact ⟨header, retained _ header parent⟩

theorem NativeMethodTransport.inferWhnf
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport
      (do actualMethods.whnf (← actualMethods.inferType expression true))
      (do shadowMethods.whnf (← shadowMethods.inferType expression true)) actualContext shadowContext state := by
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (transport.inferType state expression true)
  intro type finalState _
  exact transport.whnf finalState type

theorem NativeMethodTransport.inferDefEq
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (type expression : Expr) :
    TypeChecker.M.SuccessTransport
      (do TypeChecker.Inner.isDefEq type (← actualMethods.inferType expression true) actualMethods)
      (do TypeChecker.Inner.isDefEq type (← shadowMethods.inferType expression true) shadowMethods)
      actualContext shadowContext state := by
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (transport.inferType state expression true)
  intro inferred finalState _
  exact TypeChecker.Inner.isDefEq.transport _ _ _ _ _ _ _ (transport.isDefEqCore finalState type inferred)

theorem NativeMethodTransport.inductiveReduction
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport
      (inductiveReduceRec actualContext.env expression
        (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
        TypeChecker.Inner.inferType
        TypeChecker.Inner.isDefEq actualMethods)
      (inductiveReduceRec shadowContext.env expression
        (fun major => if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major)
        TypeChecker.Inner.inferType
        TypeChecker.Inner.isDefEq shadowMethods) actualContext shadowContext state := by
  let normalize := fun major =>
    if cheapRec then TypeChecker.Inner.whnfCore major cheapRec cheapProj else TypeChecker.Inner.whnf major
  have normalization : ∀ currentState major,
      TypeChecker.M.SuccessTransport (normalize major actualMethods) (normalize major shadowMethods)
        actualContext shadowContext currentState := by
    intro currentState major
    cases cheapRec
    · exact transport.whnf currentState major
    · exact transport.whnfCore currentState major true cheapProj
  have inferNormalization : ∀ currentState major,
      TypeChecker.M.SuccessTransport
        ((do normalize (← TypeChecker.Inner.inferType major true)) actualMethods)
        ((do normalize (← TypeChecker.Inner.inferType major true)) shadowMethods)
        actualContext shadowContext currentState := by
    intro currentState major
    dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
    apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (transport.inferType currentState major true)
    intro type finalState _
    exact normalization finalState type
  apply inductiveReduceRec.headerAxiomNormalizationTransport normalize _ _ _ _ agreement state expression
  · intro info major entry
    exact parents _ info entry.recursor
  · intro info major entry isK
    exact inferNormalization state major
  · intro info major entry isK type finalState constructor accepted matching found
    exact transport.inferDefEq finalState type constructor
  · intro info major adapted adaptedState receipt
    exact normalization adaptedState adapted
  · intro info major adapted adaptedState text normalizedState receipt accepted
    exact normalization normalizedState (.strLitToConstructor text)
  · intro info major adapted adaptedState normalized normalizedState receipt accepted literal structureLike constructor
    exact inferNormalization normalizedState normalized
  · intro info major adapted adaptedState normalized normalizedState receipt accepted literal structureLike constructor type finalState inferred matching
    exact inferNormalization finalState type

theorem NativeMethodTransport.quotientReduction
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (quotReduceRec expression TypeChecker.Inner.whnf actualMethods)
      (quotReduceRec expression TypeChecker.Inner.whnf shadowMethods) actualContext shadowContext state := by
  apply quotReduceRec.transport
  · intro lift inBounds
    exact transport.whnf state _
  · intro ind inBounds
    exact transport.whnf state _

theorem NativeMethodTransport.recursorReduction
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceRecursor expression cheapRec cheapProj shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.reduceRecursor.headerAxiomTransport _ _ _ _ state expression cheapRec cheapProj quotInit
  · intro initialized
    exact transport.quotientReduction state expression
  · intro finalState reached
    exact transport.inductiveReduction agreement parents finalState expression cheapRec cheapProj

theorem NativeMethodTransport.projectionReduction
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (index : Nat) (source : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceProj index source cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.reduceProj index source cheapRec cheapProj shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.reduceProj.headerAxiomTransport _ _ _ _ agreement state index source cheapRec cheapProj
  · cases cheapProj
    · exact transport.whnf state source
    · exact transport.whnfCore state source cheapRec true
  · intro text finalState accepted
    exact transport.whnf finalState (.strLitToConstructor text)

theorem NativeMethodTransport.coreCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool) :
    NativeCoreCallbacks actualMethods shadowMethods actualContext shadowContext state expression cheapRec cheapProj := by
  constructor
  · intro fvar cache declaration value found defined
    exact transport.whnfCore state value cheapRec cheapProj
  · intro name domain value body nondependent shape cache
    exact transport.whnfCore state _ cheapRec cheapProj
  · intro application cache
    exact transport.whnfCore state _ cheapRec cheapProj
  · intro name domain body binder finalState receipt
    exact transport.whnfCore finalState _ cheapRec cheapProj
  · intro normalized finalState receipt lambda changed
    exact transport.whnfCore finalState _ cheapRec cheapProj
  · intro normalized finalState receipt lambda unchanged
    exact transport.recursorReduction agreement parents quotInit finalState expression cheapRec cheapProj
  · intro normalized finalState reduced reducedState receipt lambda unchanged accepted
    exact transport.whnfCore reducedState reduced cheapRec cheapProj
  · intro parent index source shape cache
    exact transport.projectionReduction agreement state index source cheapRec cheapProj
  · intro parent index source reduced reducedState shape cache accepted
    exact transport.whnfCore reducedState reduced cheapRec cheapProj

theorem NativeMethodTransport.whnfCoreStep
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (locals : actualContext.lctx = shadowContext.lctx)
    (state : TypeChecker.State) (expression : Expr) (cheapRec cheapProj : Bool) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj actualMethods)
      (TypeChecker.Inner.whnfCore' expression cheapRec cheapProj shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.whnfCore'.headerAxiomTransport _ _ _ _ state expression cheapRec cheapProj locals
    (transport.coreCallbacks agreement parents quotInit state expression.consumeMData cheapRec cheapProj)

theorem NativeMethodTransport.naturalReduction
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.reduceNat expression actualMethods)
      (TypeChecker.Inner.reduceNat expression shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.reduceNat.transport
  · intro arity successor
    exact transport.whnf state _
  · intro name levels first second shape operation
    refine ⟨transport.whnf state _, ?_⟩
    intro normalized finalState value accepted literal
    exact transport.whnf finalState _

theorem NativeMethodTransport.whnfCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (state : TypeChecker.State) (expression : Expr) :
    NativeWhnfCallbacks actualMethods shadowMethods actualContext shadowContext state expression := by
  constructor
  · intro current currentState remaining reached
    exact transport.coreCallbacks agreement parents quotInit currentState current.consumeMData false false
  · intro current currentState remaining normalized normalizedState reached accepted native
    exact transport.naturalReduction normalizedState normalized

theorem NativeMethodTransport.whnfStep
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (locals : actualContext.lctx = shadowContext.lctx)
    (budget : actualContext.whnfBudget ≤ shadowContext.whnfBudget)
    (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.whnf' expression actualMethods)
      (TypeChecker.Inner.whnf' expression shadowMethods) actualContext shadowContext state :=
  TypeChecker.Inner.whnf'.headerAxiomTransport _ _ _ _ agreement locals state expression
    (transport.whnfCallbacks agreement parents quotInit state expression.consumeMData) (fun _ => budget)

theorem TypeChecker.Methods.withFuel.zeroTransport (actualContext shadowContext : TypeChecker.Context) :
    NativeMethodTransport (withFuel 0) (withFuel 0) actualContext shadowContext := by
  constructor <;> intros <;> intro result accepted <;> cases accepted

theorem TypeChecker.Methods.withFuel.normalizationStep
    (depth : Nat) (actualContext shadowContext : TypeChecker.Context)
    (transport : NativeMethodTransport (withFuel depth) (withFuel depth) actualContext shadowContext)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (locals : actualContext.lctx = shadowContext.lctx)
    (budget : actualContext.whnfBudget ≤ shadowContext.whnfBudget) :
    (∀ state expression cheapRec cheapProj,
      M.SuccessTransport ((withFuel (depth + 1)).whnfCore expression cheapRec cheapProj)
        ((withFuel (depth + 1)).whnfCore expression cheapRec cheapProj) actualContext shadowContext state) ∧
    (∀ state expression,
      M.SuccessTransport ((withFuel (depth + 1)).whnf expression)
        ((withFuel (depth + 1)).whnf expression) actualContext shadowContext state) := by
  constructor
  · exact transport.whnfCoreStep agreement parents quotInit locals
  · exact transport.whnfStep agreement parents quotInit locals budget

theorem TypeChecker.Methods.withFuel.normalizationDepthOne
    (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (parents : NativeRecursorParentFrame actualContext.env shadowContext.env)
    (quotInit : actualContext.env.quotInit = shadowContext.env.quotInit)
    (locals : actualContext.lctx = shadowContext.lctx)
    (budget : actualContext.whnfBudget ≤ shadowContext.whnfBudget) :
    (∀ state expression cheapRec cheapProj,
      M.SuccessTransport ((withFuel 1).whnfCore expression cheapRec cheapProj)
        ((withFuel 1).whnfCore expression cheapRec cheapProj) actualContext shadowContext state) ∧
    (∀ state expression,
      M.SuccessTransport ((withFuel 1).whnf expression)
        ((withFuel 1).whnf expression) actualContext shadowContext state) :=
  normalizationStep 0 actualContext shadowContext (zeroTransport actualContext shadowContext)
    agreement parents quotInit locals budget

end Lean4Lean
