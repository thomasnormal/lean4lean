import Lean4Lean.Verify.InductiveHeaderDefEqCoreTransport
import Lean4Lean.Verify.InductiveHeaderWHNFMethodTransport

namespace Lean4Lean
open Lean hiding Environment Exception

structure NativeRecursiveHeaderFrame (changed : Name → Prop) (actual shadow : Kernel.Environment) : Prop where
  agreement : HeaderAxiomLookupAgreement changed actual shadow
  recursors : NativeRecursorParentFrame actual shadow
  constructors : ∀ name information, actual.find? name = some (.ctorInfo information) →
    actual.find? information.induct = shadow.find? information.induct
  projections : ∀ parent, NativeProjectionMetadataFrame actual shadow parent
  quotInit : actual.quotInit = shadow.quotInit

structure NativeHeaderReaderFrame (actual shadow : TypeChecker.Context)
    (actualEnvironment shadowEnvironment : Kernel.Environment) : Prop where
  actualLookup : actual.env = actualEnvironment
  shadowReader : shadow = { actual with env := shadowEnvironment }

theorem NativeRecursiveHeaderFrame.refl (changed : Name → Prop) (environment : Kernel.Environment) :
    NativeRecursiveHeaderFrame changed environment environment := by
  constructor
  · exact .refl _ _
  · unfold NativeRecursorParentFrame
    intros
    rfl
  · intros
    rfl
  · intro parent
    unfold NativeProjectionMetadataFrame
    intros
    exact .inl rfl
  · rfl

def NativeConstructorParentClosure (environment : Kernel.Environment) : Prop :=
  ∀ name information, environment.find? name = some (.ctorInfo information) →
    ∃ header, environment.find? information.induct = some (.inductInfo header) ∧ name ∈ header.ctors

theorem NativeRecursiveHeaderFrame.beforeConstructors
    (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (constructorHeaders : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : AddInductive.ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure actual)
    (recursors : ∀ name information, actual.find? name = some (.recInfo information) →
      ∃ header, shadow.find? information.getMajorInduct = some (.inductInfo header))
    (quotInit : actual.quotInit = shadow.quotInit) :
    NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual shadow := by
  refine ⟨agreement, .ofShadowParents agreement recursors, ?_, ?_, quotInit⟩
  · intro name information found
    obtain ⟨header, parent, member⟩ := constructors name information found
    by_cases stable : actual.find? information.induct = shadow.find? information.induct
    · exact stable
    · have absent := agreement.missingChangedHeader constructorHeaders fresh information.induct header parent stable name member
      rw [absent] at found
      contradiction
  · exact fun parent => .ofConstructorFreshness agreement constructorHeaders fresh parent

theorem NativeHeaderReaderFrame.shadowLookup
    (frame : NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment) : shadow.env = shadowEnvironment := by
  rw [frame.shadowReader]

theorem NativeHeaderReaderFrame.locals
    (frame : NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment) : actual.lctx = shadow.lctx := by
  rw [frame.shadowReader]

theorem NativeHeaderReaderFrame.openLocal
    (frame : NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (name : Name) (binder : BinderInfo) (type : Expr) :
    NativeHeaderReaderFrame (actual.openLocal state name binder type) (shadow.openLocal state name binder type)
      actualEnvironment shadowEnvironment := by
  refine ⟨frame.actualLookup, ?_⟩
  rw [frame.shadowReader]
  rfl

theorem NativeHeaderReaderFrame.openLet
    (frame : NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (name : Name) (type value : Expr) :
    NativeHeaderReaderFrame (actual.openLet state name type value) (shadow.openLet state name type value)
      actualEnvironment shadowEnvironment := by
  refine ⟨frame.actualLookup, ?_⟩
  rw [frame.shadowReader]
  rfl

theorem NativeHeaderReaderFrame.inferComparisonContext
    (frame : NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment) (argument : Expr) :
    NativeHeaderReaderFrame (actual.inferComparisonContext argument) (shadow.inferComparisonContext argument)
      actualEnvironment shadowEnvironment := by
  cases gate : argument.isAppOfArity `eagerReduce 2
  all_goals simp only [TypeChecker.Context.inferComparisonContext, gate, Bool.false_eq_true, if_false, if_true]
  · exact frame
  · refine ⟨frame.actualLookup, ?_⟩
    rw [frame.shadowReader]

def NativeScopedMethodTransport (actualMethods shadowMethods : TypeChecker.Methods)
    (actualEnvironment shadowEnvironment : Kernel.Environment) : Prop :=
  ∀ actual shadow, NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment →
    NativeMethodTransport actualMethods shadowMethods actual shadow

theorem NativeLambdaReachable.readerFrame
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (reached : NativeLambdaReachable methods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) :
    NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment := by
  induction reached with
  | initial => exact frame
  | opened reached accepted inductionHypothesis => exact inductionHypothesis.openLocal _ _ _ _

theorem NativeForallReachable.readerFrame
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (reached : NativeForallReachable methods actualContext shadowContext state root inferOnly
      actual shadow fvars levels current currentState) :
    NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment := by
  induction reached with
  | initial => exact frame
  | opened reached accepted inductionHypothesis => exact inductionHypothesis.openLocal _ _ _ _

theorem NativeLetReachable.readerFrame
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (reached : NativeLetReachable methods actualContext shadowContext state root inferOnly
      actual shadow fvars current currentState) :
    NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment := by
  induction reached with
  | initial => exact frame
  | opened reached accepted inductionHypothesis => exact inductionHypothesis.openLet _ _ _ _

theorem NativeBinderComparisonReachable.readerFrame
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (reached : NativeBinderComparisonReachable kind methods actualContext shadowContext state first second substitution
      actual shadow currentState currentFirst currentSecond current) :
    NativeHeaderReaderFrame actual shadow actualEnvironment shadowEnvironment := by
  induction reached with
  | initial => exact frame
  | opened reached accepted dependent inductionHypothesis => exact inductionHypothesis.openLocal _ _ _ _
  | closed reached accepted nondependent inductionHypothesis => exact inductionHypothesis

theorem NativeMethodTransport.sortCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool) :
    NativeSortCallbacks actualMethods shadowMethods actualContext shadowContext state expression inferOnly := by
  constructor <;> intros
  · exact transport.inferType _ _ _
  · exact transport.whnf _ _

theorem NativeMethodTransport.letDomainCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (domain value : Expr) (inferOnly : Bool) :
    NativeLetDomainCallbacks actualMethods shadowMethods actualContext shadowContext state domain value inferOnly := by
  constructor <;> intros
  · exact transport.sortCallbacks _ _ _
  · exact transport.inferType _ _ _
  · exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.inferAppCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    NativeInferAppCallbacks actualMethods shadowMethods actualContext shadowContext state expression := by
  constructor
  · exact transport.inferType _ _ _
  · intros
    constructor
    intros
    exact transport.whnf _ _

theorem NativeMethodTransport.projectionPropCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    NativeProjectionPropCallbacks actualMethods shadowMethods actualContext shadowContext state expression := by
  constructor <;> intros
  · exact transport.inferType _ _ _
  · exact transport.whnf _ _

theorem NativeMethodTransport.projectionCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (parent : Name) (index : Nat) (source sourceType : Expr) :
    NativeProjectionCallbacks actualMethods shadowMethods actualContext shadowContext state parent index source sourceType := by
  constructor
  · exact transport.whnf _ _
  · intros
    constructor
    · intros
      constructor
      intros
      exact transport.whnf _ _
    · intros
      exact transport.projectionPropCallbacks _ _
    · intros
      constructor <;> intros
      · exact transport.whnf _ _
      · exact transport.projectionPropCallbacks _ _
    · intros
      constructor <;> intros
      · exact transport.whnf _ _
      · exact transport.projectionPropCallbacks _ _

theorem NativeScopedMethodTransport.inferCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (root : Expr) (inferOnly : Bool) :
    NativeInferMethodCallbacks actualMethods shadowMethods actualContext shadowContext state root inferOnly := by
  have transport := methodTransport actualContext shadowContext frame
  constructor
  · intros
    exact transport.inferAppCallbacks _ _
  · intros
    constructor
    · intro actual shadow fvars name domain body binder currentState reached checking
      exact (methodTransport actual shadow (reached.readerFrame frame)).sortCallbacks _ _ _
    · intro actual shadow fvars current currentState reached terminal
      exact (methodTransport actual shadow (reached.readerFrame frame)).inferType _ _ _
  · intros
    constructor
    · intro actual shadow fvars levels name domain body binder currentState reached
      exact (methodTransport actual shadow (reached.readerFrame frame)).sortCallbacks _ _ _
    · intro actual shadow fvars levels current currentState reached terminal
      exact (methodTransport actual shadow (reached.readerFrame frame)).sortCallbacks _ _ _
  · intros
    constructor
    · intro actual shadow fvars name domain value body nondependent currentState reached checking
      exact (methodTransport actual shadow (reached.readerFrame frame)).letDomainCallbacks _ _ _ _
    · intro actual shadow fvars current currentState reached terminal
      exact (methodTransport actual shadow (reached.readerFrame frame)).inferType _ _ _
  · intros
    apply TypeChecker.Inner.inferProj.headerAxiomStagedTransport _ _ _ _
      (by simpa only [frame.actualLookup, frame.shadowLookup] using metadata.agreement)
    · simpa only [frame.actualLookup, frame.shadowLookup] using metadata.projections _
    · exact transport.projectionCallbacks _ _ _ _ _
  · intros
    exact transport.whnf _ _
  · intro function argument currentState functionType functionState normalized normalizedState argumentType argumentState reached checking inferred cast argumentInferred
    exact (methodTransport _ _ (frame.inferComparisonContext argument)).isDefEqCore _ _ _

theorem NativeScopedMethodTransport.inferStep
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (expression : Expr) (inferOnly : Bool) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.inferType' expression inferOnly actualMethods)
      (TypeChecker.Inner.inferType' expression inferOnly shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.inferType'.headerAxiomMethodTransport _ _ _ _
    (by simpa only [frame.actualLookup, frame.shadowLookup] using metadata.agreement) frame.locals
  · rw [frame.shadowReader]
  · rw [frame.shadowReader]
  · exact methodTransport.inferCallbacks metadata frame state expression inferOnly

theorem NativeScopedMethodTransport.binderCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (kind : NativeBinderKind) (state : TypeChecker.State) (first second : Expr) (substitution : Array Expr) :
    NativeBinderComparisonCallbacks kind actualMethods shadowMethods actualContext shadowContext state first second substitution := by
  constructor
  · intro actual shadow currentState firstName secondName firstDomain secondDomain firstBody secondBody firstBinder secondBinder current reached different
    exact (methodTransport actual shadow (reached.readerFrame frame)).isDefEqCore _ _ _
  · intro actual shadow currentState currentFirst currentSecond current reached terminal
    exact (methodTransport actual shadow (reached.readerFrame frame)).isDefEqCore _ _ _

theorem NativeScopedMethodTransport.quickCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeQuickBodyCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  cases first <;> cases second
  all_goals first
    | exact methodTransport.binderCallbacks frame _ _ _ _ _
    | exact (methodTransport _ _ frame).isDefEqCore _ _ _
    | trivial

theorem NativeMethodTransport.appComparisonCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (first second : Expr) :
    NativeAppComparisonCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros <;> exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.etaCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (first second : Expr) :
    NativeEtaExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact transport.inferType _ _ _
  · exact transport.whnf _ _
  · exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.proofCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (first second : Expr) :
    NativeProofIrrelCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact transport.inferType _ _ _
  · exact transport.projectionPropCallbacks _ _
  · exact transport.inferType _ _ _
  · exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.stringCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (first second : Expr) :
    NativeStringExpansionCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor
  intros
  exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.etaStructCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeEtaStructCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor
  · intro name levels information head lookup arity structureLike
    have found : actualEnvironment.find? name = some (.ctorInfo information) := by
      simpa only [frame.actualLookup] using lookup
    simpa only [frame.actualLookup, frame.shadowLookup] using metadata.constructors name information found
  · intros
    exact transport.inferType _ _ _
  · intros
    exact transport.inferType _ _ _
  · intros
    exact transport.isDefEqCore _ _ _
  · intros
    constructor
    intros
    exact transport.isDefEqCore _ _ _

theorem NativeMethodTransport.unitCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeUnitLikeCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor
  · exact transport.inferType _ _ _
  · intros
    exact transport.whnf _ _
  · intros
    constructor
    · intros
      simpa only [frame.actualLookup, frame.shadowLookup] using metadata.projections _
    · intros
      exact transport.inferType _ _ _
    · intros
      exact transport.isDefEqCore _ _ _

theorem NativeScopedMethodTransport.fallbackCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqFallbackCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  have transport := methodTransport _ _ frame
  constructor
  · intros
    exact transport.appComparisonCallbacks _ _ _
  · intros
    constructor <;> intros <;> exact transport.etaCallbacks _ _ _
  · intros
    constructor <;> intros <;> exact transport.etaStructCallbacks metadata frame _ _ _
  · intros
    constructor <;> intros <;> exact transport.stringCallbacks _ _ _
  · intros
    exact transport.unitCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.deltaQuickCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaQuickCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  unfold NativeDeltaQuickCallbacks
  intros
  exact methodTransport.quickCallbacks frame _ _ _

theorem NativeMethodTransport.deltaUnfoldCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    NativeDeltaUnfoldCallbacks actualMethods shadowMethods actualContext shadowContext state expression := by
  unfold NativeDeltaUnfoldCallbacks
  intros
  exact transport.whnfCore _ _ _ _

theorem NativeScopedMethodTransport.deltaSingleCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (side : NativeDeltaSide) (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaSingleCallbacks side actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor
  · exact (methodTransport _ _ frame).deltaUnfoldCallbacks _ _
  · intros
    exact methodTransport.deltaQuickCallbacks frame _ _ _

theorem NativeScopedMethodTransport.deltaPairCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaPairCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).deltaUnfoldCallbacks _ _
  · exact (methodTransport _ _ frame).deltaUnfoldCallbacks _ _
  · exact methodTransport.deltaQuickCallbacks frame _ _ _

theorem NativeScopedMethodTransport.deltaArgumentsCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaArgumentsCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · unfold NativeDeltaArgumentCallbacks
    intros
    exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact methodTransport.deltaPairCallbacks frame _ _ _
  · exact methodTransport.deltaPairCallbacks frame _ _ _

theorem NativeScopedMethodTransport.deltaProjectionCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (side : NativeDeltaSide) (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaProjectionCallbacks side actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).whnfCore _ _ _ _
  · exact methodTransport.deltaQuickCallbacks frame _ _ _
  · exact methodTransport.deltaSingleCallbacks frame _ _ _ _

theorem NativeScopedMethodTransport.deltaStepCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (plan : NativeLazyDeltaPlan) (state : TypeChecker.State) (first second : Expr) :
    NativeLazyDeltaStepCallbacks plan actualMethods shadowMethods actualContext shadowContext state first second := by
  cases plan with
  | unknown => trivial
  | projection side => exact methodTransport.deltaProjectionCallbacks frame side _ _ _
  | unfold side => exact methodTransport.deltaSingleCallbacks frame side _ _ _
  | both same =>
    cases same
    · exact methodTransport.deltaPairCallbacks frame _ _ _
    · exact methodTransport.deltaArgumentsCallbacks frame _ _ _

theorem NativeMethodTransport.deltaNatCallbacks
    (transport : NativeMethodTransport actualMethods shadowMethods actualContext shadowContext)
    (state : TypeChecker.State) (expression : Expr) :
    NativeDeltaNatCallbacks actualMethods shadowMethods actualContext shadowContext state expression := by
  constructor
  · intros
    exact transport.whnf _ _
  · intros
    constructor <;> intros <;> exact transport.whnf _ _

theorem NativeScopedMethodTransport.deltaTailCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaTailCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact methodTransport.deltaStepCallbacks frame _ _ _ _

theorem NativeScopedMethodTransport.deltaNaturalCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaNaturalTailCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).deltaNatCallbacks _ _
  · exact (methodTransport _ _ frame).deltaNatCallbacks _ _
  · exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact methodTransport.deltaTailCallbacks frame _ _ _

theorem NativeScopedMethodTransport.deltaRoundCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDeltaRoundCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor
  · constructor
    intros
    exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · intros
    exact methodTransport.deltaNaturalCallbacks frame _ _ _
  · intros
    exact methodTransport.deltaTailCallbacks frame _ _ _

theorem NativeScopedMethodTransport.lazyDeltaCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeLazyDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  unfold NativeLazyDeltaCallbacks
  intros
  exact methodTransport.deltaRoundCallbacks frame _ _ _

theorem NativeScopedMethodTransport.renormalizeCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqRenormalizeCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).whnfCore _ _ _ _
  · exact (methodTransport _ _ frame).whnfCore _ _ _ _
  · exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact methodTransport.fallbackCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.unknownCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqUnknownCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · unfold NativeDefEqSimpleCallbacks
    intros
    exact (methodTransport _ _ frame).isDefEqCore _ _ _
  · exact methodTransport.renormalizeCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.defEqDeltaCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqDeltaCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact methodTransport.lazyDeltaCallbacks frame _ _ _
  · exact methodTransport.unknownCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.defEqProofCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqProofCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).proofCallbacks _ _ _
  · exact methodTransport.defEqDeltaCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.normalizedCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second normalizedFirst normalizedSecond : Expr) :
    NativeDefEqNormalizedCallbacks actualMethods shadowMethods actualContext shadowContext state first second normalizedFirst normalizedSecond := by
  constructor <;> intros
  · exact methodTransport.deltaQuickCallbacks frame _ _ _
  · exact methodTransport.defEqProofCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.cheapCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqCheapCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).whnfCore _ _ _ _
  · exact (methodTransport _ _ frame).whnfCore _ _ _ _
  · exact methodTransport.normalizedCallbacks metadata frame _ _ _ _ _

theorem NativeScopedMethodTransport.shortCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqShortCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact (methodTransport _ _ frame).whnf _ _
  · exact methodTransport.cheapCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.defEqCallbacks
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    NativeDefEqCoreCallbacks actualMethods shadowMethods actualContext shadowContext state first second := by
  constructor <;> intros
  · exact methodTransport.quickCallbacks frame _ _ _
  · exact methodTransport.shortCallbacks metadata frame _ _ _

theorem NativeScopedMethodTransport.defEqStep
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment)
    (frame : NativeHeaderReaderFrame actualContext shadowContext actualEnvironment shadowEnvironment)
    (state : TypeChecker.State) (first second : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEqCore' first second actualMethods)
      (TypeChecker.Inner.isDefEqCore' first second shadowMethods) actualContext shadowContext state := by
  apply TypeChecker.Inner.isDefEqCore'.headerAxiomTransport _ _ _ _
    (by simpa only [frame.actualLookup, frame.shadowLookup] using metadata.agreement)
  · rw [frame.shadowReader]
  · rw [frame.shadowReader]
    exact Nat.le_refl _
  · exact methodTransport.defEqCallbacks metadata frame state first second

theorem NativeScopedMethodTransport.successor
    (methodTransport : NativeScopedMethodTransport actualMethods shadowMethods actualEnvironment shadowEnvironment)
    (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment) :
    NativeScopedMethodTransport
      { isDefEqCore := fun first second => TypeChecker.Inner.isDefEqCore' first second actualMethods
        whnfCore := fun expression cheapRec cheapProj => TypeChecker.Inner.whnfCore' expression cheapRec cheapProj actualMethods
        whnf := fun expression => TypeChecker.Inner.whnf' expression actualMethods
        inferType := fun expression inferOnly => TypeChecker.Inner.inferType' expression inferOnly actualMethods }
      { isDefEqCore := fun first second => TypeChecker.Inner.isDefEqCore' first second shadowMethods
        whnfCore := fun expression cheapRec cheapProj => TypeChecker.Inner.whnfCore' expression cheapRec cheapProj shadowMethods
        whnf := fun expression => TypeChecker.Inner.whnf' expression shadowMethods
        inferType := fun expression inferOnly => TypeChecker.Inner.inferType' expression inferOnly shadowMethods }
      actualEnvironment shadowEnvironment := by
  intro actualContext shadowContext frame
  have transport := methodTransport _ _ frame
  have agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env := by
    simpa only [frame.actualLookup, frame.shadowLookup] using metadata.agreement
  have parents : NativeRecursorParentFrame actualContext.env shadowContext.env := by
    simpa only [frame.actualLookup, frame.shadowLookup] using metadata.recursors
  have quotInit : actualContext.env.quotInit = shadowContext.env.quotInit := by
    simpa only [frame.actualLookup, frame.shadowLookup] using metadata.quotInit
  constructor
  · exact methodTransport.defEqStep metadata frame
  · exact transport.whnfCoreStep agreement parents quotInit frame.locals
  · apply transport.whnfStep agreement parents quotInit frame.locals
    rw [frame.shadowReader]
    exact Nat.le_refl _
  · exact methodTransport.inferStep metadata frame

theorem TypeChecker.Methods.withFuel.headerAxiomTransport
    (depth : Nat) (metadata : NativeRecursiveHeaderFrame changed actualEnvironment shadowEnvironment) :
    NativeScopedMethodTransport (withFuel depth) (withFuel depth) actualEnvironment shadowEnvironment := by
  induction depth with
  | zero =>
    intro actualContext shadowContext frame
    exact zeroTransport actualContext shadowContext
  | succ depth inductionHypothesis => exact inductionHypothesis.successor metadata

theorem TypeChecker.whnf.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.whnf expression) (TypeChecker.whnf expression) context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel context.fuel.recDepth).whnf expression)
    ((TypeChecker.Methods.withFuel context.fuel.recDepth).whnf expression) context { context with env := shadow } state
  exact (TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).whnf state expression

theorem TypeChecker.whnfCore.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.whnfCore expression) (TypeChecker.whnfCore expression) context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel context.fuel.recDepth).whnfCore expression false false)
    ((TypeChecker.Methods.withFuel context.fuel.recDepth).whnfCore expression false false) context { context with env := shadow } state
  exact (TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).whnfCore state expression false false

theorem TypeChecker.inferType.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.inferType expression) (TypeChecker.inferType expression) context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel context.fuel.recDepth).inferType expression true)
    ((TypeChecker.Methods.withFuel context.fuel.recDepth).inferType expression true) context { context with env := shadow } state
  exact (TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).inferType state expression true

theorem TypeChecker.isDefEq.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (first second : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.isDefEq first second) (TypeChecker.isDefEq first second) context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport (TypeChecker.Inner.isDefEq first second (TypeChecker.Methods.withFuel context.fuel.recDepth))
    (TypeChecker.Inner.isDefEq first second (TypeChecker.Methods.withFuel context.fuel.recDepth)) context { context with env := shadow } state
  exact TypeChecker.Inner.isDefEq.transport _ _ _ _ _ _ _
    ((TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).isDefEqCore state first second)

theorem TypeChecker.checkType.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.checkType expression) (TypeChecker.checkType expression) context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport ((TypeChecker.Methods.withFuel context.fuel.recDepth).inferType expression false)
    ((TypeChecker.Methods.withFuel context.fuel.recDepth).inferType expression false) context { context with env := shadow } state
  exact (TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).inferType state expression false

theorem TypeChecker.ensureSort.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression source : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.ensureSort expression source) (TypeChecker.ensureSort expression source)
      context { context with env := shadow } state := by
  change TypeChecker.M.SuccessTransport (TypeChecker.Inner.ensureSortCore expression source (TypeChecker.Methods.withFuel context.fuel.recDepth))
    (TypeChecker.Inner.ensureSortCore expression source (TypeChecker.Methods.withFuel context.fuel.recDepth)) context { context with env := shadow } state
  apply TypeChecker.Inner.ensureSortCore.transport
  intro nonsort
  exact (TypeChecker.Methods.withFuel.headerAxiomTransport _ metadata _ _ ⟨rfl, rfl⟩).whnf state expression

theorem TypeChecker.ensureType.headerAxiomTransport
    (context : TypeChecker.Context) (shadow : Kernel.Environment)
    (metadata : NativeRecursiveHeaderFrame changed context.env shadow) (state : TypeChecker.State) (expression : Expr) :
    TypeChecker.M.SuccessTransport (TypeChecker.ensureType expression) (TypeChecker.ensureType expression) context { context with env := shadow } state := by
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (TypeChecker.inferType.headerAxiomTransport context shadow metadata state expression)
  intro type finalState accepted
  exact TypeChecker.ensureSort.headerAxiomTransport context shadow metadata finalState type expression

end Lean4Lean
