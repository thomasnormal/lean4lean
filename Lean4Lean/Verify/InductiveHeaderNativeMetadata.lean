import Lean4Lean.Verify.InductiveConstructorContinuation

namespace Lean4Lean
open Lean hiding Environment Exception

theorem FreshRegistrationTrace.quotInit
    (trace : FreshRegistrationTrace allowed original result) : result.quotInit = original.quotInit := by
  induction trace with
  | refl => rfl
  | step previous information record fresh induction =>
    simpa only [Kernel.Environment.add_quotInit] using induction

theorem FreshRegistrationTrace.headerConstructorOrigins
    (trace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (wellFormed : original.constants.WF) (name : Name) (information : ConstructorVal)
    (found : actual.find? name = some (.ctorInfo information)) :
    original.find? name = some (.ctorInfo information) := by
  rcases trace.lookup wellFormed name (.ctorInfo information) found with retained | ⟨header, impossible⟩
  · exact retained
  · cases impossible

theorem FreshRegistrationTrace.headerRecursorOrigins
    (trace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (wellFormed : original.constants.WF) (name : Name) (information : RecursorVal)
    (found : actual.find? name = some (.recInfo information)) :
    original.find? name = some (.recInfo information) := by
  rcases trace.lookup wellFormed name (.recInfo information) found with retained | ⟨header, impossible⟩
  · exact retained
  · cases impossible

theorem FreshRegistrationTrace.headerConstructorParents
    (trace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (wellFormed : original.constants.WF) (closed : NativeConstructorParentClosure original) :
    NativeConstructorParentClosure actual := by
  intro name information found
  obtain ⟨header, parent, member⟩ := closed name information
    (trace.headerConstructorOrigins wellFormed name information found)
  exact ⟨header, (trace.preserves wellFormed).2 information.induct (.inductInfo header) parent, member⟩

theorem FreshRegistrationTrace.headerRecursorShadowParents
    (actualTrace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (shadowTrace : FreshRegistrationTrace HeaderAxiomRegistrationRecord original shadow)
    (wellFormed : original.constants.WF) (closed : NativeRecursorParentsClosed original) :
    ∀ name information, actual.find? name = some (.recInfo information) →
      ∃ header, shadow.find? information.getMajorInduct = some (.inductInfo header) := by
  intro name information found
  obtain ⟨header, parent⟩ := closed name information
    (actualTrace.headerRecursorOrigins wellFormed name information found)
  exact ⟨header, (shadowTrace.preserves wellFormed).2 information.getMajorInduct (.inductInfo header) parent⟩

theorem NativeRecursiveHeaderFrame.ofHeaderRegistration (types : Array InductiveType)
    (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (headers : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (actualTrace : FreshRegistrationTrace HeaderRegistrationRecord original actual)
    (shadowTrace : FreshRegistrationTrace HeaderAxiomRegistrationRecord original shadow)
    (wellFormed : original.constants.WF) (fresh : AddInductive.ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original)
    (recursors : NativeRecursorParentsClosed original) :
    NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual shadow := by
  exact .beforeConstructors agreement headers fresh (actualTrace.headerConstructorParents wellFormed constructors)
    (actualTrace.headerRecursorShadowParents shadowTrace wellFormed recursors)
    (actualTrace.quotInit.trans shadowTrace.quotInit.symm)

namespace AddInductive

theorem HeaderAxiomContinuation.nativeFrame
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env) :
    NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual stage.shadow := by
  apply NativeRecursiveHeaderFrame.ofHeaderRegistration types stage.lookups stage.constructorHeaders
    stage.actualRegistration stage.shadowRegistration stage.initialWF fresh
  · simpa only [stage.before.frame.env] using constructors
  · simpa only [stage.before.frame.env] using recursors

theorem HeaderAxiomContinuation.acceptedConstructorsFromInitial
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (isUnsafe : Bool) (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env) :
    (checkConstructors types stats isUnsafe { reader with env := actual }).WF fun _ =>
      checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { reader with env := stage.shadow } := by
  intro result accepted
  cases result
  have metadata := stage.nativeFrame fresh constructors recursors
  have transported := checkConstructors.headerAxiomTransport types stats isUnsafe
    { reader with env := actual } stage.shadow metadata () accepted
  exact ⟨transported, checkConstructors.acceptedTraces types stats isUnsafe
    { reader with env := stage.shadow } () transported⟩

theorem checkInductiveTypes.nativeConstructorAxiomContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ConstructorsFresh actual types ∧ ConstructorsFresh stage.shadow types ∧
        (ConstructorNames types).Nodup ∧ NativeValueFrame actual final ∧
        NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types, type.name = name) actual stage.shadow ∧
        checkConstructors types stats isUnsafe { current with env := actual } = .ok () ∧
        checkConstructors types stats isUnsafe { current with env := stage.shadow } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { current with env := stage.shadow } := by
  refine (checkInductiveTypes.freshConstructorAxiomContinuation nparams types numNested isUnsafe next
    root reader aligned empty different constants definitions ordinary safetyBound).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained, accepted⟩
  obtain ⟨shadowAccepted, traces⟩ := stage.acceptedConstructorsFromInitial isUnsafe fresh constructors recursors () accepted
  exact ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    stage.nativeFrame fresh constructors recursors, accepted, shadowAccepted, traces⟩

theorem run.nativeConstructorAxiomContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ConstructorsFresh actual types.toArray ∧ ConstructorsFresh stage.shadow types.toArray ∧
        (ConstructorNames types.toArray).Nodup ∧ NativeValueFrame actual final ∧
        NativeRecursiveHeaderFrame (fun name => ∃ type ∈ types.toArray, type.name = name) actual stage.shadow ∧
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () ∧
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := stage.shadow } = .ok () ∧
        stats.AcceptedConstructorTraces types.toArray (reader.safety != .safe) { current with env := stage.shadow } := by
  refine (run.freshConstructorAxiomContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained, accepted⟩
  obtain ⟨shadowAccepted, traces⟩ := stage.acceptedConstructorsFromInitial (reader.safety != .safe)
    fresh constructors recursors () accepted
  exact ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    stage.nativeFrame fresh constructors recursors, accepted, shadowAccepted, traces⟩

end AddInductive
end Lean4Lean
