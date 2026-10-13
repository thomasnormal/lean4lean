import Lean4Lean.Verify.InductiveHeaderContinuation
import Lean4Lean.Verify.InductiveMetadata

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata
open private Lean4Lean.AddInductive.readWF Lean4Lean.AddInductive.bindWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.bindHeaderResultWF from Lean4Lean.Verify.InductiveHeaderTraces

theorem NativeValueFrame.absentBefore (frame : NativeValueFrame before after)
    (beforeWF : before.constants.WF) (absent : after.find? name = none) : before.find? name = none := by
  cases found : before.find? name with
  | none => rfl
  | some info =>
    have present : before.constants.find? name = some info := by
      simpa only [Kernel.Environment.find?, beforeWF.find?'_eq_find?] using found
    have retained := frame.lookups present
    have retained : after.find? name = some info := by
      simpa only [Kernel.Environment.find?, frame.map_wf.find?'_eq_find?] using retained
    rw [absent] at retained
    contradiction

theorem TypeChecker.Inner.inferProj.missingConstructors
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state finalState : TypeChecker.State)
    (requested : Name) (position : Nat) (value source normalized : Expr) (header : InductiveVal)
    (levels : List Level)
    (normalization : methods.whnf source context state = .ok (normalized, finalState))
    (head : normalized.getAppFn = .const header.name levels)
    (lookup : context.env.find? header.name = some (.inductInfo header))
    (missing : ∀ constructor ∈ header.ctors, context.env.find? constructor = none) :
    (TypeChecker.Inner.inferProj requested position value source methods context state).WF fun _ => False := by
  intro result accepted
  simp only [TypeChecker.Inner.inferProj, Expr.withApp_eq] at accepted
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, TypeChecker.Inner.whnf] at accepted
  rw [normalization] at accepted
  dsimp only [Except.bind] at accepted
  dsimp only [TypeChecker.getEnv, liftM, Functor.map, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure] at accepted
  dsimp only [Except.pure, Except.bind] at accepted
  rw [head] at accepted
  by_cases same : requested = header.name
  · simp only [same, bne_self_eq_false, Bool.false_eq_true, if_false] at accepted
    dsimp [Kernel.Environment.get] at accepted
    rw [lookup] at accepted
    dsimp only [Bind.bind, Pure.pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
      StateT.lift, Except.bind, Except.pure] at accepted
    cases constructors : header.ctors with
    | nil =>
      simp [constructors] at accepted
      change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
      contradiction
    | cons constructor rest =>
      cases rest with
      | nil =>
        have absent := missing constructor (by simp [constructors])
        simp [constructors, absent] at accepted
        split at accepted <;>
          change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted <;>
          contradiction
      | cons =>
        simp [constructors] at accepted
        change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
        contradiction
  · simp [same] at accepted
    change (Except.error _ : Except Kernel.Exception (Expr × TypeChecker.State)) = .ok result at accepted
    contradiction

theorem TypeChecker.Inner.tryEtaStructCore.missingConstructor
    (methods : TypeChecker.Methods) (context : TypeChecker.Context) (state : TypeChecker.State)
    (value constructor : Expr) (name : Name) (levels : List Level)
    (head : constructor.getAppFn = .const name levels) (missing : context.env.find? name = none) :
    (TypeChecker.Inner.tryEtaStructCore value constructor methods context state).WF fun _ => False := by
  intro result accepted
  simp only [TypeChecker.Inner.tryEtaStructCore] at accepted
  rw [head] at accepted
  dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
    Except.pure, Except.bind] at accepted
  dsimp [Kernel.Environment.get] at accepted
  rw [missing] at accepted
  change (Except.error _ : Except Kernel.Exception (Bool × TypeChecker.State)) = .ok result at accepted
  contradiction

theorem TypeChecker.Inner.isDefEqUnitLike.missingConstructor
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state inferredState finalState : TypeChecker.State) (first second source normalized : Expr)
    (header : InductiveVal) (constructor : Name) (levels : List Level)
    (inferred : methods.inferType first true context state = .ok (source, inferredState))
    (normalization : methods.whnf source context inferredState = .ok (normalized, finalState))
    (head : normalized.getAppFn = .const header.name levels)
    (lookup : context.env.find? header.name = some (.inductInfo header))
    (notRecursive : header.isRec = false) (constructors : header.ctors = [constructor])
    (noIndices : header.numIndices = 0) (missing : context.env.find? constructor = none) :
    (TypeChecker.Inner.isDefEqUnitLike first second methods context state).WF fun _ => False := by
  intro result accepted
  simp only [TypeChecker.Inner.isDefEqUnitLike] at accepted
  dsimp only [Bind.bind, ReaderT.bind, StateT.bind, TypeChecker.Inner.inferType,
    TypeChecker.Inner.whnf] at accepted
  rw [inferred] at accepted
  dsimp only [Except.bind] at accepted
  rw [normalization] at accepted
  dsimp only [Except.bind] at accepted
  rw [head] at accepted
  dsimp only [TypeChecker.getEnv, liftM, MonadLift.monadLift, MonadLiftT.monadLift,
    MonadReader.read, readThe, MonadReaderOf.read, ReaderT.read,
    Pure.pure, Bind.bind, ReaderT.bind, StateT.bind, ReaderT.pure, StateT.pure,
    Except.pure, Except.bind] at accepted
  dsimp [Kernel.Environment.get] at accepted
  rw [lookup] at accepted
  dsimp only [Bind.bind, Pure.pure, ReaderT.bind, ReaderT.pure, StateT.bind, StateT.pure,
    StateT.lift, Except.bind, Except.pure] at accepted
  rcases header with ⟨⟨_, _, _⟩, _, _, _, _, _, _, _, _⟩
  dsimp only at notRecursive constructors noIndices
  cases notRecursive
  cases constructors
  cases noIndices
  simp [missing, Bind.bind, ReaderT.bind, StateT.bind, StateT.lift, Except.bind] at accepted

namespace AddInductive

def ConstructorNames (types : Array InductiveType) : List Name :=
  types.toList.flatMap (fun type => type.ctors.map Constructor.name)

def ConstructorsFresh (env : Kernel.Environment) (types : Array InductiveType) : Prop :=
  ∀ type ∈ types, ∀ constructor ∈ type.ctors, env.find? constructor.name = none

theorem ConstructorsFresh.inShadow (fresh : ConstructorsFresh actual types)
    (agreement : HeaderAxiomAgreement actual shadow) : ConstructorsFresh shadow types :=
  fun type member constructor present => (agreement.none_iff constructor.name).mp
    (fresh type member constructor present)

theorem _root_.Lean4Lean.HeaderAxiomLookupAgreement.missingChangedHeader
    (agreement : HeaderAxiomLookupAgreement (fun name => ∃ type ∈ types, type.name = name) actual shadow)
    (constructorHeaders : ∀ type ∈ types, ∃ header,
      actual.find? type.name = some (.inductInfo header) ∧ header.ctors = type.ctors.map Constructor.name)
    (fresh : ConstructorsFresh actual types) (name : Name) (header : InductiveVal)
    (lookup : actual.find? name = some (.inductInfo header))
    (different : actual.find? name ≠ shadow.find? name) :
    ∀ constructor ∈ header.ctors, actual.find? constructor = none := by
  rcases agreement name with same | ⟨⟨type, member, key⟩, _⟩
  · exact False.elim (different same)
  · obtain ⟨source, sourceLookup, constructors⟩ := constructorHeaders type member
    rw [key] at sourceLookup
    have equal : source = header := ConstantInfo.inductInfo.inj (Option.some.inj (sourceLookup.symm.trans lookup))
    subst source
    intro name present
    rw [constructors] at present
    obtain ⟨constructor, constructorMember, rfl⟩ := List.mem_map.mp present
    exact fresh type member constructor constructorMember

private theorem registerConstructorFreshness (constructors : List Constructor) (index : Nat)
    (env : Kernel.Environment) (allowPrimitive : Bool)
    (makeInfo : Nat → Constructor → ConstructorVal)
    (names : ∀ index constructor, (makeInfo index constructor).name = constructor.name)
    (envWF : env.constants.WF) :
    (constructors.foldlM (fun (state : Nat × Kernel.Environment) (constructor : Constructor) => do
      state.2.checkName constructor.name allowPrimitive
      pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo state.1 constructor)))) (index, env)).WF
      fun state => NativeValueFrame env state.2 ∧
        (∀ constructor ∈ constructors, env.find? constructor.name = none) ∧
        (constructors.map Constructor.name).Nodup ∧
        ∀ constructor ∈ constructors, (state.2.find? constructor.name).isSome := by
  induction constructors generalizing index env with
  | nil => exact .pure ⟨.refl envWF, by simp, by simp, by simp⟩
  | cons constructor constructors induction =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (checkName.WF envWF constructor.name allowPrimitive).bind fun _ ⟨fresh, _⟩ => ?_
    have infoFresh : env.constants.find? (ConstantInfo.ctorInfo (makeInfo index constructor)).name = none := by
      simpa only [Kernel.Environment.find?, envWF.find?'_eq_find?,
        ConstantInfo.name, ConstantInfo.toConstantVal, names] using fresh
    have step := NativeValueFrame.addConst (ci := .ctorInfo (makeInfo index constructor)) envWF infoFresh rfl
    obtain ⟨_, self, _⟩ := Lean4Lean.AddInductive.addFresh env (.ctorInfo (makeInfo index constructor)) envWF infoFresh
    have self : (env.add (.ctorInfo (makeInfo index constructor))).find? constructor.name =
        some (.ctorInfo (makeInfo index constructor)) := by
      simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, names] using self
    refine (induction (index + 1) _ step.map_wf).mono ?_
    rintro state ⟨restFrame, restFresh, distinct, installed⟩
    refine ⟨step.trans restFrame, ?_, ?_, ?_⟩
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · simpa only [Kernel.Environment.find?, envWF.find?'_eq_find?] using fresh
      · exact step.absentBefore envWF (restFresh candidate member)
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, distinct⟩
      rintro present
      obtain ⟨candidate, member, equal⟩ := List.mem_map.mp present
      have absent := restFresh candidate member
      rw [equal, self] at absent
      contradiction
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · have retained := restFrame.lookups
          (show (env.add (.ctorInfo (makeInfo index candidate))).constants.find? candidate.name =
            some (.ctorInfo (makeInfo index candidate)) from by
            simpa only [Kernel.Environment.find?, step.map_wf.find?'_eq_find?] using self)
        have retained : state.2.find? candidate.name = some (.ctorInfo (makeInfo index candidate)) := by
          simpa only [Kernel.Environment.find?, restFrame.map_wf.find?'_eq_find?] using retained
        simp [retained]
      · exact installed candidate member

private theorem registerTypeConstructorFreshness (types : List InductiveType)
    (env : Kernel.Environment) (allowPrimitive : Bool)
    (makeInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (names : ∀ type index constructor, (makeInfo type index constructor).name = constructor.name)
    (envWF : env.constants.WF) :
    (types.foldlM (fun (current : Kernel.Environment) (type : InductiveType) => do
      let state ← type.ctors.foldlM (fun (state : Nat × Kernel.Environment) (constructor : Constructor) => do
        state.2.checkName constructor.name allowPrimitive
        pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo type state.1 constructor)))) (0, current)
      pure state.2) env).WF fun result => NativeValueFrame env result ∧
        (∀ type ∈ types, ∀ constructor ∈ type.ctors, env.find? constructor.name = none) ∧
        (types.flatMap (fun (type : InductiveType) => type.ctors.map Constructor.name)).Nodup := by
  induction types generalizing env with
  | nil => exact .pure ⟨.refl envWF, by simp, by simp⟩
  | cons type types induction =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (registerConstructorFreshness type.ctors 0 env allowPrimitive (makeInfo type)
      (names type) envWF).bind ?_
    rintro state ⟨headFrame, headFresh, headDistinct, installed⟩
    refine (induction state.2 headFrame.map_wf).mono ?_
    rintro result ⟨tailFrame, tailFresh, tailDistinct⟩
    refine ⟨headFrame.trans tailFrame, ?_, ?_⟩
    · intro candidate member constructor present
      rcases List.mem_cons.mp member with rfl | member
      · exact headFresh constructor present
      · exact headFrame.absentBefore envWF (tailFresh candidate member constructor present)
    · rw [List.flatMap_cons, List.nodup_append]
      refine ⟨headDistinct, tailDistinct, ?_⟩
      intro name headMember laterName tailMember same
      obtain ⟨constructor, present, equal⟩ := List.mem_map.mp headMember
      obtain ⟨candidate, member, rest⟩ := List.mem_flatMap.mp tailMember
      obtain ⟨later, laterMember, laterEqual⟩ := List.mem_map.mp rest
      have some := installed constructor present
      have absent := tailFresh candidate member later laterMember
      rw [laterEqual, ← same, ← equal] at absent
      rw [absent] at some
      cases some

theorem declareConstructors.freshness (stats : InductiveStats) (types : Array InductiveType)
    (isUnsafe : Bool) (reader : Context) (envWF : reader.env.constants.WF) :
    (declareConstructors stats types isUnsafe reader).WF fun final =>
      NativeValueFrame reader.env final ∧ ConstructorsFresh reader.env types ∧ (ConstructorNames types).Nodup := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  let makeInfo (type : InductiveType) (index : Nat) (constructor : Constructor) : ConstructorVal := {
    name := constructor.name, levelParams := reader.lparams, type := constructor.type, induct := type.name,
    cidx := index, numParams := stats.params.size, isUnsafe
    numFields := assert! declareConstructors.arity 0 constructor.type ≥ stats.params.size;
      declareConstructors.arity 0 constructor.type - stats.params.size }
  refine (registerTypeConstructorFreshness types.toList reader.env reader.allowPrimitive makeInfo
    (by intros; rfl) envWF).mono ?_
  rintro final ⟨frame, fresh, distinct⟩
  exact ⟨frame, by simpa only [ConstructorsFresh, Array.mem_toList_iff] using fresh, distinct⟩

theorem InductiveStats.HeaderMetadata.constructorsMissing
    (metadata : InductiveStats.HeaderMetadata stats nparams types numNested isUnsafe universes actual)
    (fresh : ConstructorsFresh actual types) (parent : Nat) (bound : parent < types.size) :
    ∃ header, actual.find? types[parent].name = some (.inductInfo header) ∧
      ∀ constructor ∈ header.ctors, actual.find? constructor = none := by
  refine ⟨_, metadata parent bound, ?_⟩
  intro name member
  obtain ⟨constructor, present, rfl⟩ := List.mem_map.mp member
  exact fresh types[parent] (Array.getElem_mem bound) constructor present

theorem checkInductiveTypes.registeredConstructorFreshness
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (reader : Context) (envWF : reader.env.constants.WF) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      reader.HeaderFrame current ∧
      stats.HeaderMetadata nparams types numNested isUnsafe current.lparams actual ∧
      ConstructorsFresh actual types ∧ (ConstructorNames types).Nodup ∧
      NativeValueFrame actual final ∧
      checkConstructors types stats isUnsafe { current with env := actual } = .ok () := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current sizes frame
  have currentWF : current.env.constants.WF := frame.env.symm ▸ envWF
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro actual declared
  obtain ⟨actualWF, _, metadata⟩ := declareInductiveTypes.metadata stats nparams types numNested isUnsafe
    current currentWF sizes.1 actual declared
  change ((checkConstructors types stats isUnsafe >>= fun _ => _) { current with env := actual }).WF _
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro checked accepted
  cases checked
  refine (declareConstructors.freshness stats types isUnsafe { current with env := actual } actualWF).bind ?_
  rintro final ⟨registered, fresh, distinct⟩
  intro _ _
  exact ⟨stats, current, actual, final, frame, metadata, fresh, distinct, registered, accepted⟩

theorem run.registeredConstructorFreshness (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (reader : Context) (envWF : reader.env.constants.WF) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      reader.HeaderFrame current ∧
      stats.HeaderMetadata nparams types.toArray numNested (reader.safety != .safe) current.lparams actual ∧
      ConstructorsFresh actual types.toArray ∧ (ConstructorNames types.toArray).Nodup ∧
      NativeValueFrame actual final ∧
      checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.registeredConstructorFreshness nparams types.toArray numNested
    (reader.safety != .safe) _ reader envWF

theorem checkInductiveTypes.freshConstructorAxiomContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ConstructorsFresh actual types ∧ ConstructorsFresh stage.shadow types ∧
        (ConstructorNames types).Nodup ∧ NativeValueFrame actual final ∧
        checkConstructors types stats isUnsafe { current with env := actual } = .ok () := by
  refine checkInductiveTypes.withHeaderAxiomContinuation nparams types numNested isUnsafe
    (next := fun stats actual => do
      checkConstructors types stats isUnsafe
      let final ← declareConstructors stats types isUnsafe
      withEnv final (next stats actual))
    (post := fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        ConstructorsFresh actual types ∧ ConstructorsFresh stage.shadow types ∧
        (ConstructorNames types).Nodup ∧ NativeValueFrame actual final ∧
        checkConstructors types stats isUnsafe { current with env := actual } = .ok ())
    root reader aligned empty different constants definitions ordinary safetyBound ?_
  intro stats current actual stage
  change ((checkConstructors types stats isUnsafe >>= fun _ => _) { current with env := actual }).WF _
  apply Lean4Lean.AddInductive.bindHeaderResultWF
  intro checked accepted
  cases checked
  refine (declareConstructors.freshness stats types isUnsafe { current with env := actual } stage.actualWF).bind ?_
  rintro final ⟨registered, fresh, distinct⟩
  intro _ _
  exact ⟨stats, current, actual, final, stage, fresh, fresh.inShadow stage.agreement, distinct, registered, accepted⟩

theorem run.freshConstructorAxiomContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        ConstructorsFresh actual types.toArray ∧ ConstructorsFresh stage.shadow types.toArray ∧
        (ConstructorNames types.toArray).Nodup ∧ NativeValueFrame actual final ∧
        checkConstructors types.toArray stats (reader.safety != .safe) { current with env := actual } = .ok () := by
  have sameSafety : root.safety = reader.safety := congrArg TypeChecker.Context.safety aligned
  have safetyBound : root.safety ≤ if reader.safety != .safe then .unsafe else .safe := by
    rw [← sameSafety]
    cases mode : root.safety with
    | safe => decide
    | «unsafe» => decide
    | «partial» => exact False.elim (ordinarySafety mode)
  unfold run
  apply Lean4Lean.AddInductive.readWF
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  exact checkInductiveTypes.freshConstructorAxiomContinuation nparams types.toArray numNested
    (reader.safety != .safe) _ root reader aligned empty different constants definitions ordinary safetyBound

end AddInductive
end Lean4Lean
