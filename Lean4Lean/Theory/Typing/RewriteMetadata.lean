import Lean4Lean.Theory.Typing.QuotObjects

/-! Actual declaration-history metadata, independent of rewrite matching soundness. -/

namespace Lean4Lean.VEnv

variable {environment extended : VEnv} {name : Lean.Name} {constant : VConstant}
  {definition : VDefVal}

private theorem addConstFresh (added : environment.addConst name constant = some extended) :
    environment.constants name = none := by
  unfold addConst at added
  split at added <;> simp_all

private theorem extensionFresh (extension : environment ≤ extended)
    (fresh : extended.constants name = none) : environment.constants name = none := by
  cases found : environment.constants name with
  | none => rfl
  | some constant =>
    have preserved := extension.constants found
    rw [fresh] at preserved
    cases preserved

private theorem quotientExtension (added : environment.addQuot = some extended) :
    environment ≤ extended ∧
      (∀ name ∈ [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind], environment.constants name = none) ∧
      extended.defeqs = (environment.addDefEq quotDefEq).defeqs := by
  unfold addQuot at added
  obtain ⟨domainEnvironment, domainAdded, remaining⟩ := Option.bind_eq_some_iff.mp added
  obtain ⟨constructorEnvironment, constructorAdded, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨liftEnvironment, liftAdded, remaining⟩ := Option.bind_eq_some_iff.mp remaining
  obtain ⟨inductionEnvironment, inductionAdded, final⟩ := Option.bind_eq_some_iff.mp remaining
  cases final
  have domainExtension := addConst_le domainAdded
  have constructorExtension := domainExtension.trans (addConst_le constructorAdded)
  have liftExtension := constructorExtension.trans (addConst_le liftAdded)
  refine ⟨(liftExtension.trans (addConst_le inductionAdded)).trans addDefEq_le, ?_, ?_⟩
  · intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact addConstFresh domainAdded
    · exact extensionFresh domainExtension (addConstFresh constructorAdded)
    · exact extensionFresh constructorExtension (addConstFresh liftAdded)
    · exact extensionFresh liftExtension (addConstFresh inductionAdded)
  · have preserved := (addConst.defeqs_eq inductionAdded).trans
      ((addConst.defeqs_eq liftAdded).trans
        ((addConst.defeqs_eq constructorAdded).trans (addConst.defeqs_eq domainAdded)))
    simp only [addDefEq, preserved]

private theorem definitionEquationInjective {first second : VDefVal}
    (equal : first.toDefEq = second.toDefEq) : first = second := by
  cases first with
  | mk firstConstant firstValue =>
    cases second with
    | mk secondConstant secondValue =>
      cases firstConstant with
      | mk firstSignature firstName =>
        cases secondConstant with
        | mk secondSignature secondName =>
          cases firstSignature
          cases secondSignature
          simp_all [VDefVal.toDefEq]

private theorem definitionNotQuotient (definition : VDefVal) : definition.toDefEq ≠ quotDefEq := by
  intro equal
  cases congrArg VDefEq.lhs equal

structure RewriteMetadata (environment : VEnv) : Prop where
  classify : ∀ {equation}, environment.defeqs equation →
    equation = quotDefEq ∨ ∃ definition : VDefVal, equation = definition.toDefEq
  lookup : ∀ {definition : VDefVal}, environment.defeqs definition.toDefEq →
    environment.constants definition.name = some definition.toVConstant
  unique : ∀ {first second : VDefVal}, environment.defeqs first.toDefEq →
    environment.defeqs second.toDefEq → first.name = second.name → first = second
  quotientNames : ∀ {definition : VDefVal}, environment.defeqs definition.toDefEq →
    environment.defeqs quotDefEq →
    ∀ name ∈ [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind], definition.name ≠ name

private theorem RewriteMetadata.extend (metadata : RewriteMetadata environment)
    (extension : environment ≤ extended) (preserved : extended.defeqs = environment.defeqs) :
    RewriteMetadata extended where
  classify registered := metadata.classify (by rwa [preserved] at registered)
  lookup registered := extension.constants (metadata.lookup (by rwa [preserved] at registered))
  unique first second equal := metadata.unique
    (by rwa [preserved] at first) (by rwa [preserved] at second) equal
  quotientNames registered initialized := metadata.quotientNames
    (by rwa [preserved] at registered) (by rwa [preserved] at initialized)

private theorem RewriteMetadata.addDefinition (metadata : RewriteMetadata environment)
    (environmentWF : environment.WF)
    (added : environment.addConst definition.name definition.toVConstant = some extended) :
    RewriteMetadata (extended.addDefEq definition.toDefEq) := by
  have fresh := addConstFresh added
  have preserved := addConst.defeqs_eq added
  have extension : environment ≤ extended.addDefEq definition.toDefEq :=
    (addConst_le added).trans addDefEq_le
  have oldDifferent {previous : VDefVal} (registered : environment.defeqs previous.toDefEq) :
      definition.name ≠ previous.name := by
    intro equal
    have found := metadata.lookup registered
    rw [← equal, fresh] at found
    cases found
  have registeredCases {previous : VDefVal}
      (registered : (extended.addDefEq definition.toDefEq).defeqs previous.toDefEq) :
      previous = definition ∨ environment.defeqs previous.toDefEq := by
    rcases registered with newEquation | oldEquation
    · exact .inl (definitionEquationInjective newEquation)
    · exact .inr (by rwa [preserved] at oldEquation)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equation registered
    rcases registered with newEquation | oldEquation
    · exact .inr ⟨definition, newEquation⟩
    · exact metadata.classify (by rwa [preserved] at oldEquation)
  · intro previous registered
    rcases registeredCases registered with rfl | previousRegistered
    · exact addDefEq_le.constants (addConst_self added)
    · exact extension.constants (metadata.lookup previousRegistered)
  · intro first second firstRegistered secondRegistered equal
    rcases registeredCases firstRegistered with rfl | firstPrevious
    · rcases registeredCases secondRegistered with rfl | secondPrevious
      · rfl
      · exact False.elim (oldDifferent secondPrevious equal)
    · rcases registeredCases secondRegistered with rfl | secondPrevious
      · exact False.elim (oldDifferent firstPrevious equal.symm)
      · exact metadata.unique firstPrevious secondPrevious equal
  · intro previous registered initialized
    have oldInitialized : environment.defeqs quotDefEq := by
      rcases initialized with newEquation | oldEquation
      · exact False.elim (definitionNotQuotient definition newEquation.symm)
      · rwa [preserved] at oldEquation
    rcases registeredCases registered with rfl | previousRegistered
    · intro name member equal
      have objects := environmentWF.quotientObjects oldInitialized
      have found : environment.contains name := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        · exact ⟨_, objects.2.2.2.2.1⟩
        · exact ⟨_, objects.2.2.2.1⟩
        · exact ⟨_, objects.2.2.1⟩
        · exact ⟨_, objects.2.1⟩
      obtain ⟨_, found⟩ := found
      rw [← equal, fresh] at found
      cases found
    · exact metadata.quotientNames previousRegistered oldInitialized

private theorem addConstsFresh {environment extended : VEnv} :
    ∀ {definitions : List VDefVal}, environment.addConsts definitions = some extended →
      ∀ definition ∈ definitions, environment.constants definition.name = none
  | [], _, _, member => by cases member
  | first :: rest, added, definition, member => by
    obtain ⟨middle, firstAdded, restAdded⟩ := Option.bind_eq_some_iff.mp added
    rcases List.mem_cons.mp member with rfl | member
    · exact addConstFresh firstAdded
    · exact extensionFresh (addConst_le firstAdded) (addConstsFresh restAdded definition member)

private theorem addConstsUnique {environment extended : VEnv} :
    ∀ {definitions : List VDefVal}, environment.addConsts definitions = some extended →
      ∀ first ∈ definitions, ∀ second ∈ definitions, first.name = second.name → first = second
  | [], _, _, member, _, _, _ => by cases member
  | definition :: definitions, added, first, firstMember, second, secondMember, equal => by
    obtain ⟨middle, firstAdded, restAdded⟩ := Option.bind_eq_some_iff.mp added
    rcases List.mem_cons.mp firstMember with rfl | firstTail
    · rcases List.mem_cons.mp secondMember with rfl | secondTail
      · rfl
      · have fresh := addConstsFresh restAdded second secondTail
        have found := addConst_self firstAdded
        rw [equal, fresh] at found
        cases found
    · rcases List.mem_cons.mp secondMember with rfl | secondTail
      · have fresh := addConstsFresh restAdded first firstTail
        have found := addConst_self firstAdded
        rw [← equal, fresh] at found
        cases found
      · exact addConstsUnique restAdded first firstTail second secondTail equal

private theorem RewriteMetadata.addMutualDefinitions (metadata : RewriteMetadata environment)
    (environmentWF : environment.WF)
    (added : environment.addConsts definitions = some extended) :
    RewriteMetadata (extended.addDefEqs definitions) := by
  have extension := (addConsts_le added).trans (addDefEqs_extension extended definitions)
  have registeredCases {definition : VDefVal}
      (registered : (extended.addDefEqs definitions).defeqs definition.toDefEq) :
      definition ∈ definitions ∨ environment.defeqs definition.toDefEq := by
    rcases (addDefEqs_defeqs ..).mp registered with ⟨previous, member, equal⟩ | old
    · cases definitionEquationInjective equal
      exact .inl member
    · exact .inr (by rwa [addConsts_defeqs added] at old)
  have oldDifferent {first second : VDefVal} (member : first ∈ definitions)
      (registered : environment.defeqs second.toDefEq) : first.name ≠ second.name := by
    intro equal
    have found := metadata.lookup registered
    rw [← equal, addConstsFresh added first member] at found
    cases found
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equation registered
    rcases (addDefEqs_defeqs ..).mp registered with ⟨definition, _, equal⟩ | old
    · exact .inr ⟨definition, equal⟩
    · exact metadata.classify (by rwa [addConsts_defeqs added] at old)
  · intro definition registered
    rcases registeredCases registered with member | old
    · rw [addDefEqs_constants]
      exact addConsts_constants added definition member
    · exact extension.constants (metadata.lookup old)
  · intro first second firstRegistered secondRegistered equal
    rcases registeredCases firstRegistered with firstMember | firstOld
    · rcases registeredCases secondRegistered with secondMember | secondOld
      · exact addConstsUnique added first firstMember second secondMember equal
      · exact False.elim (oldDifferent firstMember secondOld equal)
    · rcases registeredCases secondRegistered with secondMember | secondOld
      · exact False.elim (oldDifferent secondMember firstOld equal.symm)
      · exact metadata.unique firstOld secondOld equal
  · intro definition registered initialized
    have oldInitialized : environment.defeqs quotDefEq := by
      rcases (addDefEqs_defeqs ..).mp initialized with ⟨previous, _, impossible⟩ | old
      · exact False.elim (definitionNotQuotient previous impossible.symm)
      · rwa [addConsts_defeqs added] at old
    rcases registeredCases registered with member | old
    · intro name nameMember equal
      have objects := environmentWF.quotientObjects oldInitialized
      have found : environment.contains name := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at nameMember
        rcases nameMember with rfl | rfl | rfl | rfl
        · exact ⟨_, objects.2.2.2.2.1⟩
        · exact ⟨_, objects.2.2.2.1⟩
        · exact ⟨_, objects.2.2.1⟩
        · exact ⟨_, objects.2.1⟩
      obtain ⟨_, found⟩ := found
      rw [← equal, addConstsFresh added definition member] at found
      cases found
    · exact metadata.quotientNames old oldInitialized

private theorem RewriteMetadata.addQuotient (metadata : RewriteMetadata environment)
    (added : environment.addQuot = some extended) : RewriteMetadata extended := by
  obtain ⟨extension, fresh, preserved⟩ := quotientExtension added
  have registeredCases {definition : VDefVal} (registered : extended.defeqs definition.toDefEq) :
      environment.defeqs definition.toDefEq := by
    rw [preserved] at registered
    rcases registered with newEquation | oldEquation
    · exact False.elim (definitionNotQuotient definition newEquation)
    · exact oldEquation
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro equation registered
    rw [preserved] at registered
    rcases registered with newEquation | oldEquation
    · exact .inl newEquation
    · exact metadata.classify oldEquation
  · intro definition registered
    exact extension.constants (metadata.lookup (registeredCases registered))
  · intro first second firstRegistered secondRegistered equal
    exact metadata.unique (registeredCases firstRegistered) (registeredCases secondRegistered) equal
  · intro definition registered _ name member equal
    have found := metadata.lookup (registeredCases registered)
    rw [equal, fresh _ member] at found
    cases found

theorem WF.rewriteMetadata (environmentWF : environment.WF) : RewriteMetadata environment := by
  obtain ⟨declarations, wellFormed⟩ := environmentWF
  induction wellFormed with
  | empty => exact ⟨nofun, nofun, nofun, nofun⟩
  | @decl previous extended declaration declarations checked previousWF inductionHypothesis =>
    cases checked with
    | «axiom» _ added | «opaque» _ added =>
      exact inductionHypothesis.extend (addConst_le added) (addConst.defeqs_eq added)
    | «def» _ added =>
      exact inductionHypothesis.addDefinition ⟨_, previousWF⟩ added
    | mutualDef _ added _ =>
      exact inductionHypothesis.addMutualDefinitions ⟨_, previousWF⟩ added
    | «example» _ => exact inductionHypothesis
    | quot _ added => exact inductionHypothesis.addQuotient added
    | induct _ added =>
      exact inductionHypothesis.extend (addInduct.le added) (addInduct.defeqs_eq added)

end Lean4Lean.VEnv
