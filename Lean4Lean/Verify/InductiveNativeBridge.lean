import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.InductiveNativeTrace

namespace Lean4Lean
open Lean hiding Environment Exception

namespace NativeInductive

structure HeaderEntry where
  info : InductiveVal
  model : VConstVal

structure ConstructorEntry where
  info : ConstructorVal
  model : VConstVal

structure RecursorEntry where
  info : RecursorVal
  model : VConstVal

inductive RegistrationEntry where
  | header (entry : HeaderEntry)
  | constructor (entry : ConstructorEntry)
  | recursor (entry : RecursorEntry)

def RegistrationEntry.toConstantInfo : RegistrationEntry → ConstantInfo
  | .header entry => .inductInfo entry.info
  | .constructor entry => .ctorInfo entry.info
  | .recursor entry => .recInfo entry.info

def RegistrationEntry.insert (constants : ConstMap) : RegistrationEntry → ConstMap
  | .header entry => constants.insert entry.info.name (.inductInfo entry.info)
  | .constructor entry => constants.insert entry.info.name (.ctorInfo entry.info)
  | .recursor entry => constants.insert entry.info.name (.recInfo entry.info)

def insertOrdered (constants : ConstMap) : List RegistrationEntry → ConstMap
  | [] => constants
  | entry :: entries => insertOrdered (entry.insert constants) entries

def FreshOrdered (constants : ConstMap) : List RegistrationEntry → Prop
  | [] => True
  | entry :: entries =>
    constants.find? entry.toConstantInfo.name = none ∧
      FreshOrdered (entry.insert constants) entries

def RegistrationEntry.Semantic (env headerEnv constructorEnv : VEnv) :
    RegistrationEntry → Prop
  | .header entry => TrConstVal .safe env (.inductInfo entry.info) entry.model
  | .constructor entry => TrConstVal .safe headerEnv (.ctorInfo entry.info) entry.model
  | .recursor entry => TrConstVal .safe constructorEnv (.recInfo entry.info) entry.model

def RegistrationEntry.Metadata (decl : VInductDecl) (constructors : List ConstructorEntry) :
    RegistrationEntry → Prop
  | .header entry => entry.info.numParams = decl.nparams
  | .constructor entry => entry.info.numParams = decl.nparams
  | .recursor entry =>
    entry.info.all = decl.types.map (·.name) ∧
      ∀ rule ∈ entry.info.rules, ∃ ctor ∈ constructors, rule.ctor = ctor.info.name

def RegistrationEntry.RuleSemantics (constructorEnv : VEnv) : RegistrationEntry → Prop
  | .header _ => True
  | .constructor _ => True
  | .recursor entry =>
    ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS constructorEnv entry.info.levelParams [] rule.rhs semantic

def RegistrationEntry.ModelShape : RegistrationEntry → Prop
  | .header entry => entry.model.name = entry.info.name ∧
      entry.model.uvars = entry.info.levelParams.length
  | .constructor entry => entry.model.name = entry.info.name ∧
      entry.model.uvars = entry.info.levelParams.length
  | .recursor entry => entry.model.name = entry.info.name ∧
      entry.model.uvars = entry.info.levelParams.length

theorem RegistrationEntry.Semantic.modelShape
    {env headerEnv constructorEnv : VEnv} {entry : RegistrationEntry}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    entry.ModelShape := by
  cases entry with
  | header entry => exact ⟨hsemantic.2.symm, hsemantic.1.2.1.symm⟩
  | constructor entry => exact ⟨hsemantic.2.symm, hsemantic.1.2.1.symm⟩
  | recursor entry => exact ⟨hsemantic.2.symm, hsemantic.1.2.1.symm⟩

theorem RegistrationEntry.Semantic.typeTranslation
    {env headerEnv constructorEnv : VEnv} {entry : RegistrationEntry}
    (hsemantic : entry.Semantic env headerEnv constructorEnv) :
    ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry => TrExprS headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry => TrExprS constructorEnv entry.info.levelParams [] entry.info.type semantic := by
  cases entry with
  | header entry => exact ⟨_, hsemantic.1.2.2⟩
  | constructor entry => exact ⟨_, hsemantic.1.2.2⟩
  | recursor entry => exact ⟨_, hsemantic.1.2.2⟩

def HeaderEntry.toConstantInfo (entry : HeaderEntry) : ConstantInfo :=
  .inductInfo entry.info

def ConstructorEntry.toConstantInfo (entry : ConstructorEntry) : ConstantInfo :=
  .ctorInfo entry.info

def RecursorEntry.toConstantInfo (entry : RecursorEntry) : ConstantInfo :=
  .recInfo entry.info

def insertHeaders (constants : ConstMap) : List HeaderEntry → ConstMap
  | [] => constants
  | entry :: entries =>
    insertHeaders (constants.insert entry.info.name (.inductInfo entry.info)) entries

def insertConstructors (constants : ConstMap) : List ConstructorEntry → ConstMap
  | [] => constants
  | entry :: entries =>
    insertConstructors (constants.insert entry.info.name (.ctorInfo entry.info)) entries

def insertRecursors (constants : ConstMap) : List RecursorEntry → ConstMap
  | [] => constants
  | entry :: entries =>
    insertRecursors (constants.insert entry.info.name (.recInfo entry.info)) entries

theorem insertHeaders_toConstantInfos (constants : ConstMap) (entries : List HeaderEntry) :
    insertHeaders constants entries =
      insertInfos constants (entries.reverse.map HeaderEntry.toConstantInfo) := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertHeaders, List.reverse_cons, List.map_append, List.map_singleton,
      HeaderEntry.toConstantInfo]
    rw [ih, ← insertInfos_append]
    rfl

theorem insertConstructors_toConstantInfos (constants : ConstMap) (entries : List ConstructorEntry) :
    insertConstructors constants entries =
      insertInfos constants (entries.reverse.map ConstructorEntry.toConstantInfo) := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertConstructors, List.reverse_cons, List.map_append, List.map_singleton,
      ConstructorEntry.toConstantInfo]
    rw [ih, ← insertInfos_append]
    rfl

theorem insertRecursors_toConstantInfos (constants : ConstMap) (entries : List RecursorEntry) :
    insertRecursors constants entries =
      insertInfos constants (entries.reverse.map RecursorEntry.toConstantInfo) := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertRecursors, List.reverse_cons, List.map_append, List.map_singleton,
      RecursorEntry.toConstantInfo]
    rw [ih, ← insertInfos_append]
    rfl

theorem insertOrdered_headers (constants : ConstMap) (entries : List HeaderEntry) :
    insertOrdered constants (entries.map (fun entry => .header entry)) =
      insertHeaders constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertOrdered, RegistrationEntry.insert, insertHeaders]
    rw [ih]

theorem insertOrdered_constructors (constants : ConstMap) (entries : List ConstructorEntry) :
    insertOrdered constants (entries.map (fun entry => .constructor entry)) =
      insertConstructors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertOrdered, RegistrationEntry.insert, insertConstructors]
    rw [ih]

theorem insertOrdered_recursors (constants : ConstMap) (entries : List RecursorEntry) :
    insertOrdered constants (entries.map (fun entry => .recursor entry)) =
      insertRecursors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertOrdered, RegistrationEntry.insert, insertRecursors]
    rw [ih]

def FreshHeaders (constants : ConstMap) : List HeaderEntry → Prop
  | [] => True
  | entry :: entries =>
    constants.find? entry.info.name = none ∧
      FreshHeaders (constants.insert entry.info.name (.inductInfo entry.info)) entries

def FreshConstructors (constants : ConstMap) : List ConstructorEntry → Prop
  | [] => True
  | entry :: entries =>
    constants.find? entry.info.name = none ∧
      FreshConstructors (constants.insert entry.info.name (.ctorInfo entry.info)) entries

def FreshRecursors (constants : ConstMap) : List RecursorEntry → Prop
  | [] => True
  | entry :: entries =>
    constants.find? entry.info.name = none ∧
      FreshRecursors (constants.insert entry.info.name (.recInfo entry.info)) entries

theorem FreshHeaders.ordered (constants : ConstMap) (entries : List HeaderEntry) :
    FreshOrdered constants (entries.map (fun entry => .header entry)) ↔
      FreshHeaders constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, FreshOrdered, RegistrationEntry.toConstantInfo,
      RegistrationEntry.insert, ConstantInfo.name, ConstantInfo.toConstantVal, FreshHeaders]
    rw [ih]

theorem FreshConstructors.ordered (constants : ConstMap) (entries : List ConstructorEntry) :
    FreshOrdered constants (entries.map (fun entry => .constructor entry)) ↔
      FreshConstructors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, FreshOrdered, RegistrationEntry.toConstantInfo,
      RegistrationEntry.insert, ConstantInfo.name, ConstantInfo.toConstantVal, FreshConstructors]
    rw [ih]

theorem FreshRecursors.ordered (constants : ConstMap) (entries : List RecursorEntry) :
    FreshOrdered constants (entries.map (fun entry => .recursor entry)) ↔
      FreshRecursors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, FreshOrdered, RegistrationEntry.toConstantInfo,
      RegistrationEntry.insert, ConstantInfo.name, ConstantInfo.toConstantVal, FreshRecursors]
    rw [ih]

theorem insertOrdered_append (constants : ConstMap) (first second : List RegistrationEntry) :
    insertOrdered constants (first ++ second) =
      insertOrdered (insertOrdered constants first) second := by
  induction first generalizing constants with
  | nil => rfl
  | cons entry first ih =>
    simp only [List.cons_append, insertOrdered]
    rw [ih]

theorem insertOrdered_toConstantInfos (constants : ConstMap) (entries : List RegistrationEntry) :
    insertOrdered constants entries =
      insertInfos constants (entries.map RegistrationEntry.toConstantInfo).reverse := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertOrdered, List.map_cons, List.reverse_cons]
    have hentry : entry.insert constants =
        insertInfos constants [entry.toConstantInfo] := by
      cases entry <;> rfl
    rw [hentry, ih, ← insertInfos_append]

theorem FreshOrdered.append {constants : ConstMap} {first second : List RegistrationEntry}
    (hfirst : FreshOrdered constants first)
    (hsecond : FreshOrdered (insertOrdered constants first) second) :
    FreshOrdered constants (first ++ second) := by
  induction first generalizing constants with
  | nil => simpa using hsecond
  | cons entry first ih =>
    simp only [FreshOrdered, List.cons_append] at hfirst ⊢
    exact ⟨hfirst.1, ih hfirst.2 hsecond⟩

structure RegistrationEvidence (constants : ConstMap) (env : VEnv) (decl : VInductDecl)
    (resultConstants : ConstMap) (result : VEnv) where
  headers : List HeaderEntry
  constructors : List ConstructorEntry
  recursors : List RecursorEntry
  headerConstants : ConstMap
  constructorConstants : ConstMap
  headerEnv : VEnv
  constructorEnv : VEnv
  declWF : decl.WF env
  headerModels : headers.map (·.model) = decl.types.map (·.toVConstVal)
  constructorModels : constructors.map (·.model) = decl.constructorHeaders
  headerAdd : env.addInductHeaders decl.types = some headerEnv
  constructorAdd : headerEnv.addConstructorHeaders decl.constructorHeaders = some constructorEnv
  recursorAdd : constructorEnv.addConstructorHeaders (recursors.map (·.model)) = some result
  headerFresh : FreshHeaders constants headers
  constructorFresh : FreshConstructors headerConstants constructors
  recursorFresh : FreshRecursors constructorConstants recursors
  headerMap : headerConstants = insertHeaders constants headers
  constructorMap : constructorConstants = insertConstructors headerConstants constructors
  resultMap : resultConstants = insertRecursors constructorConstants recursors
  headerTranslation : ∀ entry ∈ headers,
    TrConstVal .safe env (.inductInfo entry.info) entry.model
  headerParameters : ∀ entry ∈ headers, entry.info.numParams = decl.nparams
  constructorTranslation : ∀ entry ∈ constructors,
    TrConstVal .safe headerEnv (.ctorInfo entry.info) entry.model
  constructorParameters : ∀ entry ∈ constructors, entry.info.numParams = decl.nparams
  recursorTranslation : ∀ entry ∈ recursors,
    TrConstVal .safe constructorEnv (.recInfo entry.info) entry.model
  recursorParents : ∀ entry ∈ recursors,
    entry.info.all = decl.types.map (·.name)
  recursorRules : ∀ entry ∈ recursors, ∀ rule ∈ entry.info.rules,
    ∃ ctor ∈ constructors, rule.ctor = ctor.info.name
  recursorRuleTranslation : ∀ entry ∈ recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
    TrExprS constructorEnv entry.info.levelParams [] rule.rhs semantic

def RegistrationEvidence.orderedEntries
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    List RegistrationEntry :=
  evidence.headers.map (fun entry => .header entry) ++
    evidence.constructors.map (fun entry => .constructor entry) ++
    evidence.recursors.map (fun entry => .recursor entry)

theorem RegistrationEvidence.orderedFresh
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    FreshOrdered constants evidence.orderedEntries := by
  have hheaders : FreshOrdered constants
      (evidence.headers.map (fun entry => .header entry)) :=
    (FreshHeaders.ordered constants evidence.headers).2 evidence.headerFresh
  have hconstructors : FreshOrdered
      (insertOrdered constants (evidence.headers.map (fun entry => .header entry)))
      (evidence.constructors.map (fun entry => .constructor entry)) := by
    have h := (FreshConstructors.ordered evidence.headerConstants evidence.constructors).2
      evidence.constructorFresh
    rw [evidence.headerMap, ← insertOrdered_headers] at h
    exact h
  have hheaderConstructors : FreshOrdered constants
      (evidence.headers.map (fun entry => .header entry) ++
        evidence.constructors.map (fun entry => .constructor entry)) :=
    FreshOrdered.append hheaders hconstructors
  have hrecursors : FreshOrdered
      (insertOrdered constants
        (evidence.headers.map (fun entry => .header entry) ++
          evidence.constructors.map (fun entry => .constructor entry)))
      (evidence.recursors.map (fun entry => .recursor entry)) := by
    have h := (FreshRecursors.ordered evidence.constructorConstants evidence.recursors).2
      evidence.recursorFresh
    rw [evidence.constructorMap, evidence.headerMap, ← insertOrdered_headers,
      ← insertOrdered_constructors] at h
    rw [insertOrdered_append]
    exact h
  exact FreshOrdered.append hheaderConstructors hrecursors

theorem RegistrationEvidence.orderedSemantic
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv := by
  intro entry hmem
  simp only [RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, hmem, rfl⟩
      exact evidence.headerTranslation header hmem
    · rcases List.mem_map.mp hconstructors with ⟨constructor, hmem, rfl⟩
      exact evidence.constructorTranslation constructor hmem
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hmem, rfl⟩
    exact evidence.recursorTranslation recursor hmem

theorem RegistrationEvidence.orderedModelShape
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, entry.ModelShape := by
  intro entry hmem
  exact (evidence.orderedSemantic entry hmem).modelShape

theorem RegistrationEvidence.orderedTypeTranslation
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, ∃ semantic, match entry with
      | .header entry => TrExprS env entry.info.levelParams [] entry.info.type semantic
      | .constructor entry =>
        TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
      | .recursor entry =>
        TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic := by
  intro entry hmem
  have hsemantic := evidence.orderedSemantic entry hmem
  cases entry with
  | header entry => exact ⟨_, hsemantic.1.2.2⟩
  | constructor entry => exact ⟨_, hsemantic.1.2.2⟩
  | recursor entry => exact ⟨_, hsemantic.1.2.2⟩

theorem RegistrationEvidence.orderedMetadata
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Metadata decl evidence.constructors := by
  intro entry hmem
  simp only [RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, hmem, rfl⟩
      exact evidence.headerParameters header hmem
    · rcases List.mem_map.mp hconstructors with ⟨constructor, hmem, rfl⟩
      exact evidence.constructorParameters constructor hmem
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hmem, rfl⟩
    exact ⟨evidence.recursorParents recursor hmem, evidence.recursorRules recursor hmem⟩

theorem RegistrationEvidence.orderedRuleSemantics
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics evidence.constructorEnv := by
  intro entry hmem
  simp only [RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, hmem, rfl⟩
      trivial
    · rcases List.mem_map.mp hconstructors with ⟨constructor, hmem, rfl⟩
      trivial
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hmem, rfl⟩
    intro rule hrule
    exact evidence.recursorRuleTranslation recursor hmem rule hrule

theorem RegistrationEvidence.to_addInduct
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    env.addInductWithRecursors decl
      (evidence.recursors.map (·.model)) = some result := by
  unfold VEnv.addInductWithRecursors VEnv.addInduct
  rw [evidence.headerAdd]
  simp [evidence.constructorAdd, evidence.recursorAdd]

theorem RegistrationEvidence.native_map
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertRecursors (insertConstructors (insertHeaders constants evidence.headers)
      evidence.constructors) evidence.recursors := by
  calc
    resultConstants = insertRecursors evidence.constructorConstants evidence.recursors :=
      evidence.resultMap
    _ = insertRecursors (insertConstructors evidence.headerConstants evidence.constructors)
        evidence.recursors := by rw [evidence.constructorMap]
    _ = insertRecursors (insertConstructors (insertHeaders constants evidence.headers)
        evidence.constructors) evidence.recursors := by rw [evidence.headerMap]

theorem RegistrationEvidence.orderedMap
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrdered constants evidence.orderedEntries := by
  unfold RegistrationEvidence.orderedEntries
  rw [insertOrdered_append, insertOrdered_append, insertOrdered_recursors,
    insertOrdered_constructors, insertOrdered_headers]
  exact evidence.native_map

theorem RegistrationEvidence.native_map_records
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertInfos constants
      ((evidence.headers.map HeaderEntry.toConstantInfo ++
        evidence.constructors.map ConstructorEntry.toConstantInfo ++
        evidence.recursors.map RecursorEntry.toConstantInfo).reverse) := by
  calc
    resultConstants = insertRecursors (insertConstructors (insertHeaders constants evidence.headers)
      evidence.constructors) evidence.recursors := evidence.native_map
    _ = insertInfos constants
        ((evidence.headers.map HeaderEntry.toConstantInfo ++
          evidence.constructors.map ConstructorEntry.toConstantInfo ++
          evidence.recursors.map RecursorEntry.toConstantInfo).reverse) := by
      rw [insertRecursors_toConstantInfos, insertConstructors_toConstantInfos,
        insertHeaders_toConstantInfos]
      simp only [List.reverse_append, List.map_reverse]
      rw [insertInfos_append, insertInfos_append]
      congr 1
      exact List.append_assoc _ _ _

theorem RegistrationEvidence.recursor_translation_receipt
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors,
      TrConstVal .safe evidence.constructorEnv (.recInfo entry.info) entry.model :=
  evidence.recursorTranslation

end NativeInductive

end Lean4Lean
