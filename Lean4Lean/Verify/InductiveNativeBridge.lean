import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Environment.Lemmas
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

def RegistrationEntry.model : RegistrationEntry → VConstVal
  | .header entry => entry.model
  | .constructor entry => entry.model
  | .recursor entry => entry.model

def RegistrationEntry.insert (constants : ConstMap) : RegistrationEntry → ConstMap
  | .header entry => constants.insert entry.info.name (.inductInfo entry.info)
  | .constructor entry => constants.insert entry.info.name (.ctorInfo entry.info)
  | .recursor entry => constants.insert entry.info.name (.recInfo entry.info)

def RegistrationEntry.insertModel (constants : ConstMap) (entry : RegistrationEntry) : ConstMap :=
  constants.insert entry.model.name entry.toConstantInfo

def insertOrdered (constants : ConstMap) : List RegistrationEntry → ConstMap
  | [] => constants
  | entry :: entries => insertOrdered (entry.insert constants) entries

def insertOrderedModel (constants : ConstMap) : List RegistrationEntry → ConstMap
  | [] => constants
  | entry :: entries => insertOrderedModel (entry.insertModel constants) entries

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

/-- Rule bodies may call any registered recursor, including a later mutual parent.
Their translation is checked after all recursor signatures have been inserted. -/
def RegistrationEntry.RuleSemantics (ruleEnv : VEnv) : RegistrationEntry → Prop
  | .header _ => True
  | .constructor _ => True
  | .recursor entry =>
    ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS ruleEnv entry.info.levelParams [] rule.rhs semantic

theorem RegistrationEntry.RuleSemantics.mono
    {before after : VEnv} {entry : RegistrationEntry}
    (rules : entry.RuleSemantics before) (extension : before ≤ after) :
    entry.RuleSemantics after := by
  cases entry with
  | header _ | constructor _ => trivial
  | recursor entry =>
    intro rule member
    obtain ⟨semantic, translated⟩ := rules rule member
    exact ⟨semantic, translated.mono extension⟩

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

theorem RegistrationEntry.ModelShape.toConstantInfo
    {entry : RegistrationEntry} (hshape : entry.ModelShape) :
    entry.model.name = entry.toConstantInfo.name ∧
      entry.model.uvars = entry.toConstantInfo.levelParams.length := by
  cases entry with
  | header entry => exact hshape
  | constructor entry => exact hshape
  | recursor entry => exact hshape

theorem RegistrationEntry.insert_modelShape
    {entry : RegistrationEntry} {constants : ConstMap} (hshape : entry.ModelShape) :
    entry.insert constants = constants.insert entry.model.name entry.toConstantInfo := by
  cases entry <;>
    simp only [RegistrationEntry.insert, RegistrationEntry.model, RegistrationEntry.toConstantInfo]
  · rw [hshape.1]
  · rw [hshape.1]
  · rw [hshape.1]

theorem insertOrdered_modelShape (constants : ConstMap) (entries : List RegistrationEntry)
    (hshape : ∀ entry ∈ entries, entry.ModelShape) :
    insertOrdered constants entries = insertOrderedModel constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertOrdered, insertOrderedModel]
    have htail : ∀ entry ∈ entries, entry.ModelShape :=
      fun entry hmem => hshape entry (by simp [hmem])
    rw [entry.insert_modelShape (hshape entry (by simp))]
    simpa [RegistrationEntry.insertModel] using ih (entry.insertModel constants) htail

theorem insertOrdered_toInsertConsts (constants : ConstMap) (entries : List RegistrationEntry)
    (hshape : ∀ entry ∈ entries, entry.ModelShape) :
    insertOrdered constants entries =
      insertConsts constants (entries.map RegistrationEntry.toConstantInfo) := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [insertOrdered, insertConsts, List.foldl_cons, List.map_cons]
    have hentryShape := hshape entry (by simp)
    rw [entry.insert_modelShape hentryShape]
    simpa [insertConsts, hentryShape.toConstantInfo.1] using
      ih (constants.insert entry.model.name entry.toConstantInfo)
      (fun current hcurrent => hshape current (by simp [hcurrent]))

theorem FreshOrdered.baseFresh {constants : ConstMap} {entries : List RegistrationEntry}
    (hconstants : constants.WF) (hshape : ∀ entry ∈ entries, entry.ModelShape)
    (hfresh : FreshOrdered constants entries) :
    ∀ entry ∈ entries, constants.find? entry.toConstantInfo.name = none := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    intro current hcurrent
    simp only [FreshOrdered] at hfresh
    have hentryShape := hshape entry (by simp)
    have hentryInsert : entry.insert constants =
        constants.insert entry.model.name entry.toConstantInfo :=
      entry.insert_modelShape hentryShape
    rw [hentryInsert] at hfresh
    have hbase' : (constants.insert entry.toConstantInfo.name entry.toConstantInfo).WF :=
      hconstants.insert _ _ hfresh.1
    have hbase : (constants.insert entry.model.name entry.toConstantInfo).WF := by
      simpa [hentryShape.toConstantInfo.1] using hbase'
    rcases List.mem_cons.mp hcurrent with hcurrent | hcurrent
    · simpa [hcurrent] using hfresh.1
    · have htail := ih hbase
        (fun current hcurrent => hshape current (by simp [hcurrent])) hfresh.2
        current hcurrent
      rw [hconstants.find?_insert] at htail
      split at htail
      · contradiction
      · exact htail

theorem FreshOrdered.nodup {constants : ConstMap} {entries : List RegistrationEntry}
    (hconstants : constants.WF) (hshape : ∀ entry ∈ entries, entry.ModelShape)
    (hfresh : FreshOrdered constants entries) :
    (entries.map (fun entry => entry.toConstantInfo.name)).Nodup := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    simp only [FreshOrdered] at hfresh
    have hentryShape := hshape entry (by simp)
    have hentryInsert : entry.insert constants =
        constants.insert entry.model.name entry.toConstantInfo :=
      entry.insert_modelShape hentryShape
    rw [hentryInsert] at hfresh
    have hbase' : (constants.insert entry.toConstantInfo.name entry.toConstantInfo).WF :=
      hconstants.insert _ _ hfresh.1
    have hbase : (constants.insert entry.model.name entry.toConstantInfo).WF := by
      simpa [hentryShape.toConstantInfo.1] using hbase'
    apply List.nodup_cons.mpr
    refine ⟨?_, ih hbase
      (fun current hcurrent => hshape current (by simp [hcurrent])) hfresh.2⟩
    intro hname
    obtain ⟨other, hother, hname⟩ := List.mem_map.mp hname
    have htail := FreshOrdered.baseFresh hbase
      (fun current hcurrent => hshape current (by simp [hcurrent])) hfresh.2
      other hother
    rw [hconstants.find?_insert] at htail
    split at htail <;> simp_all [hentryShape.toConstantInfo.1]

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
  | nil => simpa [insertOrdered] using hsecond
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
  /-- Recursor types translate before insertion; recursive rule bodies translate afterwards. -/
  recursorRuleTranslation : ∀ entry ∈ recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
    TrExprS result entry.info.levelParams [] rule.rhs semantic

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

theorem RegistrationEvidence.orderedModelShapeToConstantInfo
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.model.name = entry.toConstantInfo.name ∧
        entry.model.uvars = entry.toConstantInfo.levelParams.length := by
  intro entry hmem
  exact (evidence.orderedSemantic entry hmem).modelShape.toConstantInfo

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

/- Pair the complete stored-rule semantic witness with an arbitrary retained
   per-rule result.  The result is exposed only for recursor entries; headers
   and constructors still receive the ordinary trivial registration receipt. -/
theorem RegistrationEvidence.orderedRuleResultsOf
    {Result : RecursorEntry → RecursorRule → Prop}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics result ∧ match entry with
        | .header _ | .constructor _ => True
        | .recursor entry => ∀ rule ∈ entry.info.rules, Result entry rule := by
  intro entry hmem
  simp only [RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, hmem, rfl⟩
      exact ⟨trivial, trivial⟩
    · rcases List.mem_map.mp hconstructors with ⟨constructor, hmem, rfl⟩
      exact ⟨trivial, trivial⟩
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hmem, rfl⟩
    refine ⟨?_, ?_⟩
    · intro rule hrule
      exact evidence.recursorRuleTranslation recursor hmem rule hrule
    · intro rule hrule
      exact ruleResults recursor hmem rule hrule

/- A recursor consumer often needs the translated RHS and its retained result
   at the same indexed rule.  Keep that pairing at the registration boundary
   so callers do not have to reopen the ordered-entry proof. -/
theorem RegistrationEvidence.recursorRuleResult
    {Result : RecursorEntry → RecursorRule → Prop}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (ruleResults : ∀ (entry : RecursorEntry), entry ∈ evidence.recursors →
      ∀ rule, rule ∈ entry.info.rules → Result entry rule) :
    ∀ entry ∈ evidence.recursors, ∀ rule ∈ entry.info.rules, ∃ semantic,
      TrExprS result entry.info.levelParams [] rule.rhs semantic ∧ Result entry rule := by
  intro entry hentry rule hrule
  obtain ⟨semantic, hsemantic⟩ := evidence.recursorRuleTranslation entry hentry rule hrule
  exact ⟨semantic, hsemantic, ruleResults entry hentry rule hrule⟩

theorem RegistrationEvidence.orderedRuleSemantics
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.RuleSemantics result := by
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

private theorem insertConsts_headerInfos (constants : ConstMap) (entries : List HeaderEntry) :
    insertConsts constants (entries.map HeaderEntry.toConstantInfo) =
      insertHeaders constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertConsts, List.foldl_cons, insertHeaders]
    exact ih (constants.insert entry.info.name (.inductInfo entry.info))

private theorem insertConsts_constructorInfos (constants : ConstMap)
    (entries : List ConstructorEntry) :
    insertConsts constants (entries.map ConstructorEntry.toConstantInfo) =
      insertConstructors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertConsts, List.foldl_cons, insertConstructors]
    exact ih (constants.insert entry.info.name (.ctorInfo entry.info))

private theorem FreshHeaders.wf {constants : ConstMap} {entries : List HeaderEntry}
    (hconstants : constants.WF) :
    FreshHeaders constants entries → (insertHeaders constants entries).WF := by
  intro hfresh
  induction entries generalizing constants with
  | nil => exact hconstants
  | cons entry entries ih =>
    simp only [FreshHeaders] at hfresh
    rw [insertHeaders]
    exact ih (hconstants.insert _ _ hfresh.1) hfresh.2

private theorem FreshConstructors.wf {constants : ConstMap} {entries : List ConstructorEntry}
    (hconstants : constants.WF) :
    FreshConstructors constants entries → (insertConstructors constants entries).WF := by
  intro hfresh
  induction entries generalizing constants with
  | nil => exact hconstants
  | cons entry entries ih =>
    simp only [FreshConstructors] at hfresh
    rw [insertConstructors]
    exact ih (hconstants.insert _ _ hfresh.1) hfresh.2

private theorem FreshHeaders.baseFresh {constants : ConstMap} {entries : List HeaderEntry}
    (hconstants : constants.WF) (hfresh : FreshHeaders constants entries) :
    ∀ entry ∈ entries, constants.find? entry.info.name = none := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    intro current hcurrent
    simp only [FreshHeaders] at hfresh
    rcases List.mem_cons.mp hcurrent with hcurrent | hcurrent
    · simpa [hcurrent] using hfresh.1
    · have htail := ih (hconstants.insert _ _ hfresh.1) hfresh.2 current hcurrent
      rw [hconstants.find?_insert] at htail
      split at htail
      · contradiction
      · exact htail

private theorem FreshConstructors.baseFresh {constants : ConstMap}
    {entries : List ConstructorEntry} (hconstants : constants.WF)
    (hfresh : FreshConstructors constants entries) :
    ∀ entry ∈ entries, constants.find? entry.info.name = none := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    intro current hcurrent
    simp only [FreshConstructors] at hfresh
    rcases List.mem_cons.mp hcurrent with hcurrent | hcurrent
    · simpa [hcurrent] using hfresh.1
    · have htail := ih (hconstants.insert _ _ hfresh.1) hfresh.2 current hcurrent
      rw [hconstants.find?_insert] at htail
      split at htail
      · contradiction
      · exact htail

private theorem FreshHeaders.nodup {constants : ConstMap} {entries : List HeaderEntry}
    (hconstants : constants.WF) (hfresh : FreshHeaders constants entries) :
    (entries.map (·.info.name)).Nodup := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    simp only [FreshHeaders] at hfresh
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (hconstants.insert _ _ hfresh.1) hfresh.2⟩
    intro hname
    obtain ⟨other, hother, hname⟩ := List.mem_map.mp hname
    have htail := FreshHeaders.baseFresh (hconstants.insert _ _ hfresh.1) hfresh.2
      other hother
    rw [hconstants.find?_insert] at htail
    split at htail <;> simp_all

private theorem FreshConstructors.nodup {constants : ConstMap}
    {entries : List ConstructorEntry} (hconstants : constants.WF)
    (hfresh : FreshConstructors constants entries) :
    (entries.map (·.info.name)).Nodup := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    simp only [FreshConstructors] at hfresh
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (hconstants.insert _ _ hfresh.1) hfresh.2⟩
    intro hname
    obtain ⟨other, hother, hname⟩ := List.mem_map.mp hname
    have htail := FreshConstructors.baseFresh (hconstants.insert _ _ hfresh.1) hfresh.2
      other hother
    rw [hconstants.find?_insert] at htail
    split at htail <;> simp_all

private theorem FreshRecursors.baseFresh {constants : ConstMap}
    {entries : List RecursorEntry} (hconstants : constants.WF)
    (hfresh : FreshRecursors constants entries) :
    ∀ entry ∈ entries, constants.find? entry.info.name = none := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    intro current hcurrent
    simp only [FreshRecursors] at hfresh
    rcases List.mem_cons.mp hcurrent with hcurrent | hcurrent
    · simpa [hcurrent] using hfresh.1
    · have htail := ih (hconstants.insert _ _ hfresh.1) hfresh.2 current hcurrent
      rw [hconstants.find?_insert] at htail
      split at htail
      · contradiction
      · exact htail

private theorem FreshRecursors.nodup {constants : ConstMap}
    {entries : List RecursorEntry} (hconstants : constants.WF)
    (hfresh : FreshRecursors constants entries) :
    (entries.map (·.info.name)).Nodup := by
  induction entries generalizing constants with
  | nil => simp
  | cons entry entries ih =>
    simp only [FreshRecursors] at hfresh
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (hconstants.insert _ _ hfresh.1) hfresh.2⟩
    intro hname
    obtain ⟨other, hother, hname⟩ := List.mem_map.mp hname
    have htail := FreshRecursors.baseFresh (hconstants.insert _ _ hfresh.1) hfresh.2
      other hother
    rw [hconstants.find?_insert] at htail
    split at htail <;> simp_all

private theorem RegistrationEvidence.headerPairs
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    List.Forall₂
      (fun info header => info.name = header.name ∧
        TrConstant .safe env (.inductInfo info) header.toVConstant)
      (evidence.headers.map (·.info)) decl.types := by
  have go : ∀ (entries : List HeaderEntry) (types : List VInductiveType),
      entries.map (·.model) = types.map (·.toVConstVal) →
      (∀ entry ∈ entries,
        TrConstVal .safe env (.inductInfo entry.info) entry.model) →
      List.Forall₂
        (fun entry type => entry.info.name = type.name ∧
          TrConstant .safe env (.inductInfo entry.info) type.toVConstant)
        entries types := by
    intro entries
    induction entries with
    | nil =>
      intro types hmodels _
      cases types <;> simp_all
    | cons entry entries ih =>
      intro types hmodels htranslation
      cases types with
      | nil => simp at hmodels
      | cons type types =>
        simp only [List.map_cons, List.cons.injEq] at hmodels
        refine .cons ?_ (ih types hmodels.2 (fun entry hmem =>
          htranslation entry (.tail _ hmem)))
        have hsemantic := htranslation entry (.head _)
        have hname : entry.info.name = type.name := by
          calc
            entry.info.name = entry.model.name := hsemantic.2
            _ = type.toVConstVal.name := congrArg VConstVal.name hmodels.1
            _ = type.name := rfl
        refine ⟨hname, ?_⟩
        simpa [hmodels.1] using hsemantic.1
  rw [List.forall₂_map_left_iff]
  exact go evidence.headers decl.types evidence.headerModels evidence.headerTranslation

private theorem RegistrationEvidence.constructorPairs
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    List.Forall₂
      (fun info ctor => info.name = ctor.name ∧
        TrConstant .safe evidence.headerEnv (.ctorInfo info) ctor.toVConstant)
      (evidence.constructors.map (·.info)) decl.constructorHeaders := by
  have go : ∀ (entries : List ConstructorEntry) (ctors : List VConstVal),
      entries.map (·.model) = ctors →
      (∀ entry ∈ entries,
        TrConstVal .safe evidence.headerEnv (.ctorInfo entry.info) entry.model) →
      List.Forall₂
        (fun entry ctor => entry.info.name = ctor.name ∧
          TrConstant .safe evidence.headerEnv (.ctorInfo entry.info) ctor.toVConstant)
        entries ctors := by
    intro entries
    induction entries with
    | nil =>
      intro ctors hmodels _
      cases ctors <;> simp_all
    | cons entry entries ih =>
      intro ctors hmodels htranslation
      cases ctors with
      | nil => simp at hmodels
      | cons ctor ctors =>
        simp only [List.map_cons, List.cons.injEq] at hmodels
        refine .cons ?_ (ih ctors hmodels.2 (fun entry hmem =>
          htranslation entry (.tail _ hmem)))
        have hsemantic := htranslation entry (.head _)
        have hname : entry.info.name = ctor.name := by
          calc
            entry.info.name = entry.model.name := hsemantic.2
            _ = ctor.name := congrArg VConstVal.name hmodels.1
        refine ⟨hname, ?_⟩
        simpa [hmodels.1] using hsemantic.1
  rw [List.forall₂_map_left_iff]
  exact go evidence.constructors decl.constructorHeaders evidence.constructorModels
    evidence.constructorTranslation

theorem RegistrationEvidence.to_addInductEvidence
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF) :
    AddInductEvidence .safe constants env decl evidence.constructorConstants
      evidence.constructorEnv := by
  have hheaderMap : evidence.headerConstants =
      insertConsts constants (evidence.headers.map (.inductInfo ·.info)) := by
    change evidence.headerConstants =
      insertConsts constants (evidence.headers.map HeaderEntry.toConstantInfo)
    exact evidence.headerMap.trans (insertConsts_headerInfos constants evidence.headers).symm
  have hconstructorMap : evidence.constructorConstants =
      insertConsts evidence.headerConstants (evidence.constructors.map (.ctorInfo ·.info)) := by
    change evidence.constructorConstants =
      insertConsts evidence.headerConstants (evidence.constructors.map ConstructorEntry.toConstantInfo)
    exact evidence.constructorMap.trans
      (insertConsts_constructorInfos evidence.headerConstants evidence.constructors).symm
  have hheaderFresh : ∀ info ∈ evidence.headers.map (·.info),
      constants.find? info.name = none := by
    intro info hmem
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
    exact FreshHeaders.baseFresh hconstants evidence.headerFresh entry hentry
  have hheaderNodup : (evidence.headers.map (·.info)).map (·.name) |>.Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      evidence.headerFresh.nodup hconstants
  have hheaderWF : evidence.headerConstants.WF := by
    rw [evidence.headerMap]
    exact evidence.headerFresh.wf hconstants
  have hconstructorFresh : ∀ info ∈ evidence.constructors.map (·.info),
      (insertConsts constants (evidence.headers.map (.inductInfo ·.info))).find? info.name = none := by
    intro info hmem
    rw [← hheaderMap]
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
    exact FreshConstructors.baseFresh hheaderWF evidence.constructorFresh entry hentry
  have hconstructorNodup : (evidence.constructors.map (·.info)).map (·.name) |>.Nodup := by
    simpa only [List.map_map, Function.comp_def] using
      evidence.constructorFresh.nodup hheaderWF
  have hmap : evidence.constructorConstants =
      insertConsts constants
        (evidence.headers.map (.inductInfo ·.info) ++ evidence.constructors.map (.ctorInfo ·.info)) := by
    calc
      evidence.constructorConstants =
          insertConsts evidence.headerConstants (evidence.constructors.map (.ctorInfo ·.info)) :=
        hconstructorMap
      _ = insertConsts (insertConsts constants (evidence.headers.map (.inductInfo ·.info)))
          (evidence.constructors.map (.ctorInfo ·.info)) := by rw [hheaderMap]
      _ = insertConsts constants
          (evidence.headers.map (.inductInfo ·.info) ++ evidence.constructors.map (.ctorInfo ·.info)) := by
        rw [insertConsts_append]
  let headers : List InductiveVal := evidence.headers.map (·.info)
  let constructors : List ConstructorVal := evidence.constructors.map (·.info)
  refine AddInductEvidence.intro headers constructors evidence.headerEnv evidence.headerPairs
    evidence.constructorPairs evidence.headerAdd evidence.constructorAdd ?_ ?_
    (by simpa [headers] using hheaderFresh)
    (by
      simpa [headers, constructors, List.map_map, Function.comp_def] using hconstructorFresh)
    (by
      simpa [headers, constructors, List.map_map, Function.comp_def] using hmap)
  · simpa [headers, List.map_map, Function.comp_def] using hheaderNodup
  · simpa [constructors, List.map_map, Function.comp_def] using hconstructorNodup

theorem RegistrationEvidence.to_addInductEvidence_at
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (safety : DefinitionSafety) (hconstants : constants.WF) :
    AddInductEvidence safety constants env decl evidence.constructorConstants
      evidence.constructorEnv :=
  (evidence.to_addInductEvidence hconstants).sf_mono DefinitionSafety.le_safe

private theorem insertConsts_recursorInfos (constants : ConstMap) (entries : List RecursorEntry) :
    insertConsts constants (entries.map (.recInfo ·.info)) =
      insertRecursors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertConsts, List.foldl_cons, insertRecursors]
    exact ih (constants.insert entry.info.name (.recInfo entry.info))

private theorem insertConsts_recursorInfoMap (constants : ConstMap)
    (entries : List RecursorEntry) :
    insertConsts constants ((entries.map (·.info)).map (fun info => .recInfo info)) =
      insertRecursors constants entries := by
  induction entries generalizing constants with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.map_cons, insertConsts, List.foldl_cons, insertRecursors]
    exact ih (constants.insert entry.info.name (.recInfo entry.info))

theorem RegistrationEvidence.to_addInductWithRecursorsEvidence
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    AddInductWithRecursorsEvidence .safe constants env decl
      evidence.constructorConstants evidence.constructorEnv
      (evidence.recursors.map (·.info)) (evidence.recursors.map (·.model))
      resultConstants result := by
  have hinduct := evidence.to_addInductEvidence hconstants
  have hheaderWF : evidence.headerConstants.WF := by
    rw [evidence.headerMap]
    exact evidence.headerFresh.wf hconstants
  have hconstructorWF : evidence.constructorConstants.WF := by
    rw [evidence.constructorMap]
    exact evidence.constructorFresh.wf hheaderWF
  have htranslations : List.Forall₂
      (fun info model => info.name = model.name ∧
        TrConstant .safe evidence.constructorEnv (.recInfo info) model.toVConstant ∧
        model.toVConstant.WF evidence.constructorEnv)
      (evidence.recursors.map (·.info)) (evidence.recursors.map (·.model)) := by
    have go : ∀ entries : List RecursorEntry,
        (∀ entry ∈ entries,
          entry.info.name = entry.model.name ∧
            TrConstant .safe evidence.constructorEnv (.recInfo entry.info)
              entry.model.toVConstant ∧
            entry.model.toVConstant.WF evidence.constructorEnv) →
        List.Forall₂
          (fun info model => info.name = model.name ∧
            TrConstant .safe evidence.constructorEnv (.recInfo info) model.toVConstant ∧
            model.toVConstant.WF evidence.constructorEnv)
          (entries.map (·.info)) (entries.map (·.model)) := by
      intro entries
      induction entries with
      | nil => intro _; exact .nil
      | cons entry entries ih =>
        intro hentries
        refine .cons (hentries entry (by simp)) (ih (fun current hcurrent =>
          hentries current (by simp [hcurrent])))
    apply go evidence.recursors
    intro entry hentry
    have htranslation := evidence.recursorTranslation entry hentry
    exact ⟨htranslation.2, htranslation.1, hrecursors entry hentry⟩
  have hrecursorNodup :
      (evidence.recursors.map (·.model)).map (·.name) |>.Nodup := by
    have hpair : List.Forall₂ Eq
        (evidence.recursors.map (·.info.name))
        (evidence.recursors.map (·.model.name)) := by
      have namePairs : ∀ (entries : List RecursorEntry),
          List.Forall₂
            (fun info model => info.name = model.name ∧
              TrConstant .safe evidence.constructorEnv (.recInfo info) model.toVConstant ∧
              model.toVConstant.WF evidence.constructorEnv)
            (entries.map (·.info)) (entries.map (·.model)) →
          List.Forall₂ Eq (entries.map (·.info.name)) (entries.map (·.model.name)) := by
        intro entries
        induction entries with
        | nil => intro _; exact .nil
        | cons entry entries ih =>
          intro h
          cases h with
          | cons head tail => exact .cons head.1 (ih tail)
      exact namePairs evidence.recursors htranslations
    have hnames := List.forall₂_eq.mp hpair
    simpa only [List.map_map, Function.comp_def, hnames] using
      evidence.recursorFresh.nodup hconstructorWF
  refine {
    inductiveEvidence := hinduct
    translations := htranslations
    recursorAdd := evidence.recursorAdd
    recursorNodup := hrecursorNodup
    recursorFresh := by
      intro model hmem
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hmem
      have hshape := (evidence.recursorTranslation entry hentry).2
      have hfresh := FreshRecursors.baseFresh hconstructorWF evidence.recursorFresh entry hentry
      rw [← hshape]
      exact hfresh
    resultMap := by
      calc
        resultConstants = insertRecursors evidence.constructorConstants evidence.recursors :=
          evidence.resultMap
        _ = insertConsts evidence.constructorConstants
            ((evidence.recursors.map (·.info)).map (fun info => .recInfo info)) := by
          exact (insertConsts_recursorInfoMap evidence.constructorConstants evidence.recursors).symm
  }

/- Expose the complete staged registration receipt at an arbitrary safety
   threshold.  The native producer is checked at `.safe`; lowering the
   threshold is sound and lets legacy consumers retain their chosen policy
   without rebuilding the header/constructor/recursor witness. -/
theorem RegistrationEvidence.to_addInductWithRecursorsEvidence_at
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (safety : DefinitionSafety) (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    AddInductWithRecursorsEvidence safety constants env decl
      evidence.constructorConstants evidence.constructorEnv
      (evidence.recursors.map (·.info)) (evidence.recursors.map (·.model))
      resultConstants result :=
  (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).sf_mono
    DefinitionSafety.le_safe

theorem RegistrationEvidence.to_trEnvInductive
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (history : TrEnvInductive safety constants Q env)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    TrEnvInductive safety resultConstants Q result := by
  have hdecl : VDecl.WF env (.induct decl) evidence.constructorEnv := by
    apply VDecl.WF.induct evidence.declWF
    unfold VEnv.addInduct
    rw [evidence.headerAdd]
    exact evidence.constructorAdd
  refine TrEnvInductive.induct (C := constants) (Q := Q) (env := env) (decl := decl)
    (inductiveEnv := evidence.constructorEnv)
    (inductiveConstants := evidence.constructorConstants)
    (recursors := evidence.recursors.map (·.info))
    (models := evidence.recursors.map (·.model))
    (resultConstants := resultConstants) (result := result) history hdecl ?_
  exact (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).sf_mono
    DefinitionSafety.le_safe

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

theorem RegistrationEvidence.orderedModelMap
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    resultConstants = insertOrderedModel constants evidence.orderedEntries := by
  calc
    resultConstants = insertOrdered constants evidence.orderedEntries := evidence.orderedMap
    _ = insertOrderedModel constants evidence.orderedEntries :=
      insertOrdered_modelShape constants evidence.orderedEntries evidence.orderedModelShape

theorem RegistrationEvidence.headerModelMembership
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : HeaderEntry} (hmem : entry ∈ evidence.headers) :
    ∃ type ∈ decl.types, entry.model = type.toVConstVal := by
  have hmodel : entry.model ∈ evidence.headers.map (·.model) :=
    List.mem_map.mpr ⟨entry, hmem, rfl⟩
  rw [evidence.headerModels] at hmodel
  obtain ⟨type, htype, heq⟩ := List.mem_map.mp hmodel
  exact ⟨type, htype, heq.symm⟩

theorem RegistrationEvidence.constructorModelMembership
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : ConstructorEntry} (hmem : entry ∈ evidence.constructors) :
    ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor := by
  have hmodel : entry.model ∈ evidence.constructors.map (·.model) :=
    List.mem_map.mpr ⟨entry, hmem, rfl⟩
  rw [evidence.constructorModels] at hmodel
  exact ⟨entry.model, hmodel, rfl⟩

theorem RegistrationEvidence.orderedModelMembership
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries, match entry with
      | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
      | .constructor entry => ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
      | .recursor _ => True := by
  intro entry hmem
  simp only [RegistrationEvidence.orderedEntries, List.mem_append] at hmem
  rcases hmem with hphase | hrecursors
  · rcases hphase with hheaders | hconstructors
    · rcases List.mem_map.mp hheaders with ⟨header, hmem, rfl⟩
      exact evidence.headerModelMembership hmem
    · rcases List.mem_map.mp hconstructors with ⟨constructor, hmem, rfl⟩
      exact evidence.constructorModelMembership hmem
  · rcases List.mem_map.mp hrecursors with ⟨recursor, hmem, rfl⟩
    trivial

theorem RegistrationEvidence.orderedEntryReceipt
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.orderedEntries,
      entry.Semantic env evidence.headerEnv evidence.constructorEnv ∧
        entry.ModelShape ∧
        (∃ semantic, match entry with
          | .header entry =>
            TrExprS env entry.info.levelParams [] entry.info.type semantic
          | .constructor entry =>
            TrExprS evidence.headerEnv entry.info.levelParams [] entry.info.type semantic
          | .recursor entry =>
            TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic) ∧
        match entry with
          | .header entry => ∃ type ∈ decl.types, entry.model = type.toVConstVal
          | .constructor entry =>
            ∃ constructor ∈ decl.constructorHeaders, entry.model = constructor
          | .recursor _ => True := by
  intro entry hmem
  cases entry with
  | header entry =>
    have hsemantic := evidence.orderedSemantic (.header entry) hmem
    refine ⟨hsemantic, hsemantic.modelShape, ?_, ?_⟩
    · exact ⟨_, hsemantic.1.2.2⟩
    · exact evidence.orderedModelMembership (.header entry) hmem
  | constructor entry =>
    have hsemantic := evidence.orderedSemantic (.constructor entry) hmem
    refine ⟨hsemantic, hsemantic.modelShape, ?_, ?_⟩
    · exact ⟨_, hsemantic.1.2.2⟩
    · exact evidence.orderedModelMembership (.constructor entry) hmem
  | recursor entry =>
    have hsemantic := evidence.orderedSemantic (.recursor entry) hmem
    refine ⟨hsemantic, hsemantic.modelShape, ?_, ?_⟩
    · exact ⟨_, hsemantic.1.2.2⟩
    · exact evidence.orderedModelMembership (.recursor entry) hmem

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
