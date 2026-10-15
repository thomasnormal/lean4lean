import Lean4Lean.Verify.Environment.Basic

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

theorem RegistrationEvidence.recursor_translation_receipt
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    ∀ entry ∈ evidence.recursors,
      TrConstVal .safe evidence.constructorEnv (.recInfo entry.info) entry.model :=
  evidence.recursorTranslation

end NativeInductive

end Lean4Lean
