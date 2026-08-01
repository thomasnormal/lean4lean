import Lean4Lean.TypeChecker
import Lean4Lean.Quot
import Lean4Lean.Inductive.Add
import Lean4Lean.Primitive

namespace Lean4Lean
open Lean hiding Environment Exception
open TypeChecker Kernel Environment

open private Lean.Kernel.Environment.add from Lean.Environment
open private markQuotInit from Lean.Environment
open private quotTypeExpr quotMkTypeExpr quotLiftTypeExpr quotIndTypeExpr from Lean4Lean.Quot

def Environment.definitionPrimitives : NameSet := .ofList [
  ``Nat.add, ``Nat.pred, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
  ``Nat.bitwise, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList, ``Char.ofNat]

def checkPrimitiveGuard (b : Bool) (e : Exception) : Except Exception Unit :=
  if b then pure () else throw e

def checkPrimitiveHeader (v : DefinitionVal) : Except Exception Unit := do
  checkPrimitiveGuard (Environment.definitionPrimitives.contains v.name) <|
    .other s!"invalid primitive definition {v.name}"
  checkPrimitiveGuard (v.safety == .safe && v.levelParams.isEmpty) <|
    .other s!"invalid safety or universe parameters for primitive {v.name}"
  checkPrimitiveGuard (!(v.name == ``Char.ofNat) || v.type == q(Nat → Char)) <|
    .other "invalid type for primitive Char.ofNat"
  checkPrimitiveGuard (!(v.name == ``String.ofList) || v.type == q(List Char → String)) <|
    .other "invalid type for primitive String.ofList"

def checkStringPrimitiveDeps (v : DefinitionVal) : M Unit := do
  if v.name == ``String.ofList then
    _ ← checkType q(List Char)
    let nilType ← checkType q(List.nil (α := Char))
    unless ← isDefEq nilType q(List Char) do
      throw <| .other "invalid type for List.nil"
    _ ← checkType q(Char → List Char → List Char)
    let consType ← checkType q(List.cons (α := Char))
    unless ← isDefEq consType q(Char → List Char → List Char) do
      throw <| .other "invalid type for List.cons"

def checkConstantVal (env : Environment) (v : ConstantVal) (allowPrimitive := false) : M Unit := do
  checkName env v.name allowPrimitive
  checkDuplicatedUnivParams v.levelParams
  checkNoMVarNoFVar env v.name v.type
  let sort ← checkType v.type
  _ ← ensureSort sort v.type

def checkPrimitiveDefinition (env : Environment) (v : DefinitionVal)
    (fuel : FuelConfig) : Except Exception Unit := do
  checkPrimitiveHeader v
  let allowPrimitive ← M.run env (safety := .safe) (lctx := {})
    (lparams := v.levelParams) (fuel := fuel) (Environment.checkPrimitiveDef v)
  let _ ← if allowPrimitive then
      M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams)
        (fuel := fuel) (checkStringPrimitiveDeps v)
    else pure ()
  M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
    checkConstantVal env v.toConstantVal allowPrimitive
    Kernel.Environment.checkNoMVarNoFVar env v.name v.value
    let valType ← TypeChecker.checkType v.value
    if !(← isDefEq valType v.type) then
      throw <| Exception.declTypeMismatch env (.defnDecl v) valType

def addAxiom (env : Environment) (v : AxiomVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    _ ← (checkConstantVal env v.toConstantVal).run env
      (safety := if v.isUnsafe then .unsafe else .safe) (lparams := v.levelParams) (fuel := fuel)
  return env.add (.axiomInfo v)

def addDefinitionHeader (env : Environment) (v : DefinitionVal)
    (fuel : FuelConfig := {}) : Except Exception Environment := do
  _ ← (checkConstantVal env v.toConstantVal).run env
    (safety := v.safety) (lparams := v.levelParams) (fuel := fuel)
  return env.add (.defnInfo v)

def addDefinition (env : Environment) (v : DefinitionVal)
    (check := true) (fuel : FuelConfig := {}) : Except Exception Environment := do
  if let .unsafe := v.safety then
    -- Meta definition can be recursive.
    -- So, we check the header, add, and then type check the body.
    let env' ← if check then addDefinitionHeader env v fuel else pure <| env.add (.defnInfo v)
    if check then
      checkNoMVarNoFVar env' v.name v.value
      M.run env' (safety := .unsafe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
        let valType ← TypeChecker.checkType v.value
        if !(← isDefEq valType v.type) then
          throw <| .declTypeMismatch env' (.defnDecl v) valType
    return env'
  else
    if check then
      if Environment.primitives.contains v.name then
        checkPrimitiveDefinition env v fuel
      else
        M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
          checkConstantVal env v.toConstantVal false
          checkNoMVarNoFVar env v.name v.value
          let valType ← TypeChecker.checkType v.value
          if !(← isDefEq valType v.type) then
            throw <| .declTypeMismatch env (.defnDecl v) valType
    return env.add (.defnInfo v)

def addMutualHeaders (env : Environment) (safety : DefinitionSafety)
    (levelParams : List Name) (fuel : FuelConfig := {}) :
    List DefinitionVal → Except Exception Environment
  | [] => pure env
  | v :: vs => do
    if v.safety != safety then
      throw <| .other
        "invalid mutual definition, declarations must have the same safety annotation"
    if v.levelParams != levelParams then
      throw <| .other
        "invalid mutual definition, declarations must have the same universe parameters"
    let env ← addDefinitionHeader env v fuel
    addMutualHeaders env safety levelParams fuel vs

def checkMutualBodies (env : Environment) (safety : DefinitionSafety)
    (levelParams : List Name) (vs : List DefinitionVal)
    (fuel : FuelConfig := {}) : Except Exception Unit :=
  M.run env (safety := safety) (lctx := {}) (lparams := levelParams) (fuel := fuel) do
    for v in vs do
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.mutualDefnDecl vs) valType

def addTheorem (env : Environment) (v : TheoremVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    -- TODO(Leo): we must add support for handling tasks here
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
      checkConstantVal env v.toConstantVal
      if !(← isProp v.type) then
        throw <| .thmTypeIsNotProp env v.name v.type
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.thmDecl v) valType
  return env.add (.thmInfo v)

def addOpaque (env : Environment) (v : OpaqueVal) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  if check then
    M.run env (safety := .safe) (lctx := {}) (lparams := v.levelParams) (fuel := fuel) do
      checkConstantVal env v.toConstantVal
      checkNoMVarNoFVar env v.name v.value
      let valType ← TypeChecker.checkType v.value
      if !(← isDefEq valType v.type) then
        throw <| .declTypeMismatch env (.opaqueDecl v) valType
  return env.add (.opaqueInfo v)

def addMutual (env : Environment) (vs : List DefinitionVal)
    (check := true) (fuel : FuelConfig := {}) : Except Exception Environment := do
  let v₀ :: _ := vs | throw <| .other "invalid empty mutual definition"
  if let .safe := v₀.safety then
    throw <| .other "invalid mutual definition, declaration is not tagged as unsafe/partial"
  let env' ← if check then addMutualHeaders env v₀.safety v₀.levelParams fuel vs else
    pure <| vs.foldl (fun env v => env.add (.defnInfo v)) env
  if check then
    checkMutualBodies env' v₀.safety v₀.levelParams vs fuel
  return env'

/-- Type check given declaration and add it to the environment -/
def addDecl (env : Environment) (decl : Declaration) (check := true) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  match decl with
  | .axiomDecl v => addAxiom env v check fuel
  | .defnDecl v => addDefinition env v check fuel
  | .thmDecl v => addTheorem env v check fuel
  | .opaqueDecl v => addOpaque env v check fuel
  | .mutualDefnDecl v => addMutual env v check fuel
  | .quotDecl => addQuot env
  | .inductDecl lparams nparams types isUnsafe =>
    let allowPrimitive ← checkPrimitiveInductive env lparams nparams types isUnsafe
    addInductive env lparams nparams types isUnsafe allowPrimitive fuel

def addQuotInfo (env : Environment) (v : QuotVal)
    (fuel : FuelConfig := {}) : Except Exception Environment := do
  _ ← (checkConstantVal env v.toConstantVal).run env
    (safety := .safe) (lparams := v.levelParams) (fuel := fuel)
  return env.add (.quotInfo v)

def addQuotVerified (env : Environment) (fuel : FuelConfig := {}) : Except Exception Environment := do
  if env.quotInit then return env
  checkEqType env
  let quot : QuotVal := {
    name := ``Quot, kind := .type, levelParams := [`u], type := quotTypeExpr }
  let env ← addQuotInfo env quot fuel
  let quotMk : QuotVal := {
    name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := quotMkTypeExpr }
  let env ← addQuotInfo env quotMk fuel
  let quotLift : QuotVal := {
    name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := quotLiftTypeExpr }
  let env ← addQuotInfo env quotLift fuel
  let quotInd : QuotVal := {
    name := ``Quot.ind, kind := .ind, levelParams := [`u], type := quotIndTypeExpr }
  return markQuotInit <| ← addQuotInfo env quotInd fuel

/-- The declaration fragment covered by the current end-to-end verification proof. -/
def addDeclVerified (env : Environment) (decl : Declaration)
    (fuel : FuelConfig := {}) : Except Exception Environment := do
  match decl with
  | .axiomDecl v => addAxiom env v true fuel
  | .defnDecl v => addDefinition env v true fuel
  | .thmDecl v => addTheorem env v true fuel
  | .opaqueDecl v => addOpaque env v true fuel
  | .mutualDefnDecl vs => addMutual env vs true fuel
  | .quotDecl => addQuotVerified env fuel
  | .inductDecl .. =>
    throw <| .other "inductive declarations are not supported by the verified checker"
