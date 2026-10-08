import Lean4Lean.Verify.ConstructorHeaders
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace ConstructorHeadersTest

private def parentHeaders : List VInductiveType := boolInductDecl.types ++ natInductDecl.types
private def ctors : List VConstVal := parentHeaders.flatMap (·.ctors)
private def headerEnv : VEnv := (VEnv.empty.addInductHeaders parentHeaders).getD VEnv.empty
private def ctorEnv : VEnv := (headerEnv.addConstructorHeaders ctors).getD headerEnv

example : headerEnv.addConstructorHeaders ctors = some ctorEnv := rfl
example : headerEnv.addConstructorHeaders [] = some headerEnv := rfl
example : ctorEnv.constants ``Bool.true = some { uvars := 0, type := .const ``Bool [] } := rfl
example : ctorEnv.constants ``Nat.zero = some { uvars := 0, type := .const ``Nat [] } := rfl
example : ctorEnv.constants ``Nat.succ = some {
    uvars := 0, type := .forallE (.const ``Nat []) (.const ``Nat []) } := rfl
example : ctorEnv.constants ``Bool.rec = none := rfl
example : ctorEnv.constants ``Nat.rec = none := rfl
example : (ctorEnv.addConstructorHeaders ctors).isSome = false := by decide
example : (headerEnv.addConstructorHeaders (ctors ++ ctors)).isSome = false := by decide
example : headerEnv ≤ ctorEnv := VEnv.addConstructorHeaders.le (ctors := ctors) rfl
example : ctorEnv.defeqs = headerEnv.defeqs :=
  VEnv.addConstructorHeaders.defeqs_eq (ctors := ctors) rfl

example (env env' : VEnv) (ctors : List VConstVal) (hordered : env.Ordered)
    (htypes : ∀ ctor ∈ ctors, ctor.toVConstant.WF env)
    (hadd : env.addConstructorHeaders ctors = some env') : env'.Ordered :=
  VEnv.addConstructorHeaders.ordered hordered htypes hadd

example (oldEnv env : VEnv) (lparams : List Name) (types : List InductiveType)
    (vtypes : List VInductiveType)
    (htr : List.Forall₂ (TrInductiveType oldEnv env lparams) types vtypes) :
    List.Forall₂ (fun type vtype =>
      List.Forall₂ (TrConstructor env lparams) type.ctors vtype.ctors) types vtypes :=
  htr.imp fun _ _ htype => htype.2.2.2

example (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (types : Array InductiveType) (isUnsafe : Bool) {safety : DefinitionSafety}
    {env : VEnv} {vtypes : List VInductiveType} (haligned : Aligned safety ctx.env.constants env)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun type vtype =>
      List.Forall₂ (TrConstructor env ctx.lparams) type.ctors vtype.ctors) types.toList vtypes) :
    (AddInductive.declareConstructors stats types isUnsafe ctx).WF fun result =>
      ∃ env', env.addConstructorHeaders (vtypes.flatMap (·.ctors)) = some env' ∧
        env ≤ env' ∧ env'.defeqs = env.defeqs ∧ Aligned safety result.constants env' :=
  (AddInductive.declareConstructors.refines ctx stats types isUnsafe
    haligned hsafety hctors).mono fun _ ⟨env', hadd, haligned'⟩ =>
      ⟨env', hadd, VEnv.addConstructorHeaders.le hadd,
        VEnv.addConstructorHeaders.defeqs_eq hadd, haligned'⟩

private def context (isUnsafe : Bool) : AddInductive.Context := {
  env := Kernel.Environment.empty `ConstructorHeadersTest, lparams := [],
  safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }

private def datatype (name : Name) (ctors : List Constructor) : InductiveType := {
  name, type := .sort (.succ .zero), ctors }

private def mutualTypes : Array InductiveType := #[
  datatype `Left [⟨`Left.unit, .const `Left []⟩,
    ⟨`Left.swap, .forallE `right (.const `Right []) (.const `Left []) .default⟩],
  datatype `Right [⟨`Right.wrap, .forallE `left (.const `Left []) (.const `Right []) .default⟩]]

private def checkedStage (numParams : Nat) (types : Array InductiveType) (isUnsafe : Bool) :
    AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes numParams types fun stats => do
    let headers ← AddInductive.declareInductiveTypes stats numParams types 0 isUnsafe
    AddInductive.withEnv headers do
      AddInductive.checkConstructors types stats isUnsafe
      AddInductive.declareConstructors stats types isUnsafe

private def checkMetadata (ctx : AddInductive.Context) (numParams : Nat)
    (types : Array InductiveType) (fields : Array (Array Nat)) (isUnsafe : Bool) : MetaM Unit := do
  let .ok result := checkedStage numParams types isUnsafe ctx
    | throwError "failed checked constructor staging"
  unless types.size == fields.size do throwError "invalid metadata fixture"
  for type in types, expected in fields do
    unless type.ctors.length == expected.size do throwError "invalid constructor-count fixture"
    let mut index := 0
    for ctor in type.ctors do
      let some (.ctorInfo info) := result.find? ctor.name | throwError "missing {ctor.name}"
      unless info.name == ctor.name && info.type == ctor.type && info.induct == type.name &&
          info.cidx == index && info.levelParams == ctx.lparams && info.numParams == numParams &&
          info.numFields == expected[index]! && info.isUnsafe == isUnsafe do
        throwError "incorrect constructor metadata for {ctor.name}"
      index := index + 1
    if result.contains (type.name ++ `rec) then throwError "constructor staging installed a recursor"
  if numParams == 0 && !types.isEmpty then
    let stats : AddInductive.InductiveStats := {
      levels := ctx.lparams.map .param, resultLevel := .succ .zero,
      nindices := types.map fun _ => 0, indConsts := types.map fun type => .const type.name [],
      params := #[], isNotZero := true }
    if (AddInductive.declareConstructors stats types isUnsafe { ctx with env := result }).isOk then
      throwError "accepted an existing constructor-name collision"

private def importedTypes (env : Kernel.Environment) : MetaM (Array InductiveType) := do
  [``Bool, ``Nat].toArray.mapM fun name => do
    let some (.inductInfo info) := env.find? name | throwError "missing primitive {name}"
    let ctors ← info.ctors.mapM fun name => do
      let some (.ctorInfo info) := env.find? name | throwError "missing primitive constructor"
      pure ({ name, type := info.type } : Constructor)
    pure { name, type := info.type, ctors }

private def rejectStage (ctx : AddInductive.Context) (types : Array InductiveType) : MetaM Unit := do
  if (checkedStage 0 types false ctx).isOk then throwError "accepted invalid constructor fixture"

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [``VEnv.addConstructorHeaders.append, ``VEnv.addConstructorHeaders.le,
      ``VEnv.addConstructorHeaders.constants, ``VEnv.addConstructorHeaders.defeqs_eq,
      ``VEnv.addConstructorHeaders.ordered] do
    audit theoremName standard
  audit ``TrConstructor.mono (standard ++ [``sorryAx])
  let registration := standard ++ [``sorryAx, ``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentHashMap.WF.toList'_insert]
  audit ``AddInductive.declareConstructors.refines registration
  audit ``AddInductive.declareConstructors.ordered registration
  let primitives ← importedTypes (← Lean.getEnv).toKernelEnv
  for isUnsafe in [false, true] do
    checkMetadata (context isUnsafe) 0 mutualTypes #[#[0, 1], #[1]] isUnsafe
    checkMetadata { context isUnsafe with allowPrimitive := true } 0 primitives
      #[#[0, 0], #[0, 1]] isUnsafe
    checkMetadata (context isUnsafe) 0 #[] #[] isUnsafe
    let boxType : Expr := .forallE `A (.sort (.param `u)) (.sort (.param `u)) .default
    let boxCtor : Expr := .forallE `A (.sort (.param `u))
      (.forallE `value (.bvar 0) (.app (.const `Box [.param `u]) (.bvar 1)) .default) .default
    let box : InductiveType := { name := `Box, type := boxType, ctors := [⟨`Box.mk, boxCtor⟩] }
    checkMetadata { context isUnsafe with lparams := [`u] } 1 #[box] #[#[1]] isUnsafe
  let ctx := context false
  rejectStage ctx #[datatype `Wrong [⟨`Wrong.mk, .const `Other []⟩], datatype `Other []]
  rejectStage ctx #[datatype `First [⟨`Shared, .const `First []⟩],
    datatype `Second [⟨`Shared, .const `Second []⟩]]
  rejectStage ctx #[datatype `Duplicate [⟨`Duplicate.mk, .const `Duplicate []⟩,
    ⟨`Duplicate.mk, .const `Duplicate []⟩]]
  let negative : InductiveType := datatype `Negative [⟨`Negative.mk,
    .forallE `function (.forallE `input (.const `Negative []) (.const `Negative []) .default)
      (.const `Negative []) .default⟩]
  rejectStage ctx #[negative]
  checkMetadata (context true) 0 #[negative] #[#[1]] true

end ConstructorHeadersTest
