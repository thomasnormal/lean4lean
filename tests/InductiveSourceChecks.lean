import Lean4Lean.Verify.InductiveSourceChecks
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive

namespace InductiveSourceChecksTest

theorem checkedSources (env : Kernel.Environment) (types : List InductiveType) :
    (Lean4Lean.Environment.checkInductiveSources env types).WF fun _ =>
      InductiveSourcesNoMVarNoFVar types :=
  Lean4Lean.Environment.checkInductiveSources.WF env types

theorem cleanSourcesNoOp (env : Kernel.Environment) (types : List InductiveType)
    (hsources : InductiveSourcesNoMVarNoFVar types) :
    Lean4Lean.Environment.checkInductiveSources env types = .ok () :=
  Lean4Lean.Environment.checkInductiveSources.eq_pure env types hsources

theorem structuralFreshness (type : Expr) (hfvars : type.FVarsIn (fun _ => False))
    (ngen : NameGenerator) : SourceReserved type ngen :=
  SourceReserved.of_fvarsIn_false hfvars ngen

theorem headerFreshness (types : List InductiveType)
    (hsources : InductiveSourcesNoMVarNoFVar types) (indType : InductiveType)
    (hmem : indType ∈ types) (ngen : NameGenerator) : SourceReserved indType.type ngen :=
  hsources.headerReserved indType hmem ngen

theorem constructorFreshness (types : List InductiveType)
    (hsources : InductiveSourcesNoMVarNoFVar types) (indType : InductiveType)
    (hmem : indType ∈ types) (ctor : Constructor) (hctor : ctor ∈ indType.ctors)
    (ngen : NameGenerator) : SourceReserved ctor.type ngen :=
  hsources.constructorReserved indType hmem ctor hctor ngen

theorem fullFrontendSources (env : Kernel.Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig) :
    (Lean4Lean.Environment.addInductive env lparams numParams types isUnsafe allowPrimitive fuel).WF
      fun _ => InductiveSourcesNoMVarNoFVar types :=
  Lean4Lean.Environment.addInductive.sources env lparams numParams types isUnsafe allowPrimitive fuel

theorem declarationSources (env : Kernel.Environment) (lparams : List Name) (numParams : Nat)
    (types : List InductiveType) (isUnsafe check : Bool) (fuel : FuelConfig) :
    (Lean4Lean.addDecl env (.inductDecl lparams numParams types isUnsafe) check fuel).WF
      fun _ => InductiveSourcesNoMVarNoFVar types :=
  Lean4Lean.addDecl.inductiveSources env lparams numParams types isUnsafe check fuel

theorem frontendConstructorFreshness (env : Kernel.Environment) (lparams : List Name)
    (numParams : Nat) (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) :
    (Lean4Lean.Environment.addInductive env lparams numParams types isUnsafe allowPrimitive fuel).WF
      fun _ => ∀ indType ∈ types, ∀ ctor ∈ indType.ctors, ∀ ngen, SourceReserved ctor.type ngen :=
  Lean4Lean.Environment.addInductive.constructorReserved env lparams numParams types
    isUnsafe allowPrimitive fuel

private def batch (numTypes numCtors : Nat) (owner : Nat) (ctorIndex : Option Nat)
    (poison : Expr) : List InductiveType :=
  (List.range numTypes).map fun typeIndex =>
    let name := Name.mkNum `SourceOwner typeIndex
    let clean := Expr.sort (.succ .zero)
    let type := if typeIndex = owner && ctorIndex.isNone then poison else clean
    let ctors := (List.range numCtors).map fun index => {
      name := Name.mkNum name index
      type := if typeIndex = owner && ctorIndex = some index then poison else clean : Constructor }
    { name, type, ctors }

private def sourcePoisons : List Expr :=
  let id : FVarId := ⟨`OutsideSource⟩
  let sortType := Expr.sort (.succ .zero)
  [.fvar ⟨.num `_nested_fresh 0⟩, .fvar ⟨.num `_nested_fresh 1⟩,
    .fvar ⟨.num `_nested_fresh 2⟩, .fvar ⟨.num `_nested_fresh 17⟩, .fvar id,
    .mvar ⟨`Unassigned⟩, .sort (.mvar ⟨`UnassignedLevel⟩),
    .const `Family [.mvar ⟨`UnassignedLevel⟩], mkApp (.fvar id) sortType,
    .lam `binder sortType (.fvar id) .implicit,
    .letE `binder sortType (.fvar id) (.bvar 0) true,
    .mdata {} (.fvar id), .proj `Pair 0 (.fvar id), mkApp (.mvar ⟨`Unassigned⟩) (.fvar id)]

private def checkRejected (result : Except Kernel.Exception ResultType)
    (expectedName : Name) (source : Expr) : MetaM Unit := do
  match result with
  | .error (.declHasMVars _ name original) =>
    unless source.hasMVar && name == expectedName && original == source do
      throwError "metavariable rejection did not retain the original declaration/name"
  | .error (.declHasFVars _ name original) =>
    unless !source.hasMVar && source.hasFVar && name == expectedName && original == source do
      throwError "free-variable rejection did not retain the original declaration/name"
  | _ => throwError "invalid source did not produce its original-variable diagnostic"

private def checkPreflight (env : Kernel.Environment) : MetaM Unit := do
  for numTypes in [0, 1, 2, 33] do
    for numCtors in [0, 1, 2, 33, 65] do
      unless (Lean4Lean.Environment.checkInductiveSources env
          (batch numTypes numCtors 0 none (.sort (.succ .zero)))).isOk do
        throwError "clean source preflight unexpectedly failed"
  for poison in sourcePoisons do
    for owner in [0, 1, 32] do
      let name := Name.mkNum `SourceOwner owner
      checkRejected (Lean4Lean.Environment.checkInductiveSources env (batch 33 33 owner none poison))
        name poison
      for ctorIndex in [0, 1, 32] do
        checkRejected
          (Lean4Lean.Environment.checkInductiveSources env (batch 33 33 owner (some ctorIndex) poison))
          (Name.mkNum name ctorIndex) poison

private def parameterBinders (numParams : Nat) (body : Expr) : Expr :=
  (List.range numParams).foldr (fun index result =>
    .forallE (Name.mkNum `parameter index) (.sort (.succ .zero)) result .implicit) body

private def familyApp (name : Name) (numParams offset : Nat) : Expr :=
  mkAppN (.const name []) ((List.range numParams).map fun index =>
    Expr.bvar (numParams - 1 - index + offset)).toArray

private def checkValidFrontend (env : Lean.Environment) (numParams : Nat)
    (isUnsafe nested check : Bool) : MetaM Unit := do
  let name := `CleanSourceDatatype
  let domain := if nested then mkApp (.const ``List [.zero]) (familyApp name numParams 0)
    else .const ``Nat []
  let ctorType := parameterBinders numParams (.forallE `field domain (familyApp name numParams 1) .default)
  let ctor : Constructor := { name := name ++ `mk, type := ctorType }
  let decl := Declaration.inductDecl [] numParams [{
    name, type := parameterBinders numParams (.sort (.succ .zero)), ctors := [ctor] }] isUnsafe
  unless (env.addDeclCore 0 decl none).isOk do
    throwError "clean source unexpectedly fails native validation"
  match Lean4Lean.addDecl env.toKernelEnv decl check with
  | .ok _ => pure ()
  | .error (.other message) =>
    throwError "unexpected clean-source rejection: {message}"
  | .error _ => throwError "unexpected structured clean-source rejection"

private def captureType (index : Nat) : InductiveType :=
  let name := `SourceCaptureDatatype
  let sortType := Expr.sort (.succ .zero)
  let header := Expr.forallE `A sortType sortType .default
  let ctorType := Expr.forallE `A sortType
    (.forallE `field (.fvar ⟨.num `_nested_fresh index⟩)
      (mkApp (.const name []) (.bvar 1)) .default) .default
  { name, type := header, ctors := [{ name := name ++ `mk, type := ctorType }] }

private def checkCapturedFrontend (env : Kernel.Environment) : MetaM Unit := do
  for index in [0, 1, 2, 17] do
    let indType := captureType index
    let ctor := indType.ctors[0]!
    for isUnsafe in [false, true] do
      for check in [false, true] do
        checkRejected
          (Lean4Lean.addDecl env (.inductDecl [] 1 [indType] isUnsafe) check) ctor.name ctor.type
  let indType := captureType 2
  let .ok result := StateT.run' (ElimNestedInductive.run ({} : FuelConfig).inductiveFuel 1 [indType] env)
      { lvls := [], newTypes := #[indType] }
    | throwError "unguarded source-capture preprocessing no longer succeeds"
  let .ok added := AddInductive.run 1 result.types result.aux2nested.size {
    env, lparams := [], safety := .safe, allowPrimitive := false }
    | throwError "unguarded staged checker no longer accepts the captured constructor"
  let some (.ctorInfo stored) := added.find? (indType.name ++ `mk)
    | throwError "unguarded capture did not install its constructor"
  let expected := Expr.forallE `A (.sort (.succ .zero))
    (.forallE `field (.bvar 0) (mkApp (.const indType.name []) (.bvar 1)) .default) .default
  unless stored.type == expected && !stored.type.hasFVar do
    throwError "unguarded preprocessing no longer exposes the original source-capture bug"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``SourceReserved.of_fvarsIn_false,
      ``InductiveSourcesNoMVarNoFVar.headerReserved,
      ``InductiveSourcesNoMVarNoFVar.constructorReserved] do
    audit theoremName []
  let interfaces := [``Expr.hasFVar_eq, ``Expr.hasExprMVar_eq, ``Expr.hasLevelMVar_eq,
    ``Level.hasMVar_eq]
  for theoremName in [``Lean4Lean.Environment.checkInductiveSources.WF,
      ``Lean4Lean.Environment.checkInductiveSources.eq_pure,
      ``Lean4Lean.Environment.addInductive.sources, ``Lean4Lean.addDecl.inductiveSources,
      ``Lean4Lean.Environment.addInductive.constructorReserved] do
    audit theoremName interfaces
  let env ← Lean.getEnv
  checkPreflight env.toKernelEnv
  checkCapturedFrontend env.toKernelEnv
  for numParams in [0, 1, 2] do
    for isUnsafe in [false, true] do
      for nested in [false, true] do
        for check in [false, true] do
          checkValidFrontend env numParams isUnsafe nested check
  logInfo "checked 20 clean/168 invalid source batches, 16 captured frontend rejections, 24 clean native/frontend accepts, and the unguarded capture pipeline"

end InductiveSourceChecksTest
