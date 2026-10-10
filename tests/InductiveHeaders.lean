import Lean4Lean.Verify.Inductive
import Lean4Lean.Verify.InductiveHeaders
import Lean4Lean.Inductive.Add
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace InductiveHeadersTest

private def headers : List VInductiveType := boolInductDecl.types ++ natInductDecl.types

private def stagedEnv : VEnv := (VEnv.empty.addInductHeaders headers).getD VEnv.empty

example : VEnv.empty.addInductHeaders headers = some stagedEnv := rfl

example : stagedEnv.Ordered := by
  apply VEnv.addInductHeaders.ordered VEnv.Ordered.empty ?_ (show
    VEnv.empty.addInductHeaders headers = some stagedEnv from rfl)
  intro header hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact (boolInductDecl.headersWF header hmem).2
  · exact (natInductDecl.headersWF header hmem).2

example : stagedEnv.WF := by
  apply VEnv.addInductHeaders.wf (env := VEnv.empty) (env' := stagedEnv)
    ⟨[], .empty⟩ ?_ (show VEnv.empty.addInductHeaders headers = some stagedEnv from rfl)
  intro header hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact (boolInductDecl.headersWF header hmem).2
  · exact (natInductDecl.headersWF header hmem).2

example : stagedEnv.constants ``Bool = some { uvars := 0, type := .sort (.succ .zero) } := rfl
example : stagedEnv.constants ``Nat = some { uvars := 0, type := .sort (.succ .zero) } := rfl

example : [``Bool.false, ``Bool.true, ``Nat.zero, ``Nat.succ].any
    (fun name => (stagedEnv.constants name).isSome) = false := by decide

example : (VEnv.empty.addInductHeaders (headers ++ headers)).isSome = false := by decide
example : (stagedEnv.addInductHeaders boolInductDecl.types).isSome = false := by decide
example : (stagedEnv.addInductHeaders natInductDecl.types).isSome = false := by decide
example : VEnv.empty.addInductHeaders [] = some VEnv.empty := rfl

example (env env' : VEnv) (decl : VInductDecl) (hheaders : decl.HeadersWF env)
    (hordered : env.Ordered) (hadd : env.addInductHeaders decl.types = some env') :
    env'.Ordered :=
  VEnv.addInductHeaders.ordered hordered (fun header hmem => (hheaders header hmem).2) hadd

example (env env' : VEnv) (hadd : env.addInductHeaders headers = some env') :
    env'.defeqs = env.defeqs := VEnv.addInductHeaders.defeqs_eq hadd

private def polymorphicHeader : VInductiveType := {
  name := `Parametric
  uvars := 1
  type := .sort (.param 0)
  ctors := []
}

example : polymorphicHeader.toVConstant.WF VEnv.empty := ⟨_, .sort (by decide)⟩

example : ((VEnv.empty.addInductHeaders [polymorphicHeader]).getD VEnv.empty).Ordered := by
  apply VEnv.addInductHeaders.ordered VEnv.Ordered.empty ?_ (show
    VEnv.empty.addInductHeaders [polymorphicHeader] = some
      ((VEnv.empty.addInductHeaders [polymorphicHeader]).getD VEnv.empty) from rfl)
  intro header hmem
  simp only [List.mem_singleton] at hmem
  subst header
  exact ⟨_, .sort (by decide)⟩

example {env ctorEnv : VEnv} {lparams : List Name} {types : List InductiveType}
    {headers : List VInductiveType}
    (htr : List.Forall₂ (TrInductiveType env ctorEnv lparams) types headers) :
    List.Forall₂ (TrInductiveHeader env lparams) types headers :=
  htr.imp fun _ _ htype => htype.header

private def ordinaryType (name : Name) : InductiveType := {
  name, type := .sort (.succ .zero), ctors := [] }

private def ordinaryHeader (name : Name) : VInductiveType := {
  name, uvars := 0, type := .sort (.succ .zero), ctors := [] }

private def ordinaryTypes : Array InductiveType := #[ordinaryType `First, ordinaryType `Second]

private def ordinaryHeaders : List VInductiveType := [ordinaryHeader `First, ordinaryHeader `Second]

private def ordinaryStats : AddInductive.InductiveStats := {
  levels := [], resultLevel := .succ .zero, nindices := #[0, 0],
  indConsts := #[.const `First [], .const `Second []], params := #[], isNotZero := true }

private def ordinaryContext (isUnsafe : Bool) : AddInductive.Context := {
  env := Kernel.Environment.empty `InductiveHeadersTest,
  lparams := [], safety := if isUnsafe then .unsafe else .safe, allowPrimitive := false }

private def checkedHeaders (numParams : Nat) (types : Array InductiveType) (isUnsafe : Bool) :
    AddInductive.M Kernel.Environment :=
  AddInductive.checkInductiveTypes numParams types fun stats =>
    AddInductive.declareInductiveTypes stats numParams types 0 isUnsafe

example (isUnsafe : Bool) :
    (AddInductive.declareInductiveTypes ordinaryStats 0 ordinaryTypes 0 isUnsafe
      (ordinaryContext isUnsafe)).WF fun env' =>
        ∃ venv', VEnv.empty.addInductHeaders ordinaryHeaders = some venv' ∧
          Aligned (if isUnsafe then .unsafe else .safe) env'.constants venv' ∧ venv'.Ordered := by
  apply AddInductive.declareInductiveTypes.ordered (ordinaryContext isUnsafe)
    ordinaryStats 0 ordinaryTypes 0 isUnsafe Aligned.empty VEnv.Ordered.empty
    DefinitionSafety.le_rfl rfl ?_ ?_
  · exact .cons ⟨rfl, rfl, .sort rfl⟩ (.cons ⟨rfl, rfl, .sort rfl⟩ .nil)
  · intro header hmem
    simp [ordinaryHeaders] at hmem
    rcases hmem with rfl | rfl <;> exact ⟨_, .sort trivial⟩

example (isUnsafe : Bool) :
    (checkedHeaders 0 ordinaryTypes isUnsafe (ordinaryContext isUnsafe)).WF fun env' =>
      ∃ venv', VEnv.empty.addInductHeaders ordinaryHeaders = some venv' ∧
        Aligned (if isUnsafe then .unsafe else .safe) env'.constants venv' ∧ venv'.Ordered := by
  apply AddInductive.checkInductiveTypes.orderedHeaders (ordinaryContext isUnsafe)
    0 ordinaryTypes 0 isUnsafe Aligned.empty VEnv.Ordered.empty DefinitionSafety.le_rfl
  · exact .cons ⟨rfl, rfl, .sort rfl⟩ (.cons ⟨rfl, rfl, .sort rfl⟩ .nil)
  · intro header hmem
    simp [ordinaryHeaders] at hmem
    rcases hmem with rfl | rfl <;> exact ⟨_, .sort trivial⟩

example (isUnsafe : Bool) :
    (checkedHeaders 0 #[] isUnsafe (ordinaryContext isUnsafe)).WF fun env' =>
      ∃ venv', VEnv.empty.addInductHeaders [] = some venv' ∧
        Aligned (if isUnsafe then .unsafe else .safe) env'.constants venv' ∧ venv'.Ordered :=
  AddInductive.checkInductiveTypes.orderedHeaders (ordinaryContext isUnsafe)
    0 #[] 0 isUnsafe Aligned.empty VEnv.Ordered.empty DefinitionSafety.le_rfl .nil (by simp)

example (ctx : AddInductive.Context) (numParams : Nat) (types : Array InductiveType)
    (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    {headers : List VInductiveType} (haligned : Aligned safety ctx.env.constants venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) types.toList headers) :
    (checkedHeaders numParams types isUnsafe ctx).WF fun env' =>
      ∃ venv', venv ≤ venv' ∧ venv'.defeqs = venv.defeqs ∧
        Aligned safety env'.constants venv' :=
  (AddInductive.checkInductiveTypes.refinesHeaders ctx numParams types 0 isUnsafe
    haligned hsafety hheaders).mono fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', VEnv.addInductHeaders.le hadd, VEnv.addInductHeaders.defeqs_eq hadd, haligned'⟩

private def audit (theoremName : Name) (allowed : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "{theoremName}: unexpected axiom {axiomName}"

private def checkExecutableHeader (imported : Kernel.Environment) (typeName : Name) : MetaM Unit := do
  let some (.inductInfo info) := imported.find? typeName | throwError "missing {typeName}"
  let ctors ← info.ctors.mapM fun name => do
    let some (.ctorInfo ctor) := imported.find? name | throwError "missing {name}"
    pure ({ name := ctor.name, type := ctor.type } : Constructor)
  let type : InductiveType := { name := info.name, type := info.type, ctors }
  let stats : AddInductive.InductiveStats := {
    levels := [], resultLevel := .succ .zero, nindices := #[0],
    indConsts := #[.const typeName []], params := #[], isNotZero := true }
  let ctx : AddInductive.Context := {
    env := Kernel.Environment.empty `InductiveHeadersTest,
    lparams := [], safety := .safe, allowPrimitive := true }
  for action in [AddInductive.declareInductiveTypes stats 0 #[type] 0 false,
      checkedHeaders 0 #[type] false] do
    let .ok result := action ctx | throwError "failed to stage {typeName}"
    let some (.inductInfo registered) := result.find? typeName | throwError "missing staged header"
    unless registered.levelParams.isEmpty && registered.numParams == 0 && registered.numIndices == 0 &&
        registered.type == type.type && registered.ctors == info.ctors && registered.all == [typeName] &&
        !registered.isUnsafe do
      throwError "incorrect staged metadata for {typeName}"
    for name in info.ctors do
      if result.contains name then throwError "header staging installed constructor {name}"
    if (action { ctx with env := imported }).isOk then throwError "accepted duplicate {typeName}"
    if (action { ctx with allowPrimitive := false }).isOk then
      throwError "accepted {typeName} without primitive authorization"

private def checkMutualHeaders (isUnsafe : Bool) : MetaM Unit := do
  let ctx := ordinaryContext isUnsafe
  for action in [fun types => AddInductive.declareInductiveTypes ordinaryStats 0 types 0 isUnsafe,
      fun types => checkedHeaders 0 types isUnsafe] do
    let .ok result := action ordinaryTypes ctx | throwError "failed to stage mutual headers"
    for type in ordinaryTypes do
      let some (.inductInfo info) := result.find? type.name | throwError "missing {type.name}"
      unless info.name == type.name && info.type == type.type && info.isUnsafe == isUnsafe &&
          info.levelParams.isEmpty && info.numParams == 0 && info.numIndices == 0 &&
          info.all == [`First, `Second] && info.ctors.isEmpty do
        throwError "incorrect mutual header metadata for {type.name}"
    if (action ordinaryTypes { ctx with env := result }).isOk then
      throwError "accepted a mutual-header collision"
    if (action #[ordinaryType `First, ordinaryType `First] ctx).isOk then
      throwError "accepted duplicate names in a mutual declaration"
  let shortStats := { ordinaryStats with nindices := #[0] }
  let .ok truncated := AddInductive.declareInductiveTypes shortStats 0 ordinaryTypes 0 isUnsafe ctx
    | throwError "unexpected rejection by the unchecked header prefix"
  unless truncated.contains `First && !truncated.contains `Second do
    throwError "statistics-length boundary changed; revisit the refinement precondition"

private def checkCheckedMetadata (ctx : AddInductive.Context) (numParams : Nat)
    (types : Array InductiveType) (indices : Array Nat) (isUnsafe : Bool) : MetaM Unit := do
  let .ok result := checkedHeaders numParams types isUnsafe ctx
    | throwError "failed to check and stage datatype headers"
  unless types.size == indices.size do throwError "invalid metadata fixture"
  for type in types, index in indices do
    let some (.inductInfo info) := result.find? type.name | throwError "missing {type.name}"
    unless info.name == type.name && info.type == type.type && info.levelParams == ctx.lparams &&
        info.numParams == numParams && info.numIndices == index && info.isUnsafe == isUnsafe &&
        info.all == types.toList.map (·.name) && info.ctors.isEmpty && info.numNested == 0 do
      throwError "incorrect checked header metadata"

private def checkCheckedFixtures (imported : Kernel.Environment) (isUnsafe : Bool) : MetaM Unit := do
  let ctx := { ordinaryContext isUnsafe with env := imported }
  let sortType : Expr := .sort (.succ .zero)
  let indexed (count : Nat) := count.fold
    (fun _ _ type => Expr.forallE `index (.const ``Nat []) type .default) sortType
  checkCheckedMetadata ctx 0
    #[{ ordinaryType `IndexedFirst with type := indexed 1 },
      { ordinaryType `IndexedSecond with type := indexed 2 }] #[1, 2] isUnsafe
  let polyCtx := { ctx with lparams := [`u] }
  let polyType : Expr := .forallE `A (.sort (.param `u))
    (.forallE `value (.bvar 0) (.sort (.param `u)) .default) .default
  checkCheckedMetadata polyCtx 1
    #[{ ordinaryType `PolyFirst with type := polyType },
      { ordinaryType `PolySecond with type := polyType }] #[1, 1] isUnsafe

private def checkCheckedRejections (imported : Kernel.Environment) : MetaM Unit := do
  let ctx := { ordinaryContext false with env := imported }
  let parameter (domain : Expr) := Expr.forallE `A domain (.sort (.succ .zero)) .default
  let cases : List (Nat × Array InductiveType × AddInductive.Context) := [
    (1, ordinaryTypes, ctx),
    (1, #[{ ordinaryType `First with type := parameter (.sort (.succ .zero)) },
      { ordinaryType `Second with type := parameter (.sort .zero) }], ctx),
    (0, #[ordinaryType `First, { ordinaryType `Second with type := .sort .zero }], ctx),
    (0, #[{ ordinaryType `UnknownUniverse with type := .sort (.param `u) }], ctx),
    (0, #[{ ordinaryType `InvalidType with type := .const `Missing [] }], ctx),
    (0, ordinaryTypes, { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } })]
  for (numParams, types, ctx) in cases do
    if (checkedHeaders numParams types false ctx).isOk then
      throwError "accepted invalid datatype types before header registration"

run_meta
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for theoremName in [``VEnv.addInductHeaders.le, ``VEnv.addInductHeaders.constants,
      ``VEnv.addInductHeaders.defeqs_eq, ``VEnv.addInductHeaders.ordered,
      ``VInductDecl.HeadersWF.mono, ``boolInductDecl.headersWF, ``natInductDecl.headersWF] do
    audit theoremName standard
  audit ``VEnv.addInductHeaders.wf (standard ++ [``sorryAx])
  audit ``Environment.PrimitiveInductiveDecl.toVDecl (standard ++ [``sorryAx])
  let translation := standard ++ [``sorryAx, ``Lean.Expr.eqv_eq,
    ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq]
  audit ``Environment.checkPrimitiveInductive.toVDecl translation
  audit ``TrInductiveType.header (standard ++ [``sorryAx])
  let registration := standard ++ [``sorryAx,
    ``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.toList'_insert, ``Lean.PersistentHashMap.WF.find?_eq]
  audit ``AddInductive.declareInductiveTypes.refines registration
  audit ``AddInductive.declareInductiveTypes.ordered registration
  audit ``AddInductive.checkInductiveTypes.refinesHeaders registration
  audit ``AddInductive.checkInductiveTypes.orderedHeaders registration
  let imported := (← Lean.getEnv).toKernelEnv
  for typeName in [``Bool, ``Nat] do
    checkExecutableHeader imported typeName
  for isUnsafe in [false, true] do
    checkMutualHeaders isUnsafe
    checkCheckedFixtures imported isUnsafe
  checkCheckedRejections imported

end InductiveHeadersTest
