import Lean4Lean.Verify.InductiveParamReconstruction
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.ElimNestedInductive

namespace InductiveParamReconstructionTest

theorem reservedNoFVars (type : Expr) (ngen : NameGenerator) (hfvars : type.hasFVar = false) :
    SourceReserved type ngen := SourceReserved.noFVars type ngen hfvars

theorem currentFresh (type : Expr) (ngen : NameGenerator) (hreserved : SourceReserved type ngen) :
    ⟨ngen.curr⟩ ∉ type.fvarsList := hreserved.current_fresh

theorem nextReserved (body : Expr) (ngen : NameGenerator) (hreserved : SourceReserved body ngen) :
    SourceReserved (body.instantiate1 (.fvar ⟨ngen.curr⟩)) ngen.next :=
  hreserved.instantiate1_current

theorem freshInverse (body : Expr) (id : FVarId) (depth : Nat) (hfresh : id ∉ body.fvarsList) :
    (body.instantiate1' (.fvar id) depth).abstract1 id depth = body :=
  abstract_instantiate1_fresh body id depth hfresh

theorem scopeFromValidity (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hscope : ContextNoLooseBVars lctx) :
    lctx.BindingScope := hvalid.bindingScope hscope

theorem nativeFold (numParams : Nat) (lctx : LocalContext) (params : Array Expr)
    (hvalid : ParamValidity numParams lctx params) (hscope : ContextNoLooseBVars lctx)
    (body : Expr) (hbody : body.looseBVarRange' = 0) :
    lctx.mkForall params body = reconstructParams lctx.toList body :=
  hvalid.mkForall_reconstruct hscope body hbody

theorem structuralExtraction (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Kernel.Environment) (state : State) (post : ResultType × State → Prop)
    (hreserved : SourceReserved type state.ngen)
    (hnext : ∀ lctx remainder params state', reconstructParams lctx.toList remainder = type →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.reconstruct type numParams next env state post hreserved hnext

theorem sourceRoundtrip (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (hscope : type.looseBVarRange' = 0) (hreserved : SourceReserved type state.ngen) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.mkForall result.1.2.2 result.1.2.1 = type :=
  withParams.getReconstruction type numParams env state hscope hreserved

theorem noFVarsRoundtrip (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (hscope : type.looseBVarRange' = 0) (hfvars : type.hasFVar = false) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.mkForall result.1.2.2 result.1.2.1 = type :=
  withParams.getReconstruction_noFVars type numParams env state hscope hfvars

theorem sourceContinuation (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M ResultType)
    (env : Kernel.Environment) (state : State) (post : ResultType × State → Prop)
    (hscope : type.looseBVarRange' = 0) (hreserved : SourceReserved type state.ngen)
    (hnext : ∀ lctx remainder params state', lctx.mkForall params remainder = type →
      (next lctx remainder params env state').WF post) :
    (withParams type numParams next env state).WF post :=
  withParams.sourceReconstruction type numParams next env state post hscope hreserved hnext

theorem directRoundtrip (type : Expr) (numParams : Nat) (env : Kernel.Environment) (state : State)
    (hscope : type.looseBVarRange' = 0) (hreserved : SourceReserved type state.ngen) :
    (withParams type numParams (fun lctx remainder params => pure (lctx.mkForall params remainder))
      env state).WF fun result => result.1 = type :=
  withParams.mkForall_source type numParams env state hscope hreserved

theorem metavariableReserved (id : MVarId) (ngen : NameGenerator) :
    SourceReserved (.mvar id) ngen := by simp [SourceReserved, Expr.fvarsList]

theorem priorIdReserved (ngen : NameGenerator) :
    SourceReserved (.fvar ⟨ngen.curr⟩) ngen.next := by
  intro fvar hmem
  simp only [Expr.fvarsList, List.mem_singleton] at hmem
  exact hmem ▸ NameGenerator.next_reserves_self

theorem currentCaptureNotReserved (ngen : NameGenerator) :
    ¬ SourceReserved (.fvar ⟨ngen.curr⟩) ngen := by
  intro hreserved
  exact hreserved.current_fresh (by simp [Expr.fvarsList])

theorem futureCaptureNotReserved (ngen : NameGenerator) :
    ¬ SourceReserved (.fvar ⟨ngen.next.curr⟩) ngen := by
  intro hreserved
  exact NameGenerator.not_reserves_self
    (NameGenerator.Reserves.mono .next (hreserved _ (by simp [Expr.fvarsList])))

theorem zeroMetavariableRoundtrip (id : MVarId) (env : Kernel.Environment) (state : State) :
    (withParams (.mvar id) 0 (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => result.1.1.mkForall result.1.2.2 result.1.2.1 = .mvar id :=
  withParams.getReconstruction (.mvar id) 0 env state rfl (metavariableReserved id state.ngen)

private def parameterBinders (numParams : Nat) (externalDomains : Bool)
    (external : FVarId) (body : Expr) : Expr :=
  (List.range numParams).foldr (fun index result =>
    let base := if index = 0 then Expr.sort (.succ .zero) else .bvar (index - 1)
    let domain := if externalDomains then mkApp (.fvar external) base else base
    let name := if index % 2 = 0 then Name.anonymous else `repeated
    let bi := match index % 4 with
      | 0 => BinderInfo.implicit
      | 1 => .strictImplicit
      | 2 => .instImplicit
      | _ => .default
    Expr.forallE name domain result bi) body

private def parameterApp (numParams offset : Nat) : Expr :=
  mkAppN (.const `SourceFamily []) ((List.range numParams).map fun index =>
    Expr.bvar (numParams - 1 - index + offset)).toArray

private def sourceTails (numParams : Nat) (external : FVarId) : List Expr :=
  let sortType := Expr.sort (.succ .zero)
  let dependent := parameterApp numParams 0
  let domain := if numParams = 0 then sortType else .bvar (numParams - 1)
  [sortType, .forallE `extra domain (parameterApp numParams 1) .instImplicit,
    .lam `extra domain (parameterApp numParams 1) .strictImplicit,
    .letE `extra domain dependent (parameterApp numParams 1) false,
    .letE `extra domain dependent (parameterApp numParams 1) true,
    .mdata {} dependent, .proj `SourcePair 0 dependent,
    mkApp (.fvar external) dependent, .mvar ⟨`Unassigned⟩, .fvar external,
    .lit (.natVal 37), .lit (.strVal "source"), .sort (.mvar ⟨`UnassignedLevel⟩)]

private def reservedFlag (ngen : NameGenerator) (id : FVarId) : Bool :=
  match id.name with
  | .num namePrefix index => namePrefix != ngen.namePrefix || index < ngen.idx
  | _ => true

private def checkExtraction (env : Kernel.Environment) (state : State)
    (numParams : Nat) (type : Expr) : MetaM Unit := do
  unless type.looseBVarRange' == 0 && type.fvarsList.all (reservedFlag state.ngen) do
    throwError "reconstruction fixture violates scope/freshness premises"
  match withParams type numParams
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "unexpected source reconstruction extraction failure"
  | .ok ((lctx, remainder, params), _) =>
    unless params.size == numParams && lctx.mkForall params remainder == type do
      throwError "native re-abstraction did not reconstruct the source"
    let decls := (lctx.decls.toList.filterMap id).reverse
    unless reconstructParams decls remainder == type do
      throwError "sequential reconstruction did not reconstruct the source"
    match withParams type numParams
        (fun lctx remainder params => pure (lctx.mkForall params remainder)) env state with
    | .ok (rebound, _) =>
      unless rebound == type do
        throwError "direct re-abstraction callback did not reconstruct the source"
    | .error _ => throwError "direct re-abstraction callback unexpectedly failed"

private def checkCapture (env : Kernel.Environment) (state : State)
    (captureDomain future : Bool) : MetaM Unit := do
  let id : FVarId := ⟨if future then state.ngen.next.curr else state.ngen.curr⟩
  let sortType := Expr.sort (.succ .zero)
  let type := if captureDomain then
    .forallE `outer sortType
      (.forallE `middle sortType (.forallE `inner (.fvar id) sortType .implicit) .default) .default
    else parameterBinders 3 false ⟨`OutsideSource⟩ (.fvar id)
  unless type.looseBVarRange' == 0 && !type.fvarsList.all (reservedFlag state.ngen) do
    throwError "source-capture fixture failed to isolate the freshness premise"
  match withParams type 3
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "source-capture helper boundary unexpectedly rejects extraction"
  | .ok ((lctx, remainder, params), _) =>
    unless lctx.mkForall params remainder != type do
      throwError "missing source freshness failed to expose capture"

private def checkLooseSource (env : Kernel.Environment) (state : State)
    (looseDomain : Bool) : MetaM Unit := do
  let sortType := Expr.sort (.succ .zero)
  let type := if looseDomain then
    .forallE `outer sortType (.forallE `inner (.bvar 1) sortType .implicit) .default
    else parameterBinders 2 false ⟨`OutsideSource⟩ (.bvar 2)
  unless type.looseBVarRange' != 0 && type.fvarsList.isEmpty do
    throwError "loose-source fixture failed to isolate the scope premise"
  match withParams type 2
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error _ => throwError "loose-source helper boundary unexpectedly rejects extraction"
  | .ok ((lctx, remainder, params), _) =>
    let decls := (lctx.decls.toList.filterMap id).reverse
    unless lctx.mkForall params remainder != type && reconstructParams decls remainder == type do
      throwError "scope boundary failed to distinguish native from sequential reconstruction"

private def checkRejection (env : Kernel.Environment) (state : State) : MetaM Unit := do
  match withParams (.sort (.succ .zero)) 1
      (fun lctx remainder params => pure (lctx, remainder, params)) env state with
  | .error (.other message) =>
    unless message == "invalid inductive datatype declaration, incorrect number of parameters" do
      throwError "parameter shortage changed its diagnostic"
  | _ => throwError "parameter shortage did not reject extraction"

private def audit (theoremName : Name) (interfaces : List Name) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  for theoremName in [``SourceReserved.current_fresh, ``instantiate1_fvar_mem,
      ``abstract_instantiate1_fresh, ``metavariableReserved, ``priorIdReserved,
      ``currentCaptureNotReserved, ``futureCaptureNotReserved] do
    audit theoremName []
  audit ``SourceReserved.noFVars [``Expr.hasFVar_eq]
  for theoremName in [``SourceReserved.instantiate1_current, ``withParams.reconstruct] do
    audit theoremName [``Expr.instantiate1_eq, ``PersistentArray.toList'_push]
  let maps := [``PersistentHashMap.WF.find?_eq, ``PersistentHashMap.WF.toList'_insert,
    ``PersistentArray.toList'_push]
  audit ``ParamValidity.bindingScope maps
  let binding := [``Expr.abstractRange_eq, ``Expr.abstract_eq,
    ``Expr.hasLooseBVar_eq, ``Expr.lowerLooseBVars_eq]
  audit ``ParamValidity.mkForall_reconstruct (maps ++ binding)
  for theoremName in [``withParams.getReconstruction, ``withParams.sourceReconstruction,
      ``withParams.mkForall_source] do
    audit theoremName (``Expr.instantiate1_eq :: maps ++ binding)
  audit ``withParams.getReconstruction_noFVars
    (``Expr.hasFVar_eq :: ``Expr.instantiate1_eq :: maps ++ binding)
  let env := (← Lean.getEnv).toKernelEnv
  let states : List State := [
    { lvls := [], newTypes := #[] },
    { ngen := { namePrefix := `SourceSeed, idx := 17 }, lvls := [.param `u], nextIdx := 7,
      nestedAux := #[(.const ``Nat [], `StoredAux)],
      newTypes := #[{ name := `ExistingHeader, type := .sort (.succ .zero), ctors := [] }] },
    { ngen := { namePrefix := .anonymous, idx := 1048576 }, lvls := [], newTypes := #[] }]
  for state in states do
    let external : FVarId := if state.ngen.idx = 0 then ⟨`OutsideSource⟩
      else ⟨Name.mkNum state.ngen.namePrefix (state.ngen.idx - 1)⟩
    for numParams in [0, 1, 2, 3, 31, 32, 33, 65] do
      for externalDomains in [false, true] do
        for tail in sourceTails numParams external do
          checkExtraction env state numParams (parameterBinders numParams externalDomains external tail)
    for captureDomain in [false, true] do
      for future in [false, true] do
        checkCapture env state captureDomain future
    for looseDomain in [false, true] do
      checkLooseSource env state looseDomain
    checkRejection env state
  logInfo "checked 624 source round trips, 12 source-capture boundaries, 6 loose-source boundaries, and 3 rejections"

end InductiveParamReconstructionTest
