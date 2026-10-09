import Lean4Lean.Verify.InductiveIndexAlignment
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace InductiveIndexAlignmentTest

abbrev CarrierAlias := Nat
abbrev HiddenIndex := Nat → Type

example (level : Level) : SortTelescope (.sort level) := .sort level

example (name : Name) (domain : Expr) (bi : BinderInfo) (level : Level) :
    SortTelescope (.forallE name domain (.sort level) bi) := .forallE name domain bi (.sort level)

example {type : Expr} (htype : SortTelescope type) (param : Expr) (depth : Nat) :
    SortTelescope (type.instantiate1' param depth) := htype.instantiate1' param depth

example {type : Expr} (htype : SortTelescope type) (param : Expr) :
    SortTelescope (type.instantiate1 param) := htype.instantiate1 param

example {type : Expr} (htype : SortTelescope type) (param : Expr) (depth index : Nat) :
    declareConstructors.arity index (type.instantiate1' param depth) = declareConstructors.arity index type :=
  htype.arity_instantiate1' param depth index

example {type : Expr} (htype : SortTelescope type) (param : Expr) :
    declareConstructors.arity 0 (type.instantiate1 param) = declareConstructors.arity 0 type :=
  htype.arity_instantiate1 param

example {type : Expr} (htype : SortTelescope type) (first second : Expr) :
    declareConstructors.arity 0 (type.instantiate1 first) = declareConstructors.arity 0 (type.instantiate1 second) :=
  (htype.arity_instantiate1 first).trans (htype.arity_instantiate1 second).symm

example {type : Expr} (htype : SortTelescope type)
    (hnot : ∀ name domain body bi, type ≠ .forallE name domain body bi) :
    ∃ level, type = .sort level := htype.nonForall hnot

example {type : Expr} (htype : SortTelescope type) (ctx : Context) :
    ((monadLift (TypeChecker.whnf type) : M Expr) ctx).WF fun result => result = type := htype.whnf ctx

example {type : Expr} (htype : SortTelescope type) (first second : Context) (left right : Expr)
    (hleft : ((monadLift (TypeChecker.whnf type) : M Expr) first) = .ok left)
    (hright : ((monadLift (TypeChecker.whnf type) : M Expr) second) = .ok right) : left = right :=
  (htype.whnf first left hleft).trans (htype.whnf second right hright).symm

example {body : Expr} (htype : SortTelescope body) (name : Name) (domain : Expr) (bi : BinderInfo)
    (param : Expr) (ctx : Context) :
    ((monadLift (TypeChecker.whnf (body.instantiate1 param)) : M Expr) ctx).WF fun result =>
      SortTelescope result ∧ declareConstructors.arity 0 (.forallE name domain body bi) =
        1 + declareConstructors.arity 0 result := htype.whnfStep name domain bi param ctx

example {nparams : Nat} {stats finalStats : InductiveStats} {type terminal : Expr}
    {index nindices finalIndices : Nat} {ctx finalCtx : Context}
    (trace : CheckedHeaderTrace nparams stats type index nindices ctx terminal finalStats finalIndices finalCtx)
    (htype : SortTelescope type) : index + nindices + declareConstructors.arity 0 type = nparams + finalIndices :=
  trace.telescopeCount htype

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hindex : index ≤ stats.params.size) :
    finalIndex = min (index + declareConstructors.arity 0 type) stats.params.size ∧
      finalIndex + finalIndices.size = index + indices.size + declareConstructors.arity 0 type :=
  trace.telescopeCounts htype hindex

example {stats : InductiveStats} {type terminal : Expr} {index finalIndex : Nat}
    {indices finalIndices : Array Expr} {ctx finalCtx : Context}
    (trace : RecursorIndexTrace stats type index indices ctx terminal finalIndex finalIndices finalCtx)
    (htype : SortTelescope type) (hindex : index ≤ stats.params.size)
    (hbound : stats.params.size ≤ index + declareConstructors.arity 0 type) : finalIndex = stats.params.size := by
  have hposition := (trace.telescopeCounts htype hindex).1
  simpa [Nat.min_eq_right hbound] using hposition

example {nparams parent count : Nat} {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (htype : SortTelescope types[parent]!.type) : declareConstructors.arity 0 types[parent]!.type = params.size + count :=
  source.telescopeCount htype

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level} {parent count : Nat}
    {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (htype : SortTelescope types[parent]!.type)
    (hcount : declareConstructors.arity 0 types[parent]!.type = stats.params.size + count) : info.indices.size = count :=
  source.telescopeIndexCount htype hcount

example {nparams : Nat} {types : Array InductiveType} {stats : InductiveStats}
    {original checkedRoot recursorRoot current : Context} {elimLevel : Level} {infos : Array RecInfo}
    (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (sources : RecursorInfoIndexSources stats types elimLevel recursorRoot infos current)
    (htypes : TelescopeHeaders types) : RecursorIndexCounts stats types infos :=
  headers.telescopeIndexCounts sources htypes

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M α) (original checkedRoot ctx : Context) (post : α → Prop)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ infos current, ctx.RecursorScopeFrame current →
      RecursorInfoIndexSources stats types elimLevel ctx infos current → RecursorIndexCounts stats types infos →
      (next infos current).WF post) : (mkRecInfos stats types elimLevel next ctx).WF post :=
  mkRecInfos.scopedAlignedIndices nparams stats types elimLevel next original checkedRoot ctx post headers htypes hwf hreserved hnext

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (original checkedRoot ctx : Context) (headers : CheckedHeaderSources nparams types original stats checkedRoot)
    (htypes : TelescopeHeaders types) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos stats types elimLevel (fun infos => do return (infos, ← readThe Context)) ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      RecursorInfoIndexSources stats types elimLevel ctx result.1 result.2 ∧ RecursorIndexCounts stats types result.1 :=
  mkRecInfos.getAlignedIndices nparams stats types elimLevel original checkedRoot ctx headers htypes hwf hreserved

example (nparams : Nat) (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (original checkedRoot ctx : Context)
    (headers : CheckedHeaderSources nparams types original stats checkedRoot) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      RecursorIndexCounts stats types result.2.1 := by
  intro result hresult
  exact (mkRecInfos.registeredAlignedIndices nparams stats types elimLevel lparams isK isUnsafe
    original checkedRoot ctx headers htypes hwf hreserved henv result hresult).2.2.2.2.2.2.2

example (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (ctx : Context) (htypes : TelescopeHeaders types)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        withEnv (← declareConstructors stats types false) do
          let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK false
          return (stats, result)) ctx).WF fun result => RecursorIndexCounts result.1 types result.2.2.1 :=
  checkInductiveTypes.safeRegisteredIndexCounts nparams types numNested elimLevel lparams isK ctx htypes hwf hreserved

example {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    (counts : RecursorIndexCounts stats types infos) (parent : Nat) (hparent : parent < types.size)
    (hwrong : infos[parent]!.indices.size ≠ stats.nindices[parent]!) : False := hwrong (counts.2 parent hparent)

example {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    (counts : RecursorIndexCounts stats types infos) (hwrong : infos.size ≠ types.size) : False := hwrong counts.1

example (name : Name) (levels : List Level) (htype : SortTelescope (.const name levels)) : False := by cases htype

example (id : FVarId) (htype : SortTelescope (.fvar id)) : False := by cases htype

example (type : Expr) (htype : SortTelescope (.mdata {} type)) : False := by cases htype

example (name : Name) (domain : Expr) (bi : BinderInfo) (sourceName : Name) (levels : List Level)
    (htype : SortTelescope (.forallE name domain (.const sourceName levels) bi)) : False := by
  cases htype with
  | forallE _ _ _ tail => cases tail

private def sortType : Expr := .sort (.succ .zero)

private def indexed (count : Nat) : Expr :=
  (List.range count).foldr (fun _ body => .forallE `index (.const ``Nat []) body .implicit) sortType

private def header (name : Name) (type : Expr := sortType) : InductiveType := { name, type, ctors := [] }

private def stage (nparams : Nat) (types : Array InductiveType) (isK : Bool) :
    M (InductiveStats × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero) (← readThe Context).lparams isK false
        return (stats, result)

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) (isK := false) : MetaM Unit := do
  let .ok (stats, env, infos, source) := stage nparams types isK ctx | throwError "safe index-alignment prefix failed"
  unless stats.nindices == expected && infos.size == types.size do throwError "alignment fixture lost checked counts"
  for parent in [:types.size] do
    let info := infos[parent]!
    unless info.indices.size == stats.nindices[parent]! &&
        declareConstructors.arity 0 types[parent]!.type == stats.params.size + info.indices.size do
      throwError "stable telescope checked/generated index-count equality failed"
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "aligned recursor was not registered"
    unless recursor.numIndices == info.indices.size && recursor.numParams == stats.params.size && recursor.k == isK do
      throwError "registered recursor index/parameter/K metadata changed"
    for index in info.indices do
      unless index.isFVar && (source.lctx.find? index.fvarId!).isSome do
        throwError "aligned index lost its actual source declaration"
  for decl in ctx.lctx do
    let some retained := source.lctx.find? decl.fvarId | throwError "index alignment dropped an old local"
    unless retained.toExpr == decl.toExpr && retained.type == decl.type do throwError "index alignment changed an old local"

private def fixtures (ctx : Context) : MetaM Unit := do
  let dependent := Expr.forallE `carrier sortType (.forallE `index (.bvar 0) sortType .strictImplicit) .default
  let three := Expr.forallE `carrier sortType (.forallE `first (.bvar 0)
    (.forallE `second (.bvar 1) sortType .implicit) .default) .instImplicit
  let seeded := { ctx with
    ngen := { namePrefix := `AlignmentSeed, idx := 31 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `AlignmentSeed 30⟩ `old (.const ``Bool []) .implicit }
  for original in [ctx, seeded] do
    checkFixture original 0 #[] #[]
    checkFixture original 0 #[header `AlignZero] #[0]
    checkFixture original 0 #[header `AlignFirst (indexed 1), header `AlignSecond (indexed 3)] #[1, 3]
    checkFixture original 1 #[header `AlignFirst dependent, header `AlignSecond three] #[1, 2]
    checkFixture original 2 #[header `AlignFirst three, header `AlignSecond three] #[1, 1]
    checkFixture original 3 #[header `AlignFirst three] #[0]
    let natDomain := Expr.forallE `parameter (.const ``Nat []) (indexed 1) .default
    let aliasDomain := Expr.forallE `renamed (.const ``CarrierAlias []) (indexed 2) .strictImplicit
    checkFixture original 1 #[header `AlignFirst natDomain, header `AlignSecond aliasDomain] #[1, 2]
    checkFixture { original with lparams := [`u] } 1 #[header `AlignPoly
      (.forallE `carrier (.sort (.param `u)) (.sort (.param `u)) .default)] #[0]
    checkFixture { original with fuel := { original.fuel with inductiveFuel := 3 } }
      1 #[header `AlignExactFuel dependent] #[1]
    checkFixture original 0 #[header `AlignK] #[0] true
    let node := Expr.const `AlignNode []
    checkFixture original 0 #[{ (header `AlignNode) with ctors := [
      { name := `AlignNode.base, type := node },
      { name := `AlignNode.step, type := .forallE `field node node .default }] }] #[0]
  logInfo "twenty-two safe telescope prefixes and registrations passed checked/generated/registered index counts across different readers and environments"

private def boundaries (ctx : Context) : MetaM Unit := do
  let types := #[header `AlignWrong (indexed 2)]
  let .ok (stats, _, infos, source) := stage 0 types false ctx | throwError "unchecked-count boundary setup failed"
  let inconsistent := { stats with nindices := #[99] }
  let .ok wrong := mkRecInfos inconsistent types (.succ .zero) pure source
    | throwError "bare generator changed unchecked-statistics behavior"
  unless wrong[0]!.indices.size == 2 && inconsistent.nindices[0]! == 99 do
    throwError "stored count equality must require real checked-header receipts"
  let incomplete := { (default : InductiveStats) with params := #[.fvar ⟨`MissingParameter⟩] }
  let .ok #[] := mkRecInfos.loopArgs1 incomplete sortType 0 #[] 1 pure ctx
    | throwError "terminal recursor helper must not imply complete parameter consumption"
  let .error .deepRecursion := stage 0 types false { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    | throwError "partial checked telescope fuel diagnostic changed"
  let .error .deepRecursion := mkRecInfos stats types (.succ .zero) pure
      { source with fuel := { source.fuel with inductiveFuel := 2 } }
    | throwError "partial recursor telescope fuel diagnostic changed"
  unless infos[0]!.indices.size == 2 do throwError "boundary setup lost its valid count"
  logInfo "four unchecked-count, incomplete-parameter and partial checked/generated fuel boundaries passed"

private def aliasBoundary (ctx : Context) : MetaM Unit := do
  let types : Array InductiveType := #[{
    name := `AlignHidden
    type := .const ``HiddenIndex []
    ctors := [] }]
  let .ok (stats, _, infos, _) := stage 0 types false ctx | throwError "hidden-header alias boundary failed"
  unless declareConstructors.arity 0 types[0]!.type == 0 && stats.nindices[0]! == 1 && infos[0]!.indices.size == 1 do
    throwError "hidden-header raw/normalized gap changed"
  logInfo "hidden header alias still succeeds with a strict raw/normalized gap but remains outside the explicit-telescope theorem"

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := binding ++ [``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert]
  let registration := scope ++ [``Lean.PersistentHashMap.findAux_isSome]
  audit ``SortTelescope.instantiate1'
  audit ``SortTelescope.instantiate1 binding
  audit ``SortTelescope.arity_instantiate1'
  audit ``SortTelescope.arity_instantiate1 binding
  audit ``SortTelescope.nonForall
  audit ``SortTelescope.whnf
  audit ``SortTelescope.whnfStep binding
  audit ``CheckedHeaderTrace.telescopeCount binding
  audit ``RecursorIndexTrace.telescopeCounts binding
  audit ``CheckedHeaderSource.telescopeCount binding
  audit ``RecursorInfoIndexSource.telescopeIndexCount binding
  audit ``CheckedHeaderSources.telescopeIndexCounts binding
  audit ``mkRecInfos.scopedAlignedIndices scope
  audit ``mkRecInfos.getAlignedIndices scope
  audit ``mkRecInfos.registeredAlignedIndices registration
  audit ``checkInductiveTypes.safeRegisteredIndexCounts scope
  let ctx : Context := { env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  boundaries ctx
  aliasBoundary ctx

end InductiveIndexAlignmentTest
