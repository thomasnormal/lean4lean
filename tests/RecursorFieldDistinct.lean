import Lean4Lean.Verify.RecursorFieldDistinct
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace RecursorFieldDistinctTest

example {ctx : Context} {fields : Array Expr} (hfields : RecursorFieldsDeclared ctx.lctx fields)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    Expr.fvar ⟨ctx.ngen.curr⟩ ∉ fields.toList := hfields.fresh hwf hreserved

example {ctx : Context} {fields : Array Expr} (hfields : RecursorFieldsDeclared ctx.lctx fields)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (hnodup : fields.toList.Nodup) :
    (fields.push (.fvar ⟨ctx.ngen.curr⟩)).toList.Nodup := hfields.nodup_push hwf hreserved hnodup

example (stats : InductiveStats) (type : Expr) (next : Expr → Array Expr → Array Expr → M ResultType)
    (ctx : Context) (post : ResultType → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ result fields recursiveFields current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx fields → fields.toList.Nodup →
      recursiveFields.toList.Sublist fields.toList → (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post :=
  mkRecInfos.loopCtorArgs.distinct stats type next ctx post hwf hreserved hnext

example (stats : InductiveStats) (type : Expr) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecInfos.loopCtorArgs stats type (fun _ fields recursiveFields => pure (fields, recursiveFields)) ctx).WF
      fun result => result.1.toList.Nodup ∧ result.2.toList.Nodup := by
  exact mkRecInfos.loopCtorArgs.distinct stats type
    (fun _ fields recursiveFields => pure (fields, recursiveFields)) ctx
    (fun result => result.1.toList.Nodup ∧ result.2.toList.Nodup) hwf hreserved
    (fun _ _ _ _ _ _ hnodup hselected => .pure ⟨hnodup, hnodup.sublist hselected⟩)

example {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hdistinct : RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule := hdistinct.scope

example {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hdistinct : RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
      RecursorFieldsDeclared current.lctx fields ∧ fields.toList.Nodup ∧ recursiveFields.toList.Nodup ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor := hdistinct.selected

example {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hdistinct : RecursorRuleRhsDistinct stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsScope stats motives minors ctx ctors rules initial := hdistinct.scope

example {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hdistinct : RecursorRuleRhsDistinct stats motives minors ctx ctors rules initial)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minors[initial + index]! rule :=
  hdistinct.at index ctor hctor

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats) (parent : Nat)
    (motives minors : Array Expr) (initial : Nat) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsDistinct stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length :=
  mkRecRules.rhsDistinct types elimLevel stats parent motives minors initial ctx hwf hreserved

example {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : Kernel.Environment}
    (hdistinct : LocalRecursorRuleRhsDistinct stats types infos ctx env) :
    LocalRecursorRuleRhsScope stats types infos ctx env := hdistinct.scope

example {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {infos : Array RecInfo} {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) : LocalRecursorRuleRhsDistinct stats types infos ctx env :=
  hmetadata.localRuleRhsDistinct hcounts hwf hreserved

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsDistinct stats types result.2.1 result.2.2 result.1 :=
  mkRecInfos.registeredDistinct stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv

private def fieldStage (stats : InductiveStats) (type : Expr) : M (Array Expr × Array Expr × Context) :=
  mkRecInfos.loopCtorArgs stats type fun _ fields recursiveFields => do
    return (fields, recursiveFields, ← readThe Context)

private def checkDistinct (fields recursiveFields : Array Expr) : MetaM Unit := do
  unless fields.toList.eraseDups.length == fields.size &&
      recursiveFields.toList.eraseDups.length == recursiveFields.size do
    throwError "generated field vectors contain duplicate identities"
  unless recursiveFields.toList.isSublist fields.toList do
    throwError "recursive fields lost their ordered selection"

private def checkStage (ctx : Context) (stats : InductiveStats) (type : Expr)
    (expectedFields expectedRecursive : Nat) : MetaM Unit := do
  let .ok (fields, recursiveFields, current) := fieldStage stats type ctx
    | throwError "distinct-field traversal failed"
  unless fields.size == expectedFields && recursiveFields.size == expectedRecursive do
    throwError "incorrect distinct-field counts: expected {expectedFields}/{expectedRecursive}, \
      got {fields.size}/{recursiveFields.size} for {type}"
  checkDistinct fields recursiveFields
  for index in [:fields.size] do
    let field := fields[index]!
    unless field == .fvar ⟨.num ctx.ngen.namePrefix (ctx.ngen.idx + index)⟩ do
      throwError "field identity does not match chronological fresh allocation"
    let some decl := current.lctx.find? field.fvarId! | throwError "distinct field is undeclared"
    unless decl.toExpr == field && decl.userName == `field &&
        (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "field declaration shape or repeated binder label changed"
  unless current.ngen.idx == ctx.ngen.idx + fields.size &&
      current.lctx.numIndices == ctx.lctx.numIndices + fields.size do
    throwError "incorrect distinct-field context advancement"

private def fixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let stats := { (default : InductiveStats) with indConsts := #[natType], nindices := #[0] }
  let one := Expr.forallE `field natType natType .default
  let higher := Expr.forallE `argument natType natType .default
  let mixed := Expr.forallE `field boolType (.forallE `field higher one .instImplicit) .strictImplicit
  let dependent := Expr.forallE `field (.sort (.succ .zero))
    (.forallE `field (.bvar 0) natType .implicit) .default
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .implicit) natType
  let seeded := { ctx with
    ngen := { namePrefix := `DistinctSeed, idx := 41 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `DistinctSeed 40⟩ `old boolType .default }
  for current in [ctx, seeded] do
    checkStage current stats natType 0 0
    checkStage current stats one 1 1
    checkStage current stats mixed 3 2
    checkStage current stats dependent 2 0
    checkStage current stats many 33 33
  let params := { stats with params := #[.fvar ⟨`Parameter⟩] }
  checkStage ctx params (.forallE `parameter (.sort (.succ .zero)) one .default) 1 0
  let exposing := { stats with params := #[one] }
  checkStage ctx exposing (.forallE `parameter (.sort (.succ .zero)) (.bvar 0) .default) 1 0
  logInfo "twelve distinct-field fixtures passed repeated names, selection, and fresh identities"

private def replayRules (ctx : Context) (stats : InductiveStats) (types : Array InductiveType)
    (minors : Array Expr) (initial : Nat) : MetaM Unit := do
  let .ok (rules, finalIndex) := mkRecRules types (.succ .zero) stats 0 #[] minors initial ctx
    | throwError "distinct-field rule generation failed"
  unless rules.length == types[0]!.ctors.length && finalIndex == initial + rules.length do
    throwError "incorrect distinct-rule state or count"
  for (ctor, index) in types[0]!.ctors.zipIdx do
    let .ok (fields, recursiveFields, current) := fieldStage stats ctor.type ctx
      | throwError "distinct-field replay traversal failed"
    checkDistinct fields recursiveFields
    let replay := mkRecRules.loopU types stats #[] minors [] recursiveFields 0 #[] fun values =>
      pure (({
        ctor := ctor.name
        nfields := fields.size
        rhs := recursorRuleRhs stats #[] minors fields values current.lctx minors[initial + index]! } : RecursorRule),
        values.size)
    let .ok (expected, count) := replay current | throwError "distinct RHS replay failed"
    let some rule := rules[index]? | throwError "missing distinct RHS rule"
    unless rule.ctor == ctor.name && rule.nfields == fields.size && rule.rhs == expected.rhs &&
        count == recursiveFields.size do
      throwError "distinct field witnesses do not replay the coupled RHS recipe"

private def ruleFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let one := Expr.forallE `field natType natType .default
  let two := Expr.forallE `field natType one .implicit
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .implicit) natType
  let ctors : List Constructor := [
    { name := `DistinctRules.empty, type := natType },
    { name := `DistinctRules.one, type := one },
    { name := `DistinctRules.two, type := two },
    { name := `DistinctRules.many, type := many }]
  let types : Array InductiveType := #[{ name := ``Nat, type := .sort (.succ .zero), ctors }]
  let stats := { (default : InductiveStats) with indConsts := #[natType], nindices := #[0] }
  let minors := (List.range 6).toArray.map fun index => Expr.fvar ⟨.num `DistinctMinor index⟩
  let lctx := minors.foldl (fun current minor =>
    current.mkLocalDecl minor.fvarId! `minor natType .default) ctx.lctx
  replayRules { ctx with lctx } stats types minors 0
  replayRules { ctx with lctx, ngen := { namePrefix := `DistinctReplay, idx := 17 } } stats types minors 2
  logInfo "eight RHS replays passed distinct fields, selected fields, exact recipes, and shifted offsets"

private def boundaries (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let field := Expr.fvar ⟨`DuplicateFixture⟩
  let declared := ctx.lctx.mkLocalDecl field.fvarId! `field natType .default
  let duplicate := #[field, field]
  for candidate in duplicate do
    unless (declared.find? candidate.fvarId!).isSome do throwError "missing duplicate-field control declaration"
  unless duplicate.toList.eraseDups.length != duplicate.size do
    throwError "declaration membership alone must not imply distinctness"
  let two := Expr.forallE `field natType (.forallE `field natType natType .default) .default
  let .error .deepRecursion := fieldStage default two
      { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "distinct traversal lost zero-fuel rejection"
  let .error .deepRecursion := fieldStage default two
      { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } }
    | throwError "distinct traversal lost partial-allocation failure"
  logInfo "declared-duplicate control and two fuel failures passed"

private def audit (theoremName : Name) (interfaces := false) (registration := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if interfaces then [
    ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert,
    ``Lean.PersistentArray.toList'_push] else []
  let allowed := allowed ++ if registration then [``Lean.PersistentHashMap.findAux_isSome] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  audit ``RecursorFieldsDeclared.fresh true
  audit ``RecursorFieldsDeclared.nodup_push true
  audit ``mkRecInfos.loopCtorArgs.distinct true
  audit ``RecursorRuleRhsDistinctReceipt.scope
  audit ``RecursorRuleRhsDistinctReceipt.selected
  audit ``RecursorRuleRhsDistinct.scope
  audit ``RecursorRuleRhsDistinct.at
  audit ``mkRecRules.rhsDistinct true
  audit ``LocalRecursorRuleRhsDistinct.scope
  audit ``InductiveStats.RecursorOffsetMetadata.localRuleRhsDistinct true
  audit ``mkRecInfos.registeredDistinct true true
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  fixtures ctx
  ruleFixtures ctx
  boundaries ctx

end RecursorFieldDistinctTest
