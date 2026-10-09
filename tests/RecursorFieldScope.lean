import Lean4Lean.Verify.RecursorFieldScope
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved)

namespace RecursorFieldScopeTest

example (ngen : NameGenerator) : ContextReserved {} ngen := ContextReserved.empty ngen

example {lctx : LocalContext} (hwf : lctx.WF) {decl : LocalDecl} (hdecl : decl ∈ lctx.toList) :
    lctx.find? decl.fvarId = some decl := hwf.find?_of_mem hdecl

example (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    ctx.RecursorScopeFrame ctx := .refl ctx hwf hreserved

example (ctx : Context) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (name : Name) (bi : BinderInfo) (domain : Expr) :
    ctx.RecursorScopeFrame { ctx with
      ngen := ctx.ngen.next
      lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name domain bi } :=
  Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain

example {original middle current : Context} (hfirst : original.RecursorScopeFrame middle)
    (hsecond : middle.RecursorScopeFrame current) : original.RecursorScopeFrame current :=
  hfirst.trans hsecond

example {original current : Context} (hframe : original.RecursorScopeFrame current)
    (hwf : original.lctx.WF) {fvar : FVarId} {decl : LocalDecl}
    (hlookup : original.lctx.find? fvar = some decl) : current.lctx.find? fvar = some decl :=
  hframe.oldLookup hwf hlookup

example {lctx : LocalContext} {fields : Array Expr} (hfields : RecursorFieldsDeclared lctx fields) :
    RecursorFieldsAreFVars fields := hfields.fvars

example {lctx : LocalContext} {fields selected : Array Expr}
    (hfields : RecursorFieldsDeclared lctx fields) (hselected : selected.toList.Sublist fields.toList) :
    RecursorFieldsDeclared lctx selected := hfields.sublist hselected

example {lctx : LocalContext} {fields : Array Expr} (hfields : RecursorFieldsDeclared lctx fields)
    (fvar : FVarId) (name : Name) (domain : Expr) (bi : BinderInfo) :
    RecursorFieldsDeclared (lctx.mkLocalDecl fvar name domain bi) (fields.push (.fvar fvar)) :=
  hfields.push fvar name domain bi

example {lctx : LocalContext} {fields : Array Expr} (hfields : RecursorFieldsDeclared lctx fields)
    (hwf : lctx.WF) : ∀ field ∈ fields, ∃ decl, lctx.find? decl.fvarId = some decl ∧
      decl.toExpr = field ∧ decl.value? (allowNondep := true) = none ∧ decl.kind = .default :=
  hfields.lookup hwf

example (stats : InductiveStats) (type : Expr) (next : Expr → Array Expr → Array Expr → M α)
    (ctx : Context) (post : α → Prop) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ result fields recursiveFields current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx fields → recursiveFields.toList.Sublist fields.toList →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post :=
  mkRecInfos.loopCtorArgs.scope stats type next ctx post hwf hreserved hnext

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hscope : RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule := hscope.fvars

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hscope : RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
      (∀ field ∈ fields, ∃ decl, current.lctx.find? decl.fvarId = some decl ∧ decl.toExpr = field ∧
        decl.value? (allowNondep := true) = none ∧ decl.kind = .default) ∧
      (∀ field ∈ recursiveFields, ∃ decl, current.lctx.find? decl.fvarId = some decl ∧ decl.toExpr = field ∧
        decl.value? (allowNondep := true) = none ∧ decl.kind = .default) ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor := hscope.lookups

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat)
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsFVars stats motives minors ctx ctors rules initial := hscope.fvars

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial index : Nat)
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minors[initial + index]! rule :=
  hscope.at index ctor hctor

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial : Nat) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsScope stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length :=
  mkRecRules.rhsScope types elimLevel stats parent motives minors initial ctx hwf hreserved

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext) (isK isUnsafe : Bool)
    (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) : LocalRecursorRuleRhsScope stats types infos ctx env :=
  hmetadata.localRuleRhsScope hcounts hwf hreserved

example (stats : InductiveStats) (types : Array InductiveType) (infos : Array RecInfo)
    (ctx : Context) (env : Kernel.Environment)
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env) :
    LocalRecursorRuleRhsFVars stats types infos ctx env := hscope.fvars

private def scopeStage (stats : InductiveStats) (type : Expr) : M (Array Expr × Array Expr × Context) :=
  mkRecInfos.loopCtorArgs stats type fun _ fields recursiveFields => do
    return (fields, recursiveFields, ← read)

private def checkDeclared (ctx : Context) (fields : Array Expr) : MetaM Unit := do
  for field in fields do
    unless field.isFVar do throwError "generated field is not a free-variable atom"
    let some decl := ctx.lctx.find? field.fvarId! | throwError "generated field has no retained declaration"
    unless decl.toExpr == field && (decl.value? (allowNondep := true)).isNone && decl.kind == .default do
      throwError "generated field has the wrong declaration shape"

private def checkScope (ctx : Context) (stats : InductiveStats) (type : Expr)
    (expectedFields expectedRecursive : Nat) (oldVars : Array FVarId := #[]) : MetaM Unit := do
  let .ok (fields, recursiveFields, current) := scopeStage stats type ctx | throwError "scope traversal failed"
  unless fields.size == expectedFields && recursiveFields.size == expectedRecursive do
    throwError "incorrect scoped field counts"
  checkDeclared current fields
  checkDeclared current recursiveFields
  unless recursiveFields.toList.isSublist fields.toList do throwError "incorrect scoped recursive selection"
  unless current.lctx.numIndices == ctx.lctx.numIndices + fields.size &&
      current.ngen.idx == ctx.ngen.idx + fields.size && current.ngen.namePrefix == ctx.ngen.namePrefix do
    throwError "incorrect local-context or name-generator advancement"
  for fvar in oldVars do
    let some before := ctx.lctx.find? fvar | throwError "missing fixture source declaration"
    let some after := current.lctx.find? fvar | throwError "old declaration disappeared"
    unless before.type == after.type && before.value? (allowNondep := true) == after.value? (allowNondep := true) &&
        before.index == after.index && before.userName == after.userName && before.kind == after.kind do
      throwError "old declaration changed"

private def checkFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let stats := { (default : InductiveStats) with indConsts := #[natType], nindices := #[0] }
  let one := Expr.forallE `field natType natType .default
  let higher := Expr.forallE `argument natType natType .default
  let mixed := Expr.forallE `field natType (.forallE `field boolType
    (.forallE `field higher natType .strictImplicit) .instImplicit) .implicit
  checkScope ctx stats natType 0 0
  checkScope ctx stats one 1 1
  checkScope ctx stats mixed 3 2
  let dependent := Expr.forallE `field (.sort (.succ .zero))
    (.forallE `field (.bvar 0) natType .implicit) .default
  checkScope ctx default dependent 2 0
  let params := { (default : InductiveStats) with params := #[natType] }
  let withParam := Expr.forallE `parameter (.sort (.succ .zero)) one .default
  checkScope ctx params withParam 1 0
  let expands := Expr.forallE `parameter (.sort (.succ .zero)) (.bvar 0) .default
  checkScope ctx { params with params := #[one] } expands 1 0
  let repeated := Expr.forallE `field natType (Expr.forallE `field natType one .default) .default
  checkScope ctx stats repeated 3 3
  let old : FVarId := ⟨.num `ScopeSeed 2⟩
  let oldLet : FVarId := ⟨`ExternalLet⟩
  let seeded := { ctx with
    ngen := { namePrefix := `ScopeSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl old `field boolType .implicit |>.mkLetDecl oldLet `field natType (.const ``Nat.zero []) }
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .implicit) natType
  checkScope seeded stats many 33 33 #[old, oldLet]
  logInfo "eight retained-field scope fixtures passed native declarations, ordered selections, and reader advancement"

private def checkBoundaries (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let one := Expr.forallE `field natType natType .default
  let .ok (fields, _, current) := scopeStage default one ctx | throwError "reader boundary traversal failed"
  unless (ctx.lctx.find? fields[0]!.fvarId!).isNone && (current.lctx.find? fields[0]!.fvarId!).isSome do
    throwError "retained declaration must not be asserted in the original reader"
  let collision := { ctx with lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ `old boolType .default }
  let .ok (_, _, overwritten) := scopeStage default one collision | throwError "freshness control failed"
  let some before := collision.lctx.find? ⟨ctx.ngen.curr⟩ | throwError "missing collision source"
  let some after := overwritten.lctx.find? ⟨ctx.ngen.curr⟩ | throwError "missing collision result"
  unless before.type == boolType && after.type == natType do
    throwError "unreserved helper context must expose lookup overwrite"
  let .error .deepRecursion := scopeStage default natType
      { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } } | throwError "zero-fuel failure was lost"
  let two := Expr.forallE `field natType one .default
  let .error .deepRecursion := scopeStage default two
      { ctx with fuel := { ctx.fuel with inductiveFuel := 2 } } | throwError "partial scope traversal must fail"
  logInfo "original-reader and missing-freshness controls, plus two fuel failures, passed"

private def checkRuleReplay (ctx : Context) (stats : InductiveStats) (types : Array InductiveType)
    (minors : Array Expr) (initial : Nat) : MetaM Unit := do
  let .ok (rules, finalIndex) := mkRecRules types (.succ .zero) stats 0 #[] minors initial ctx
    | throwError "scoped rule generation failed"
  unless rules.length == types[0]!.ctors.length && finalIndex == initial + rules.length do
    throwError "incorrect scoped rule count or minor advancement"
  for (ctor, index) in types[0]!.ctors.zipIdx do
    let .ok (fields, recursiveFields, current) := scopeStage stats ctor.type ctx
      | throwError "scoped rule replay traversal failed"
    checkDeclared current fields
    checkDeclared current recursiveFields
    let replay := mkRecRules.loopU types stats #[] minors [] recursiveFields 0 #[] fun values =>
      pure (({
        ctor := ctor.name
        nfields := fields.size
        rhs := recursorRuleRhs stats #[] minors fields values current.lctx minors[initial + index]! } : RecursorRule),
        values.size)
    let .ok (expected, count) := replay current | throwError "scoped RHS replay failed"
    let some rule := rules[index]? | throwError "missing scoped rule"
    unless rule.ctor == expected.ctor && rule.nfields == expected.nfields && rule.rhs == expected.rhs &&
        count == recursiveFields.size && count <= rule.nfields do
      throwError "scoped field witnesses do not replay the installed RHS recipe"

private def checkRuleFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let one := Expr.forallE `field natType natType .default
  let higher := Expr.forallE `argument natType natType .default
  let mixed := Expr.forallE `field boolType (.forallE `field higher one .implicit) .instImplicit
  let dependent := Expr.forallE `field (.sort (.succ .zero))
    (.forallE `field (.bvar 0) natType .implicit) .default
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .implicit) natType
  let constructors : List Constructor := [
    { name := `ScopeRules.empty, type := natType },
    { name := `ScopeRules.one, type := one },
    { name := `ScopeRules.mixed, type := mixed },
    { name := `ScopeRules.dependent, type := dependent },
    { name := `ScopeRules.many, type := many }]
  let types : Array InductiveType := #[{ name := ``Nat, type := .sort (.succ .zero), ctors := constructors }]
  let stats := { (default : InductiveStats) with indConsts := #[natType], nindices := #[0] }
  let minors := (List.range 7).toArray.map fun index => Expr.fvar ⟨.num `ScopeMinor index⟩
  let lctx := minors.foldl (fun lctx minor => lctx.mkLocalDecl minor.fvarId! `minor natType .default) ctx.lctx
  let source := { ctx with lctx }
  checkRuleReplay source stats types minors 0
  checkRuleReplay { source with ngen := { namePrefix := `RuleSeed, idx := 23 } } stats types minors 2
  logInfo "ten scoped rule replays passed native field declarations, exact RHS recipes, and minor offsets"

private def audit (theoremName : Name) (mapInterfaces := false) (arrayInterface := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if mapInterfaces then [
    ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert] else []
  let allowed := allowed ++ if arrayInterface then [``Lean.PersistentArray.toList'_push] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

private def auditTheorems : MetaM Unit := do
  audit ``LocalContext.WF.find?_of_mem true true
  audit ``Context.RecursorScopeFrame.refl
  audit ``Context.RecursorScopeFrame.trans
  audit ``Context.RecursorScopeFrame.push true true
  audit ``Context.RecursorScopeFrame.oldLookup true true
  audit ``RecursorFieldsDeclared.fvars
  audit ``RecursorFieldsDeclared.sublist
  audit ``RecursorFieldsDeclared.push false true
  audit ``RecursorFieldsDeclared.lookup true true
  audit ``mkRecInfos.loopCtorArgs.scope true true
  audit ``RecursorRuleRhsScopeReceipt.fvars
  audit ``RecursorRuleRhsScopeReceipt.lookups true true
  audit ``RecursorRuleRhsScope.fvars
  audit ``RecursorRuleRhsScope.at
  audit ``mkRecRules.rhsScope true true
  audit ``InductiveStats.RecursorOffsetMetadata.localRuleRhsScope true true
  audit ``LocalRecursorRuleRhsScope.fvars

run_meta
  auditTheorems
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  checkFixtures ctx
  checkBoundaries ctx
  checkRuleFixtures ctx

end RecursorFieldScopeTest
