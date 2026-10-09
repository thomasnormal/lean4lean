import Lean4Lean.Verify.RecursorRuleRhsFVars
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive

namespace RecursorRegistrationTest

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx).WF
      fun env => env.constants.WF ∧
        ∀ name info, ctx.env.find? name = some info → env.find? name = some info :=
  declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx = .ok env) :
    env.constants.WF :=
  (declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx
    hwf env hresult).1

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (recInfos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment) (name : Name) (info : ConstantInfo)
    (hold : ctx.env.find? name = some info)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe ctx = .ok env) :
    env.find? name = some info :=
  (declareRecursors.preserves stats types elimLevel recInfos lparams lctx isK isUnsafe ctx
    hwf env hresult).2 name info hold

example (stats : InductiveStats) (types : Array InductiveType) (nparams numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested original root constructors)
    (elimLevel : Level) (recInfos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool)
    (hresult : declareRecursors stats types elimLevel recInfos lparams lctx isK isUnsafe
      { root with env := constructors } = .ok env) :
    env.constants.WF ∧
      (∀ name info, original.env.find? name = some info → env.find? name = some info) ∧
      stats.HeaderMetadata nparams types numNested false original.lparams env ∧
      stats.ConstructorMetadata original.lparams types false env := by
  obtain ⟨hfinal, hkeep⟩ := declareRecursors.preserves stats types elimLevel recInfos lparams
    lctx isK isUnsafe { root with env := constructors } hregistration.resultWF env hresult
  refine ⟨hfinal, fun name info hold => hkeep name info (hregistration.preservesOriginal name info hold),
    ?_, ?_⟩
  · intro parent hparent
    exact hkeep _ _ (hregistration.resultHeaderMetadata parent hparent)
  · intro parent hparent index ctor hctor
    obtain ⟨hfind, harity⟩ := hregistration.constructorMetadata parent hparent index ctor hctor
    exact ⟨hkeep _ _ hfind, harity⟩

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env :=
  declareRecursors.metadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment)
    (hresult : declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx = .ok env)
    (index : Nat) (hindex : index < types.size) :
    ∃ rules minorIndex nextIndex,
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (rules, nextIndex) ∧
      env.find? (mkRecName types[index]!.name) = some (.recInfo
        (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules)) :=
  (declareRecursors.metadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf
    env hresult).2.2 index hindex

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ (info : RecursorVal) (minorIndex nextIndex : Nat),
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (info.rules, nextIndex) :=
  hmetadata.sourceRules

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment) (nparams : Nat)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hparams : stats.ParamsCount nparams types.size) (hmotives : infos.size = types.size)
    (hminors : (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length) :
    stats.DeclaredRecursorCounts nparams types env :=
  hmetadata.declaredCounts hparams hmotives hminors

example (stats : InductiveStats) (types : Array InductiveType) (nparams numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment)
    (hregistration : stats.SafeConstructorRegistration nparams types numNested original root constructors)
    (elimLevel : Level) (infos : Array RecInfo) (lctx : LocalContext) (isK isUnsafe : Bool)
    (hresult : declareRecursors stats types elimLevel infos original.lparams lctx isK isUnsafe
      { root with env := constructors } = .ok env)
    (hmotives : infos.size = types.size)
    (hminors : (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length) :
    stats.DeclaredRecursorCounts nparams types env := by
  have hmetadata := (declareRecursors.metadata stats types elimLevel infos original.lparams
    lctx isK isUnsafe { root with env := constructors } hregistration.resultWF env hresult).2.2
  exact hmetadata.declaredCounts hregistration.traces.2.1 hmotives hminors

example (stats : InductiveStats) (env : Kernel.Environment) :
    stats.DeclaredRecursorCounts 17 #[] env := by
  simp [InductiveStats.DeclaredRecursorCounts]

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (index : Nat) (motives minors : Array Expr) (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats index motives minors initial ctx).WF fun result =>
      RecursorRuleShape types[index]!.ctors result.1 initial result.2 :=
  mkRecRules.shape types elimLevel stats index motives minors initial ctx

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (index : Nat) (motives minors : Array Expr) (initial final : Nat) (ctx : Context)
    (rules : List RecursorRule)
    (hresult : mkRecRules types elimLevel stats index motives minors initial ctx = .ok (rules, final)) :
    rules.map (·.ctor) = types[index]!.ctors.map (·.name) ∧
      rules.length = types[index]!.ctors.length ∧ final = initial + types[index]!.ctors.length := by
  have hshape := mkRecRules.shape types elimLevel stats index motives minors initial ctx _ hresult
  exact ⟨hshape.names, hshape.count, hshape.stateAdvance⟩

example (ctors : List Constructor) (rules : List RecursorRule) (initial final : Nat)
    (hshape : RecursorRuleShape ctors rules initial final) : rules.length = ctors.length :=
  hshape.count

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ (info : RecursorVal) (initial final : Nat),
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      RecursorRuleShape types[index]!.ctors info.rules initial final :=
  hmetadata.ruleShape

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    OrderedRecursorRules types env :=
  hmetadata.orderedRules

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (index : Nat) (hindex : index < types.size) :
    ∃ info : RecursorVal, env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      info.rules.map (·.ctor) = types[index]!.ctors.map (·.name) ∧
      info.rules.length = types[index]!.ctors.length :=
  hmetadata.orderedRules index hindex

example (types : Array InductiveType) (index : Nat) (hindex : index < types.size) :
    recursorMinorOffset types (index + 1) = recursorMinorOffset types index + types[index]!.ctors.length :=
  recursorMinorOffset.succ types index hindex

example (types : Array InductiveType) :
    recursorMinorOffset types types.size = (types.toList.flatMap (·.ctors)).length :=
  recursorMinorOffset.total types

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env :=
  declareRecursors.offsetMetadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF)
    (env : Kernel.Environment)
    (hresult : declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx = .ok env)
    (index : Nat) (hindex : index < types.size) :
    ∃ rules,
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        (recursorMinorOffset types index) ctx = .ok (rules, recursorMinorOffset types (index + 1)) ∧
      env.find? (mkRecName types[index]!.name) = some (.recInfo
        (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules)) :=
  (declareRecursors.offsetMetadata stats types elimLevel infos lparams lctx isK isUnsafe ctx hwf
    env hresult).2.2 index hindex

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ info : RecursorVal,
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        (recursorMinorOffset types index) ctx = .ok (info.rules, recursorMinorOffset types (index + 1)) :=
  hmetadata.sourceRules

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env :=
  hmetadata.metadata

example (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hfvars : stats.ParamsAreFVars)
    (hnext : ∀ result fields recursiveFields current, ctx.HeaderFrame current →
      fields.size = declareConstructors.arity 0 type - stats.params.size →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post :=
  mkRecInfos.loopCtorArgs.fields stats type next ctx post hfvars hnext

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (index : Nat) (motives minors : Array Expr) (state : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) :
    (mkRecRules types elimLevel stats index motives minors state ctx).WF fun result =>
      RecursorRuleFields stats types[index]!.ctors result.1 :=
  mkRecRules.fieldCounts types elimLevel stats index motives minors state ctx hfvars

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial final : Nat) (ctx : Context)
    (hfvars : stats.ParamsAreFVars) (rules : List RecursorRule)
    (hresult : mkRecRules types elimLevel stats parent motives minors initial ctx = .ok (rules, final))
    (index : Nat) (ctor : Constructor) (hctor : types[parent]!.ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧ rule.ctor = ctor.name ∧
      rule.nfields = declareConstructors.arity 0 ctor.type - stats.params.size :=
  (mkRecRules.fieldCounts types elimLevel stats parent motives minors initial ctx hfvars _ hresult).at
    index ctor hctor

example (stats : InductiveStats) (ctors : List Constructor) (rules : List RecursorRule)
    (hfields : RecursorRuleFields stats ctors rules) (index : Nat) (ctor : Constructor)
    (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧ rule.ctor = ctor.name ∧
      rule.nfields = declareConstructors.arity 0 ctor.type - stats.params.size :=
  hfields.at index ctor hctor

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hfvars : stats.ParamsAreFVars) :
    ∀ index, index < types.size → ∃ info : RecursorVal,
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      RecursorRuleFields stats types[index]!.ctors info.rules :=
  hmetadata.ruleFields hfvars

example (types : Array InductiveType) (infos : Array RecInfo)
    (hcounts : RecursorInfoCounts types infos) (index : Nat) :
    ((infos.toList.take index).flatMap (fun info => info.minors.toList)).length =
      recursorMinorOffset types index :=
  hcounts.minorPrefix index

example (types : Array InductiveType) (infos : Array RecInfo)
    (hcounts : RecursorInfoCounts types infos) : RecursorMinorIndexing types infos :=
  hcounts.minorIndexing

example (types : Array InductiveType) (infos : Array RecInfo)
    (hcounts : RecursorInfoCounts types infos) (parent index : Nat)
    (hparent : parent < types.size) (hindex : index < types[parent]!.ctors.length) :
    index < infos[parent]!.minors.size ∧
      recursorMinorOffset types parent + index < (infos.flatMap (·.minors)).size ∧
      (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]? =
        infos[parent]!.minors[index]? :=
  hcounts.minorIndexing parent hparent index hindex

example (types : Array InductiveType) (infos : Array RecInfo)
    (hcounts : RecursorInfoCounts types infos) (parent index : Nat)
    (hparent : parent < types.size) (hindex : index < types[parent]!.ctors.length) :
    ∃ minor, infos[parent]!.minors[index]? = some minor ∧
      (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]? = some minor :=
  hcounts.minorIndexing.at parent hparent index hindex

example (types : Array InductiveType) (infos : Array RecInfo)
    (hcounts : RecursorInfoCounts types infos) (parent index : Nat)
    (hparent : parent < types.size) (hindex : index < types[parent]!.ctors.length) :
    (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]! =
      infos[parent]!.minors[index]! :=
  hcounts.minorIndexing.getElem! parent hparent index hindex

example (infos : Array RecInfo) : RecursorMinorIndexing #[] infos := by
  intro parent hparent
  simp at hparent

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhs stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length :=
  mkRecRules.rhs types elimLevel stats parent motives minors initial ctx

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial final : Nat) (ctx : Context)
    (rules : List RecursorRule)
    (hresult : mkRecRules types elimLevel stats parent motives minors initial ctx = .ok (rules, final)) :
    RecursorRuleRhs stats motives minors ctx types[parent]!.ctors rules initial :=
  (mkRecRules.rhs types elimLevel stats parent motives minors initial ctx _ hresult).1

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat)
    (hrhs : RecursorRuleRhs stats motives minors ctx ctors rules initial) :
    rules.length = ctors.length := hrhs.count

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial index : Nat)
    (hrhs : RecursorRuleRhs stats motives minors ctx ctors rules initial)
    (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsReceipt stats motives minors ctx ctor minors[initial + index]! rule :=
  hrhs.at index ctor hctor

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hreceipt : RecursorRuleRhsReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
      rule.rhs = current.lctx.mkLambda stats.params (current.lctx.mkLambda motives
        (current.lctx.mkLambda minors (current.lctx.mkLambda fields (mkAppN (mkAppN minor fields) values)))) :=
  hreceipt

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext) (isK isUnsafe : Bool)
    (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) : LocalRecursorRuleRhs stats types infos ctx env :=
  hmetadata.localRuleRhs hcounts

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context) (initial : Nat) :
    RecursorRuleRhs stats motives minors ctx [] [] initial := .nil

example (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ result fields recursiveFields current, ctx.HeaderFrame current →
      recursiveFields.toList.Sublist fields.toList → (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post :=
  mkRecInfos.loopCtorArgs.recursiveFields stats type next ctx post hnext

example (types : Array InductiveType) (stats : InductiveStats) (motives minors : Array Expr)
    (levels : List Level) (recursiveFields : Array Expr) (index : Nat) (values : Array Expr)
    (next : Array Expr → M (RecursorRule × Nat)) (ctx : Context) (post : RecursorRule × Nat → Prop)
    (hnext : ∀ finalValues, finalValues.size = values.size + (recursiveFields.size - index) →
      (next finalValues ctx).WF post) :
    (mkRecRules.loopU types stats motives minors levels recursiveFields index values next ctx).WF post :=
  mkRecRules.loopU.counts types stats motives minors levels recursiveFields index values next ctx post hnext

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hcounts : RecursorRuleRhsCountReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsReceipt stats motives minors ctx ctor minor rule := hcounts.receipt

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hcounts : RecursorRuleRhsCountReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧ values.size ≤ rule.nfields ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor :=
  hcounts.argumentBound

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsCounts stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length :=
  mkRecRules.rhsCounts types elimLevel stats parent motives minors initial ctx

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat)
    (hcounts : RecursorRuleRhsCounts stats motives minors ctx ctors rules initial) :
    RecursorRuleRhs stats motives minors ctx ctors rules initial := hcounts.rhs

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial index : Nat)
    (hcounts : RecursorRuleRhsCounts stats motives minors ctx ctors rules initial)
    (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsCountReceipt stats motives minors ctx ctor minors[initial + index]! rule :=
  hcounts.at index ctor hctor

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext) (isK isUnsafe : Bool)
    (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) : LocalRecursorRuleRhsCounts stats types infos ctx env :=
  hmetadata.localRuleRhsCounts hcounts

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context) (initial : Nat) :
    RecursorRuleRhsCounts stats motives minors ctx [] [] initial := .nil

example (fields : Array Expr) (hfields : RecursorFieldsAreFVars fields)
    (field : Expr) (hfield : field.isFVar = true) : RecursorFieldsAreFVars (fields.push field) :=
  hfields.push hfield

example (fields selected : Array Expr) (hfields : RecursorFieldsAreFVars fields)
    (hselected : selected.toList.Sublist fields.toList) : RecursorFieldsAreFVars selected :=
  hfields.sublist hselected

example (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ result fields recursiveFields current, ctx.HeaderFrame current →
      RecursorFieldsAreFVars fields → recursiveFields.toList.Sublist fields.toList →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post :=
  mkRecInfos.loopCtorArgs.fvars stats type next ctx post hnext

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hvars : RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsCountReceipt stats motives minors ctx ctor minor rule := hvars.counts

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctor : Constructor) (minor : Expr) (rule : RecursorRule)
    (hvars : RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
      RecursorFieldsAreFVars fields ∧ RecursorFieldsAreFVars recursiveFields ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧ values.size ≤ rule.nfields ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor :=
  hvars.shapes

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat)
    (hvars : RecursorRuleRhsFVars stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsCounts stats motives minors ctx ctors rules initial := hvars.counts

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial index : Nat)
    (hvars : RecursorRuleRhsFVars stats motives minors ctx ctors rules initial)
    (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minors[initial + index]! rule :=
  hvars.at index ctor hctor

example (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (parent : Nat) (motives minors : Array Expr) (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsFVars stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length :=
  mkRecRules.rhsFVars types elimLevel stats parent motives minors initial ctx

example (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext) (isK isUnsafe : Bool)
    (ctx : Context) (env : Kernel.Environment)
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) : LocalRecursorRuleRhsFVars stats types infos ctx env :=
  hmetadata.localRuleRhsFVars hcounts

example (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context) (initial : Nat) :
    RecursorRuleRhsFVars stats motives minors ctx [] [] initial := .nil

private def fieldStage (params : Array Expr) (type : Expr) : M Nat :=
  mkRecInfos.loopCtorArgs { (default : InductiveStats) with params } type fun _ fields _ =>
    pure fields.size

private def checkRawFields (ctx : Context) (params : Array Expr) (type : Expr)
    (expected : Nat) : MetaM Unit := do
  let .ok fields := fieldStage params type ctx | throwError "raw field-count fixture failed"
  unless fields == expected do throwError "incorrect raw field count"

private def statsFor (types : Array InductiveType) : InductiveStats := {
  levels := [], resultLevel := .succ .zero, params := #[], isNotZero := true,
  indConsts := types.map fun type => .const type.name [], nindices := types.map fun _ => 0 }

private def typeFor (name : Name) (ctors : List Name) : InductiveType := {
  name, type := .sort (.succ .zero),
  ctors := ctors.map fun ctor => { name := ctor, type := .const name [] } }

private def infoFor (name : Name) (minorNames : Array Name) : RecInfo := {
  motive := .fvar ⟨name ++ `motive⟩, major := .fvar ⟨name ++ `major⟩, indices := #[],
  minors := minorNames.map fun minor => .fvar ⟨minor⟩ }

private def fieldShapeStage (stats : InductiveStats) (type : Expr) : M (Array Expr × Array Expr) :=
  mkRecInfos.loopCtorArgs stats type fun _ fields recursiveFields => pure (fields, recursiveFields)

private def checkFieldShape (ctx : Context) (stats : InductiveStats) (type : Expr)
    (fieldCount recursiveCount : Nat) : MetaM Unit := do
  let .ok (fields, recursiveFields) := fieldShapeStage stats type ctx | throwError "field-shape fixture failed"
  unless fields.size == fieldCount && recursiveFields.size == recursiveCount &&
      fields.all (·.isFVar) && recursiveFields.all (·.isFVar) &&
      recursiveFields.toList.isSublist fields.toList do
    throwError "incorrect free-variable field/selection shape"

private def recursiveValueShapeStage (stats : InductiveStats) (types : Array InductiveType)
    (type : Expr) : M (RecursorRule × Nat) :=
  mkRecInfos.loopCtorArgs stats type fun _ _ recursiveFields =>
    mkRecRules.loopU types stats #[] #[] [] recursiveFields 0 #[] fun values =>
      pure ((default : RecursorRule), if values.all (·.isFVar) then 1 else 0)

private def checkFieldShapeFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let types := #[typeFor ``Nat []]
  let stats := statsFor types
  let one := Expr.forallE `field natType natType .default
  let higher := Expr.forallE `argument natType natType .default
  let mixed := Expr.forallE `field natType (.forallE `field boolType
    (.forallE `field higher natType .strictImplicit) .instImplicit) .implicit
  checkFieldShape ctx stats natType 0 0
  checkFieldShape ctx stats one 1 1
  checkFieldShape ctx stats mixed 3 2
  let parameterStats := { (default : InductiveStats) with params := #[.fvar ⟨`ShapeParameter⟩] }
  let withParameter := Expr.forallE `parameter (.sort (.succ .zero)) one .default
  checkFieldShape ctx parameterStats withParameter 1 0
  let dependent := Expr.forallE `parameter (.sort (.succ .zero))
    (.forallE `field (.bvar 0) (.bvar 1) .default) .default
  checkFieldShape ctx { parameterStats with params := #[natType] } dependent 1 0
  let expands := Expr.forallE `parameter (.sort (.succ .zero)) (.bvar 0) .default
  checkFieldShape ctx { parameterStats with params := #[one] } expands 1 0
  let repeated := Expr.forallE `field natType (Expr.forallE `field natType one .default) .default
  checkFieldShape ctx stats repeated 3 3
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .implicit) natType
  checkFieldShape { ctx with ngen := { namePrefix := `ShapeSeed, idx := 17 } } stats many 33 33
  let .ok (fields, _) := fieldShapeStage stats one ctx | throwError "escaping-field control failed"
  let inferField : M Expr := do return (← TypeChecker.inferType fields[0]!)
  let .error (.other _) := inferField ctx
    | throwError "free-variable shape must not assert declaration membership in the original reader context"
  let .ok (_, isFVar) := recursiveValueShapeStage stats types one ctx
    | throwError "recursive-value shape control failed"
  unless isFVar == 0 do throwError "generated recursive values need not be free variables"
  let .error .deepRecursion := fieldShapeStage stats natType
      { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "field-shape traversal must propagate zero-fuel failure"
  logInfo "eight field-shape fixtures, two scope/value-shape controls, and one fuel failure passed"

private def argumentCountStage (stats : InductiveStats) (types : Array InductiveType) (type : Expr)
    (index : Nat) (initial : Array Expr) : M (RecursorRule × Nat) :=
  mkRecInfos.loopCtorArgs stats type fun _ fields recursiveFields => do
    unless fields.all (·.isFVar) && recursiveFields.all (·.isFVar) do
      throw (.other "incorrect argument free-variable shape")
    unless recursiveFields.toList.isSublist fields.toList do throw (.other "incorrect recursive-field selection")
    mkRecRules.loopU types stats #[] #[] [] recursiveFields index initial fun values => do
      unless values.size == initial.size + (recursiveFields.size - index) do
        throw (.other "incorrect recursive-value count")
      return ({ ctor := `CountFixture, nfields := fields.size, rhs := .bvar 0 }, values.size)

private def checkArgumentCounts (ctx : Context) (stats : InductiveStats) (types : Array InductiveType)
    (type : Expr) (index : Nat) (initial : Array Expr) (fields values : Nat) : MetaM Unit := do
  let .ok (rule, count) := argumentCountStage stats types type index initial ctx
    | throwError "argument-count fixture failed"
  unless rule.nfields == fields && count == values do throwError "incorrect expected argument counts"

private def checkArgumentCountFixtures (ctx : Context) : MetaM Unit := do
  let natType := Expr.const ``Nat []
  let boolType := Expr.const ``Bool []
  let types := #[typeFor ``Nat []]
  let stats := statsFor types
  let one := Expr.forallE `field natType natType .default
  let higher := Expr.forallE `argument natType natType .default
  let mixed := [boolType, natType, higher, boolType, natType].foldr
    (fun domain body => .forallE `field domain body .implicit) natType
  checkArgumentCounts ctx stats types natType 0 #[] 0 0
  checkArgumentCounts ctx stats types one 0 #[] 1 1
  checkArgumentCounts ctx stats types mixed 0 #[] 5 3
  let parameterStats := { stats with params := #[.fvar ⟨`CountParameter⟩], indConsts := #[], nindices := #[] }
  let parameterType := Expr.forallE `parameter (.sort (.succ .zero)) one .default
  checkArgumentCounts ctx parameterStats types parameterType 0 #[] 1 0
  checkArgumentCounts ctx stats types mixed 1 #[natType, boolType] 5 4
  checkArgumentCounts ctx stats types mixed 3 #[natType] 5 1
  checkArgumentCounts ctx stats types mixed 7 #[natType, boolType] 5 2
  let many := (List.range 33).foldr (fun _ body => .forallE `field natType body .default) natType
  checkArgumentCounts ctx stats types many 0 #[] 33 33
  let zeroFuel := { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
  let .error .deepRecursion := argumentCountStage stats types natType 0 #[] zeroFuel
    | throwError "constructor selection must propagate zero-fuel failure"
  let next := fun values : Array Expr => pure ((default : RecursorRule), values.size)
  let .error .deepRecursion := mkRecRules.loopU types stats #[] #[] [] #[.const ``Nat.zero []]
      0 #[] next zeroFuel
    | throwError "recursive-value traversal must propagate zero-fuel failure"
  logInfo "eight argument-count fixtures, ordered selections, shifted/prefilled traversal boundaries, and two fuel failures passed"

private def checkMinorIndexing (types : Array InductiveType) (infos : Array RecInfo) : MetaM Unit := do
  unless infos.size == types.size do throwError "incorrect indexing information count"
  let flattened := infos.flatMap (·.minors)
  for parent in [:types.size + 3] do
    let minorPrefixSize := ((infos.toList.take parent).flatMap (fun info => info.minors.toList)).length
    unless minorPrefixSize == recursorMinorOffset types parent do throwError "incorrect minor-prefix alignment"
  for parent in [:types.size] do
    let localMinors := infos[parent]!.minors
    unless localMinors.size == types[parent]!.ctors.length do throwError "incorrect local minor count"
    for index in [:types[parent]!.ctors.length] do
      let offset := recursorMinorOffset types parent + index
      unless index < localMinors.size && offset < flattened.size do throwError "minor lookup is out of bounds"
      let some minor := localMinors[index]? | throwError "missing local minor"
      unless flattened[offset]? == some minor && flattened[offset]! == localMinors[index]! do
        throwError "flattened minor differs from the corresponding local minor"

private def localsFor (infos : Array RecInfo) : LocalContext := Id.run do
  let mut lctx : LocalContext := {}
  for info in infos do
    for binder in #[info.motive, info.major] ++ info.minors do
      lctx := lctx.mkLocalDecl binder.fvarId! binder.fvarId!.name (.const ``Nat [])
  return lctx

private def checkRuleSourceShape (ctx : Context) (types : Array InductiveType)
    (infos : Array RecInfo) (index initial : Nat) : MetaM Unit := do
  let .ok (rules, final) := mkRecRules types .zero (statsFor types) index
      (infos.map (·.motive)) (infos.flatMap (·.minors)) initial { ctx with lctx := localsFor infos }
    | throwError "rule-source shape fixture unexpectedly failed"
  unless rules.map (·.ctor) == types[index]!.ctors.map (·.name) &&
      rules.length == types[index]!.ctors.length && final == initial + types[index]!.ctors.length do
    throwError "incorrect rule-source names, count, or state advancement"
  for ruleIndex in [:rules.length] do
    let expected := recursorRuleRhs (statsFor types) (infos.map (·.motive)) (infos.flatMap (·.minors))
      #[] #[] (localsFor infos) (infos.flatMap (·.minors))[initial + ruleIndex]!
    unless rules[ruleIndex]!.rhs == expected do throwError "incorrect shifted zero-field RHS receipt"

private def checkPreserved (original env : Kernel.Environment) (name : Name) : MetaM Unit := do
  let some old := original.find? name | throwError "missing old-entry fixture {name}"
  let some retained := env.find? name | throwError "recursor registration dropped {name}"
  unless old.name == retained.name && old.type == retained.type &&
      old.levelParams == retained.levelParams && old.isUnsafe == retained.isUnsafe do
    throwError "recursor registration changed {name}"

private def rulesMatch (before after : List RecursorRule) : Bool :=
  before.length == after.length && (before.zip after).all fun pair =>
    pair.1.ctor == pair.2.ctor && pair.1.nfields == pair.2.nfields && pair.1.rhs == pair.2.rhs

private def rhsReceiptStage (types : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (infos : Array RecInfo) (ctor : Constructor) (minor : Expr) : M (RecursorRule × Nat) :=
  mkRecInfos.loopCtorArgs stats ctor.type fun _ fields recursiveFields => do
    unless fields.all (·.isFVar) && recursiveFields.all (·.isFVar) do
      throw (.other "incorrect receipt free-variable field shape")
    unless recursiveFields.toList.isSublist fields.toList do throw (.other "incorrect receipt recursive-field selection")
    mkRecRules.loopU types stats (infos.map (·.motive)) (infos.flatMap (·.minors))
      (getRecLevels elimLevel stats.levels) recursiveFields 0 #[] fun values => do
      unless values.size == recursiveFields.size && values.size ≤ fields.size do
        throw (.other "incorrect receipt recursive-value/field alignment")
      let lctx ← getLCtx
      let rule : RecursorRule := {
        ctor := ctor.name, nfields := fields.size,
        rhs := recursorRuleRhs stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          fields values lctx minor }
      return (rule, values.size)

private def checkLocalRhs (ctx : Context) (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (infos : Array RecInfo) (parent index : Nat)
    (ctor : Constructor) (rule : RecursorRule) : MetaM Unit := do
  let some minor := infos[parent]!.minors[index]? | throwError "missing RHS receipt's local minor"
  let .ok (receipt, count) := rhsReceiptStage types elimLevel stats infos ctor minor ctx
    | throwError "local-minor RHS receipt did not replay"
  unless rule.ctor == receipt.ctor && rule.nfields == receipt.nfields && count ≤ rule.nfields &&
      rule.rhs == receipt.rhs do
    throwError "installed RHS differs from its positional local-minor receipt"

private def checkRhsMinorControl (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (parent index alternate : Nat) : MetaM Unit := do
  let current := { ctx with lctx := localsFor infos }
  let .ok (rules, _) := mkRecRules types .zero (statsFor types) parent
      (infos.map (·.motive)) (infos.flatMap (·.minors)) (recursorMinorOffset types parent) current
    | throwError "RHS minor-control generation failed"
  let some ctor := types[parent]!.ctors[index]? | throwError "missing RHS control constructor"
  let some rule := rules[index]? | throwError "missing RHS control rule"
  let some minor := infos[parent]!.minors[alternate]? | throwError "missing alternate RHS control minor"
  let .ok (receipt, _) := rhsReceiptStage types .zero (statsFor types) infos ctor minor current
    | throwError "alternate RHS minor-control replay failed"
  unless rule.rhs != receipt.rhs do throwError "RHS receipt must distinguish different positional minors"

private def checkExact (ctx : Context) (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name) (lctx : LocalContext)
    (isK isUnsafe : Bool) (env : Kernel.Environment) (index minorIndex : Nat) : MetaM Nat := do
  let .ok (rules, nextIndex) := mkRecRules types elimLevel stats index
      (infos.map (·.motive)) (infos.flatMap (·.minors)) minorIndex ctx
    | throwError "rule-generation receipt did not replay"
  let expected := declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules
  let some (.recInfo actual) := env.find? expected.name | throwError "missing exact recursor record"
  unless actual.name == expected.name && actual.type == expected.type &&
      actual.levelParams == expected.levelParams && actual.all == expected.all &&
      actual.numParams == expected.numParams && actual.numIndices == expected.numIndices &&
      actual.numMotives == expected.numMotives && actual.numMinors == expected.numMinors &&
      actual.k == expected.k && actual.isUnsafe == expected.isUnsafe && rulesMatch actual.rules rules do
    throwError "installed recursor differs from the complete metadata specification"
  unless minorIndex == recursorMinorOffset types index &&
      nextIndex == recursorMinorOffset types (index + 1) do
    throwError "incorrect replayed starting/ending minor prefix offsets"
  for ruleIndex in [:types[index]!.ctors.length] do
    let ctor := types[index]!.ctors[ruleIndex]!
    let rule := actual.rules[ruleIndex]!
    unless rule.ctor == ctor.name &&
        rule.nfields == declareConstructors.arity 0 ctor.type - stats.params.size do
      throwError "incorrect ordered raw rule field count"
    checkLocalRhs ctx types elimLevel stats infos index ruleIndex ctor rule
  return nextIndex

private def checkRecursor (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (lparams : List Name) (elimLevel : Level) (lctx : LocalContext) (env : Kernel.Environment)
    (index offset : Nat) (isK isUnsafe : Bool) : MetaM Unit := do
  let type := types[index]!
  let some (.recInfo info) := env.find? (mkRecName type.name)
    | throwError "missing recursor {type.name}"
  let minors := infos.flatMap (·.minors)
  unless info.levelParams == getRecLevelParams elimLevel lparams &&
      !info.type.hasFVar &&
      info.numParams == 0 && info.numIndices == 0 && info.numMotives == infos.size &&
      info.numMinors == minors.size && info.all == (types.map (·.name)).toList &&
      info.k == isK && info.isUnsafe == isUnsafe && info.rules.length == type.ctors.length do
    throwError "incorrect recursor metadata for {type.name}"
  for ruleIndex in [:type.ctors.length] do
    let rule := info.rules[ruleIndex]!
    let expected := recursorRuleRhs (statsFor types) (infos.map (·.motive)) minors #[] #[] lctx
      infos[index]!.minors[ruleIndex]!
    unless rule.ctor == type.ctors[ruleIndex]!.name && rule.nfields == 0 &&
        rule.rhs == expected && !rule.rhs.hasFVar do
      throwError "incorrect threaded minor index for {type.name}, rule {ruleIndex}"
  discard <| checkExact ctx (statsFor types) types elimLevel infos lparams lctx isK isUnsafe env index offset

private def checkSuccess (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (lparams : List Name) (elimLevel : Level) (isK isUnsafe : Bool) : MetaM Unit := do
  checkMinorIndexing types infos
  let lctx := localsFor infos
  let .ok env := declareRecursors (statsFor types) types elimLevel infos lparams lctx isK isUnsafe
      { ctx with lctx }
    | throwError "low-level recursor registration unexpectedly failed"
  let mut offset := 0
  for index in [:types.size] do
    checkRecursor { ctx with lctx } types infos lparams elimLevel lctx env index offset isK isUnsafe
    offset := offset + types[index]!.ctors.length
  unless offset == recursorMinorOffset types types.size &&
      offset == (types.toList.flatMap (·.ctors)).length do
    throwError "incorrect total minor prefix offset"
  for name in [``Nat, ``Nat.zero, ``Nat.succ, ``Nat.rec, ``List, ``List.rec] do
    checkPreserved ctx.env env name
  unless env.quotInit == ctx.env.quotInit do throwError "recursor registration changed quotient state"

private def checkCollision (ctx : Context) (types : Array InductiveType) (infos : Array RecInfo)
    (expected : Name) : MetaM Unit := do
  let lctx := localsFor infos
  let .error (.alreadyDeclared _ name) :=
    declareRecursors (statsFor types) types .zero infos [] lctx false false { ctx with lctx }
    | throwError "expected recursor freshness rejection"
  unless name == expected do throwError "incorrect recursor collision name {name}"

private def checkedStage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Level × Array RecInfo × LocalContext × Bool × Bool × Context × Kernel.Environment) :=
  checkInductiveTypes nparams types fun stats => do
    let isUnsafe := (← readThe Context).safety != .safe
    withEnv (← declareInductiveTypes stats nparams types 0 isUnsafe) do
      checkConstructors types stats isUnsafe
      withEnv (← declareConstructors stats types isUnsafe) do
        let elimLevel ← getElimLevel stats types
        mkRecInfos stats types elimLevel fun infos => do
          let lctx ← getLCtx
          let isK ← isKTarget stats types
          let source ← readThe Context
          let env ← declareRecursors stats types elimLevel infos source.lparams lctx isK isUnsafe
          return (stats, elimLevel, infos, lctx, isK, isUnsafe, source, env)

private def closeParams (nparams : Nat) (body : Expr) : Expr :=
  nparams.fold (fun _ _ body => .forallE `parameter (.sort (.succ .zero)) body .default) body

private def checkedHeader (name : Name) (nparams : Nat) (ctors : List Constructor) : InductiveType := {
  name, type := closeParams nparams (.sort (.succ .zero)), ctors }

private def checkRuleConstructors (types : Array InductiveType) (env : Kernel.Environment) : MetaM Unit := do
  for type in types do
    let some (.recInfo recursor) := env.find? (mkRecName type.name)
      | throwError "missing field-alignment recursor"
    unless recursor.rules.length == type.ctors.length do throwError "incorrect field-alignment rule count"
    for index in [:type.ctors.length] do
      let ctor := type.ctors[index]!
      let rule := recursor.rules[index]!
      let some (.ctorInfo info) := env.find? ctor.name | throwError "missing field-alignment constructor"
      unless rule.ctor == info.name && rule.nfields == info.numFields do
        throwError "rule field count differs from the registered constructor"

private def checkChecked (ctx : Context) (nparams : Nat) (types : Array InductiveType) : MetaM Unit := do
  let .ok (stats, elimLevel, infos, lctx, isK, isUnsafe, source, env) := checkedStage nparams types ctx
    | throwError "checked recursor fixture unexpectedly failed"
  let .ok full := AddInductive.run nparams types.toList 0 ctx
    | throwError "complete recursor fixture unexpectedly failed"
  let expectedParams := if types.isEmpty then 0 else nparams
  unless stats.params.size == expectedParams && infos.size == types.size &&
      (infos.flatMap (·.minors)).size == (types.toList.flatMap (·.ctors)).length do
    throwError "checked fixture does not supply the count-alignment premises"
  checkMinorIndexing types infos
  let mut minorIndex := 0
  for index in [:types.size] do
    unless infos[index]!.indices.size == stats.nindices[index]! do
      throwError "checked fixture does not align recursor and datatype indices"
    let nextIndex ← checkExact source stats types elimLevel infos source.lparams lctx isK isUnsafe env index minorIndex
    let fullNextIndex ← checkExact source stats types elimLevel infos source.lparams lctx isK isUnsafe full index minorIndex
    unless nextIndex == fullNextIndex do throwError "complete run changed rule-state advancement"
    minorIndex := nextIndex
  for name in [``Nat, ``Nat.rec, ``List, ``List.rec] do
    checkPreserved source.env env name
    checkPreserved source.env full name
  checkRuleConstructors types env
  checkRuleConstructors types full

private def audit (theoremName : Name) (mapInterfaces := true) (instantiation := false) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound] ++ if mapInterfaces then [
    ``Lean.PersistentHashMap.findAux_isSome, ``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentHashMap.WF.toList'_insert] else []
  let allowed := allowed ++ if instantiation then [``Expr.instantiate1_eq] else []
  for axiomName in axioms do
    unless allowed.contains axiomName do throwError "unexpected axiom {axiomName} in {theoremName}"

private def auditTheorems : MetaM Unit := do
  audit ``declareRecursors.preserves
  audit ``declareRecursors.metadata
  audit ``InductiveStats.RecursorMetadata.sourceRules false
  audit ``InductiveStats.RecursorMetadata.declaredCounts false
  audit ``RecursorRuleShape.count false
  audit ``mkRecRules.shape false
  audit ``InductiveStats.RecursorMetadata.ruleShape false
  audit ``InductiveStats.RecursorMetadata.orderedRules false
  audit ``recursorMinorOffset.zero false
  audit ``recursorMinorOffset.succ false
  audit ``recursorMinorOffset.total false
  audit ``InductiveStats.RecursorOffsetMetadata.metadata false
  audit ``InductiveStats.RecursorOffsetMetadata.sourceRules false
  audit ``declareRecursors.offsetMetadata
  audit ``mkRecInfos.loopCtorArgs.fields false true
  audit ``RecursorRuleFields.at false
  audit ``mkRecRules.fieldCounts false true
  audit ``InductiveStats.RecursorMetadata.ruleFields false true
  audit ``RecursorInfoCounts.minorPrefix false
  audit ``RecursorInfoCounts.minorIndexing false
  audit ``RecursorMinorIndexing.at false
  audit ``RecursorMinorIndexing.getElem! false
  audit ``RecursorRuleRhs.count false
  audit ``RecursorRuleRhs.at false
  audit ``mkRecRules.rhs false
  audit ``InductiveStats.RecursorOffsetMetadata.localRuleRhs false
  audit ``mkRecInfos.loopCtorArgs.recursiveFields false
  audit ``mkRecRules.loopU.counts false
  audit ``RecursorRuleRhsCountReceipt.receipt false
  audit ``RecursorRuleRhsCountReceipt.argumentBound false
  audit ``RecursorRuleRhsCounts.rhs false
  audit ``RecursorRuleRhsCounts.at false
  audit ``mkRecRules.rhsCounts false
  audit ``InductiveStats.RecursorOffsetMetadata.localRuleRhsCounts false
  audit ``RecursorFieldsAreFVars.push false
  audit ``RecursorFieldsAreFVars.sublist false
  audit ``mkRecInfos.loopCtorArgs.fvars false
  audit ``RecursorRuleRhsFVarReceipt.counts false
  audit ``RecursorRuleRhsFVarReceipt.shapes false
  audit ``RecursorRuleRhsFVars.counts false
  audit ``RecursorRuleRhsFVars.at false
  audit ``mkRecRules.rhsFVars false
  audit ``InductiveStats.RecursorOffsetMetadata.localRuleRhsFVars false

run_meta
  auditTheorems
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  checkArgumentCountFixtures ctx
  checkFieldShapeFixtures ctx
  let natType := Expr.const ``Nat []
  let sortType := Expr.sort (.succ .zero)
  let parameter := Expr.fvar ⟨`FieldParameter⟩
  let otherParameter := Expr.fvar ⟨`OtherFieldParameter⟩
  let oneField := Expr.forallE `value natType natType .default
  let withParameter := Expr.forallE `parameter sortType oneField .default
  checkRawFields ctx #[] natType 0
  checkRawFields ctx #[] oneField 1
  checkRawFields ctx #[parameter] withParameter 1
  checkRawFields ctx #[parameter, otherParameter] withParameter 0
  checkRawFields ctx #[parameter, otherParameter] oneField 0
  let mixed := Expr.forallE `first natType (.forallE `second natType
    (.forallE `third natType natType .strictImplicit) .instImplicit) .implicit
  checkRawFields ctx #[] mixed 3
  let manyFields := (List.range 33).foldr
    (fun ordinal body => .forallE ((`field).appendIndexAfter ordinal) natType body .default) natType
  checkRawFields ctx #[] manyFields 33
  let .error .deepRecursion := fieldStage #[] natType
      { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "field-count traversal must propagate zero-fuel rejection"
  let expands := Expr.forallE `parameter sortType (.bvar 0) .default
  let invalidParams := #[oneField]
  let .ok expandedFields := fieldStage invalidParams expands ctx
    | throwError "non-free-variable parameter control failed"
  unless expandedFields == 1 &&
      expandedFields != declareConstructors.arity 0 expands - invalidParams.size do
    throwError "field-count theorem must retain its free-variable parameter premise"
  logInfo "seven raw field-count fixtures, one fuel boundary, and a non-free-variable parameter control passed"
  let first := typeFor `RecursorPreservedFirst [`RecursorPreservedFirst.left, `RecursorPreservedFirst.right]
  let empty := typeFor `RecursorPreservedEmpty []
  let last := typeFor `RecursorPreservedLast [`RecursorPreservedLast.last]
  let types := #[first, empty, last]
  let firstInfo := infoFor first.name #[`minorLeft, `minorRight]
  let emptyInfo := infoFor empty.name #[]
  let lastInfo := infoFor last.name #[`minorLast]
  let infos := #[firstInfo, emptyInfo, lastInfo]
  checkRhsMinorControl ctx types infos 0 0 1
  logInfo "positional RHS receipt distinguishes a deliberately swapped local minor"
  checkRuleSourceShape ctx types infos 0 0
  checkRuleSourceShape ctx types infos 0 1
  checkRuleSourceShape ctx types infos 2 0
  checkRuleSourceShape ctx types infos 2 2
  let zeroFuel := { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
  checkRuleSourceShape zeroFuel types infos 1 0
  checkRuleSourceShape zeroFuel types infos 1 17
  let reversed := typeFor first.name [`RecursorPreservedFirst.right, `RecursorPreservedFirst.left]
  checkRuleSourceShape ctx #[reversed, empty, last] infos 0 0
  let repeated := typeFor first.name [`RecursorPreservedFirst.left, `RecursorPreservedFirst.left]
  checkRuleSourceShape ctx #[repeated, empty, last] infos 0 0
  logInfo "eight direct rule-source name/order/count/state fixtures passed"
  let emptyFirst := typeFor `OffsetEmptyFirst []
  let emptyLast := typeFor `OffsetEmptyLast []
  let emptyFirstInfo := infoFor emptyFirst.name #[]
  let emptyLastInfo := infoFor emptyLast.name #[]
  checkSuccess ctx #[emptyFirst, last, empty, first, emptyLast]
    #[emptyFirstInfo, lastInfo, emptyInfo, firstInfo, emptyLastInfo] [] .zero false false
  checkSuccess ctx #[last, empty, first] #[lastInfo, emptyInfo, firstInfo] [] .zero false false
  checkSuccess ctx #[first, empty, emptyFirst, last]
    #[firstInfo, emptyInfo, emptyFirstInfo, lastInfo] [] .zero false false
  checkSuccess zeroFuel #[emptyFirst, emptyLast] #[emptyFirstInfo, emptyLastInfo] [] .zero false false
  let numbered := typeFor `OffsetNumbered ((List.range 33).map fun ordinal =>
    (`OffsetNumbered.ctor).appendIndexAfter ordinal)
  let numberedInfo := infoFor numbered.name ((List.range 33).map fun ordinal =>
    (`offsetMinor).appendIndexAfter ordinal).toArray
  checkMinorIndexing #[] #[]
  checkMinorIndexing #[emptyFirst, empty, emptyLast] #[emptyFirstInfo, emptyInfo, emptyLastInfo]
  checkMinorIndexing types infos
  checkMinorIndexing #[last, empty, first] #[lastInfo, emptyInfo, firstInfo]
  checkMinorIndexing #[emptyFirst, last, empty, first, emptyLast]
    #[emptyFirstInfo, lastInfo, emptyInfo, firstInfo, emptyLastInfo]
  checkMinorIndexing #[numbered] #[numberedInfo]
  checkMinorIndexing #[last, emptyFirst, numbered, emptyLast, first]
    #[lastInfo, emptyFirstInfo, numberedInfo, emptyLastInfo, firstInfo]
  let repeatedInfo := { firstInfo with minors := #[natType, natType] }
  checkMinorIndexing #[first, empty, last] #[repeatedInfo, emptyInfo, { lastInfo with minors := #[natType] }]
  let wrongCounts := #[{ firstInfo with minors := #[natType] },
    { emptyInfo with minors := #[natType] }, lastInfo]
  unless (wrongCounts.flatMap (·.minors)).size == (infos.flatMap (·.minors)).size &&
      (wrongCounts.flatMap (·.minors))[1]? != wrongCounts[0]!.minors[1]? do
    throwError "aggregate count control must fail local indexing"
  unless (infos.flatMap (·.minors))[first.ctors.length]? != firstInfo.minors[first.ctors.length]? do
    throwError "lookup control must retain the constructor-local bound"
  logInfo "eight minor-indexing fixtures, saturated prefixes, and two invalid-bound/count controls passed"
  checkSuccess ctx #[numbered] #[numberedInfo] [] .zero false false
  for allowPrimitive in [false, true] do
    for isK in [false, true] do
      for isUnsafe in [false, true] do
        let current := { ctx with allowPrimitive, safety := if isUnsafe then .unsafe else .safe }
        checkSuccess current #[] #[] [] .zero isK isUnsafe
        checkSuccess current #[empty] #[emptyInfo] [] .zero isK isUnsafe
        checkSuccess current types infos [`v] (.param `u) isK isUnsafe
  checkSuccess { ctx with safety := .unsafe } types infos [] .zero false false
  checkCollision ctx #[typeFor ``Nat []] #[emptyInfo] ``Nat.rec
  checkCollision ctx #[empty, typeFor ``Nat []] #[emptyInfo, lastInfo] ``Nat.rec
  checkCollision ctx #[empty, empty] #[emptyInfo, lastInfo] (mkRecName empty.name)
  let lctx := localsFor infos
  let .error .deepRecursion := declareRecursors (statsFor types) types .zero infos [] lctx false false
      { ctx with lctx, fuel := { ctx.fuel with inductiveFuel := 0 } }
    | throwError "rule-generation failure must propagate before registration"
  checkSuccess { ctx with fuel := { ctx.fuel with inductiveFuel := 0 } }
    #[empty] #[emptyInfo] [] .zero false false
  logInfo "31 successful recursor traversals with exact prefix offsets, three freshness rejections, and one rule-generation failure passed"
  let natType := Expr.const ``Nat []
  let zero := Expr.const `CheckedMetaZero []
  let one := Expr.const `CheckedMetaOne []
  let other := Expr.const `CheckedMetaOther []
  let two := Expr.const `CheckedMetaTwo []
  let base : Constructor := { name := `CheckedMetaZero.base, type := zero }
  let recursive : Constructor := {
    name := `CheckedMetaZero.tail, type := .forallE `tail zero zero .default }
  let higher : Constructor := {
    name := `CheckedMetaZero.higher
    type := .forallE `function (.forallE `index natType zero .default) zero .implicit }
  let parameterOnly : Constructor := {
    name := `CheckedMetaOne.base, type := closeParams 1 (.app one (.bvar 0)) }
  let parameterField : Constructor := {
    name := `CheckedMetaOne.value
    type := closeParams 1 (.forallE `value (.bvar 0) (.app one (.bvar 1)) .default) }
  let parameterRecursive : Constructor := {
    name := `CheckedMetaOne.tail
    type := closeParams 1 (.forallE `tail (.app one (.bvar 0)) (.app one (.bvar 1)) .default) }
  let mutualCtor : Constructor := {
    name := `CheckedMetaOne.mutual
    type := closeParams 1 (.forallE `value (.app other (.bvar 0)) (.app one (.bvar 1)) .default) }
  let otherBase : Constructor := {
    name := `CheckedMetaOther.base, type := closeParams 1 (.app other (.bvar 0)) }
  let twoBase : Constructor := {
    name := `CheckedMetaTwo.base, type := closeParams 2 (.mkAppList two [.bvar 1, .bvar 0]) }
  let mutualTypes := #[checkedHeader `CheckedMetaOne 1 [parameterOnly, mutualCtor],
    checkedHeader `CheckedMetaOther 1 [otherBase]]
  checkChecked ctx 0 #[]
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 []]
  checkChecked ctx 0 #[{
    name := `CheckedMetaProp, type := .sort .zero,
    ctors := [{ name := `CheckedMetaProp.intro, type := .const `CheckedMetaProp [] }] }]
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 [base, recursive, higher]]
  let mixedFields := [natType, zero, natType, .forallE `index natType zero .default, zero].foldr
    (fun domain body => .forallE `field domain body .implicit) zero
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 [{ name := `CheckedMetaZero.mixed, type := mixedFields }]]
  let manyRecursive := (List.range 33).foldr
    (fun _ body => .forallE `recursive zero body .default) zero
  checkChecked ctx 0 #[checkedHeader `CheckedMetaZero 0 [{ name := `CheckedMetaZero.manyRecursive, type := manyRecursive }]]
  checkChecked ctx 1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterField, parameterRecursive]]
  checkChecked ctx 2 #[checkedHeader `CheckedMetaTwo 2 [twoBase]]
  let parameterFields := (List.range 33).foldr
    (fun ordinal body => .forallE ((`field).appendIndexAfter ordinal) natType body
      (if ordinal % 2 == 0 then .implicit else .default)) (.app one (.bvar 33))
  checkChecked ctx 1 #[checkedHeader `CheckedMetaOne 1 [{
    name := `CheckedMetaOne.manyFields, type := closeParams 1 parameterFields }]]
  checkChecked ctx 1 mutualTypes
  let indexed := Expr.const `CheckedMetaIndexed []
  checkChecked ctx 1 #[{
    name := `CheckedMetaIndexed
    type := closeParams 1 (.forallE `index natType (.sort (.succ .zero)) .default)
    ctors := [{
      name := `CheckedMetaIndexed.base
      type := closeParams 1
        (.forallE `index natType (.mkAppList indexed [.bvar 1, .bvar 0]) .default) }] }]
  checkChecked { ctx with
    ngen := { namePrefix := `MetadataSeed, idx := 17 }
    lctx := ctx.lctx.mkLocalDecl ⟨`ExistingLocal⟩ `Existing natType }
    1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterRecursive]]
  let polyLevel := Level.param `u
  let polySort := Expr.sort (.succ polyLevel)
  let polyHead := Expr.const `CheckedMetaPoly [polyLevel]
  checkChecked { ctx with lparams := [`u] } 1 #[{
    name := `CheckedMetaPoly
    type := .forallE `A polySort polySort .default
    ctors := [{
      name := `CheckedMetaPoly.base
      type := .forallE `A polySort (.app polyHead (.bvar 0)) .default }] }]
  let negative : Constructor := {
    name := `CheckedMetaZero.negative
    type := .forallE `function (.forallE `value zero natType .default) zero .default }
  checkChecked { ctx with safety := .unsafe } 0 #[checkedHeader `CheckedMetaZero 0 [negative]]
  checkChecked { ctx with allowPrimitive := true } 1 mutualTypes
  checkChecked { ctx with fuel := { ctx.fuel with inductiveFuel := 3 } }
    1 #[checkedHeader `CheckedMetaOne 1 [parameterOnly, parameterRecursive]]
  logInfo "16 checked and complete recursor fixtures passed exact records, counted free-variable RHS receipts, prefix offsets, minor indexing, and registered constructor field counts"

end RecursorRegistrationTest
