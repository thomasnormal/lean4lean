import Lean4Lean.Verify.InductiveNativeTelescopeArguments
import Lean4Lean.Verify.RecursorFieldScope
import Lean4Lean.Verify.InductiveHeaderParameterApplications
import Lean4Lean.Verify.InductiveParameterPrefixReplacement

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved TypedParameterApplications)

/- The scoped receipt is the form produced by the checked recursor pass.  The
   constructor-RHS consumer needs the smaller receipt that retains only the
   native rule shape; carry it through the existing fvar and count views
   without reconstructing any fields, values, or context equalities. -/
theorem LocalRecursorRuleRhsScope.atReceipt
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env)
    (parent : Nat) (hparent : parent < types.size)
    (index : Nat) (ctor : Constructor) (hctor : types[parent]!.ctors[index]? = some ctor) :
    ∃ recursor, env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∃ rule minor, recursor.rules[index]? = some rule ∧
        infos[parent]!.minors[index]? = some minor ∧
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule := by
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨recursor, hfind, rule, minor, hrule, hminor, hreceipt.fvars.counts.receipt⟩

theorem LocalRecursorRuleRhsScope.receipts
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env) :
    LocalRecursorRuleRhs stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hreceipt.fvars.counts.receipt⟩

/- Keep the local recursor lookup and minor alignment while letting a consumer
   state its per-rule contract over the ordinary receipt. -/
theorem LocalRecursorRuleRhsScope.impReceipts
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : Kernel.Environment}
    {relation : Nat → RecursorVal → Nat → Constructor → RecursorRule → Expr → Prop}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
        ctx ctor minor rule → relation parent recursor index ctor rule minor) :
    ∀ parent, parent < types.size → ∃ recursor,
      env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          relation parent recursor index ctor rule minor := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor,
    head parent recursor index ctor rule minor hreceipt.fvars.counts.receipt⟩

/- Some result consumers need the stronger scoped receipt as well as its
   ordinary projection; pass both views without rebuilding either witness. -/
theorem LocalRecursorRuleRhsScope.impScopedReceipts
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {env : Kernel.Environment}
    {relation : Nat → RecursorVal → Nat → Constructor → RecursorRule → Expr → Prop}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule → relation parent recursor index ctor rule minor) :
    ∀ parent, parent < types.size → ∃ recursor,
      env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          relation parent recursor index ctor rule minor := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor,
    head parent recursor index ctor rule minor hreceipt hreceipt.fvars.counts.receipt⟩

/- Package the dual receipt views with the semantic rule-body witness expected
   by the later recursor registration consumer. -/
theorem LocalRecursorRuleRhsScope.ruleSemantics
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    {env : VEnv} {universes : List Name}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
            ctx ctor minor rule ∧
          RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
            ctx ctor minor rule ∧
          ∃ semantic, TrExprS env universes [] rule.rhs semantic := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  have ordinaryReceipt := hreceipt.fvars.counts.receipt
  obtain ⟨semantic, translated⟩ := head parent recursor index ctor rule minor hreceipt ordinaryReceipt
  exact ⟨rule, minor, hrule, hminor, hreceipt, ordinaryReceipt, semantic, translated⟩

/- Indexed receipts cover every stored rule only when the rule list has the
   exact constructor count.  Registration supplies this additional invariant;
   the local scope alone deliberately does not assert it. -/
theorem LocalRecursorRuleRhsScope.completeRuleSemantics
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    {env : VEnv} {universes : List Name}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (ordered : OrderedRecursorRules types kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic := by
  intro parent bound
  obtain ⟨recursor, lookup, entries⟩ := hscope parent bound
  obtain ⟨stored, storedLookup, _, count⟩ := ordered parent bound
  have same : recursor = stored := ConstantInfo.recInfo.inj (Option.some.inj (lookup.symm.trans storedLookup))
  subst stored
  refine ⟨recursor, lookup, ?_⟩
  intro rule member
  obtain ⟨index, indexBound, atIndex⟩ := List.mem_iff_getElem.mp member
  have ctorBound : index < types[parent]!.ctors.length := by omega
  have ctorLookup : types[parent]!.ctors[index]? = some types[parent]!.ctors[index] :=
    List.getElem?_eq_getElem ctorBound
  obtain ⟨matched, minor, ruleLookup, _, receipt⟩ := entries index _ ctorLookup
  have sameRule : matched = rule := by
    exact Option.some.inj (ruleLookup.symm.trans
      ((List.getElem?_eq_getElem indexBound).trans (congrArg some atIndex)))
  subst matched
  exact head parent recursor index _ rule minor receipt receipt.fvars.counts.receipt

/-- Project every scoped constructor rule in one aligned rule list to the
   ordinary receipt relation.  The constructor/index alignment and stored rule
   order are inherited directly from `List.Forall₂`; no rule is reconstructed
   from its expression. -/
theorem RecursorRuleRhsScope.receipts
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial) :
    RecursorRuleRhs stats motives minors ctx ctors rules initial := by
  exact List.Forall₂.imp (fun _ _ head => head.fvars.counts.receipt) hscope

/- An indexed all-rule lookup can cross the same scoped-to-ordinary receipt
   boundary without asking the caller to destruct the aligned list. -/
theorem RecursorRuleRhsScope.atReceipt
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial index : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsReceipt stats motives minors ctx ctor minors[initial + index]! rule := by
  obtain ⟨rule, hrule, hreceipt⟩ := hscope.at index ctor hctor
  exact ⟨rule, hrule, hreceipt.fvars.counts.receipt⟩

/- Let an all-rule consumer work with ordinary receipts while the caller keeps
   the stronger scoped alignment as its source invariant. -/
theorem RecursorRuleRhsScope.impReceipts
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    {relation : Constructor × Nat → RecursorRule → Prop}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        relation entry rule) :
    List.Forall₂ relation (ctors.zipIdx initial) rules := by
  exact List.Forall₂.imp (fun entry rule hreceipt =>
    head entry rule hreceipt.fvars.counts.receipt) hscope

/- Preserve both receipt views for all-rule consumers that need scoped context
   witnesses alongside the ordinary RHS relation. -/
theorem RecursorRuleRhsScope.impScopedReceipts
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    {relation : Constructor × Nat → RecursorRule → Prop}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        relation entry rule) :
    List.Forall₂ relation (ctors.zipIdx initial) rules := by
  exact List.Forall₂.imp (fun entry rule hreceipt =>
    head entry rule hreceipt (hreceipt.fvars.counts.receipt)) hscope

/- The generated constructor-RHS producer returns a large dependent package.
   Name that package so an all-rule consumer can retain every witness while
   still using the aligned scoped receipt as its source invariant. -/
abbrev GeneratedConstructorRuleRhsResult
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {constructor : Constructor} {motives minors : Array Expr} {ctx : Context}
    {minor : Expr} {rule : RecursorRule} : Prop :=
  ∃ (infos : Array RecInfo) (domainReader : Context) (domain : Expr) (ids : List FVarId)
    (final base target : MLCtx) (count : Nat) (arguments : List VExpr)
    (resultType : VExpr) (insertionLift : Lift) (peeled minorSemantic : VExpr)
    (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
    (replacements : List Expr) (replacementTerminal : Expr)
    (values : List VExpr) (bodySemantic rhsSemantic rhsType : VExpr),
    IndexMLCtxExtension base ids final ∧
    VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0 ∧
    peelTypeAnnotations domain =
      fieldModel.lctx.mkForall fields
        (domainReader.lctx.mkForall hypotheses
          (recursorMinorBody stats infos constructor terminal fields)) ∧
    NativeTelescopeArguments env universes final
      (fieldModel.lctx.mkForall fields
        (domainReader.lctx.mkForall hypotheses
          (recursorMinorBody stats infos constructor terminal fields)))
      (fields.toList ++ replacements) replacementTerminal ∧
    TypedParameterApplications env universes final peeled
      (fields.toList ++ replacements) values bodySemantic ∧
    TrExprS env universes final.vlctx
      (minor.mkAppList (fields.toList ++ replacements))
      (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
    env.HasType universes.length final.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments minorSemantic values) bodySemantic ∧
    TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray)
      (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
    TrExprS env universes base.vlctx rule.rhs rhsSemantic ∧
    env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType ∧
    env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType ∧
    TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
    env.HasType universes.length base.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
    env.SortArity universes.length base.vlctx.toCtx count resultType ∧
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count
      (resultType.lift' insertionLift)

/- Named relation for callers that feed the concrete generated package into
   the generic registration CPS theorem. -/
abbrev GeneratedRecursorRuleResult
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (motives minors : Array Expr) (ctx : Context) (constructor : Constructor)
    (minor : Expr) (rule : RecursorRule) : Prop :=
  GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
    (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
    (constructor := constructor) (minor := minor) (rule := rule)

abbrev GeneratedRecursorRuleResultSemantics
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (motives minors : Array Expr) (ctx : Context) (constructor : Constructor)
    (minor : Expr) (rule : RecursorRule) : Prop :=
  (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
    GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule

/- The generated package contains several layers of constructor-body bookkeeping.
   Registration consumers that are checking the recursor iota step need only the
   RHS receipt and the base/target applied translations.  Keep those witnesses
   in a named projection so consumers do not have to destructure the complete
   dependent package (and accidentally discard its explicit sort-arity facts). -/
abbrev GeneratedRecursorRuleIotaKind
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (motives minors : Array Expr) (ctx : Context) (constructor : Constructor)
    (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (base target : MLCtx) (count : Nat) (arguments : List VExpr)
    (resultType : VExpr) (insertionLift : Lift) (replacements : List Expr)
    (rhsSemantic rhsType : VExpr),
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
    TrExprS env universes base.vlctx rule.rhs rhsSemantic ∧
    env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType ∧
    env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType ∧
    TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
    env.HasType universes.length base.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
    env.SortArity universes.length base.vlctx.toCtx count resultType ∧
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count
      (resultType.lift' insertionLift)

theorem GeneratedConstructorRuleRhsResult.iotaKind
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
      (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
      (constructor := constructor) (minor := minor) (rule := rule)) :
    GeneratedRecursorRuleIotaKind env universes stats motives minors ctx constructor minor rule := by
  rcases result with ⟨infos, domainReader, domain, ids, final, base, target, count,
    arguments, resultType, insertionLift, peeled, minorSemantic, fieldModel, terminal,
    fields, hypotheses, replacements, replacementTerminal, values, bodySemantic,
    rhsSemantic, rhsType, extension, insertion, sourceEq, nativeArguments,
    typedArguments, bodyTranslated, bodyTyped, nestedTranslated, ruleReceipt,
    rhsTranslated, rhsTyped,
    rhsKind, baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated,
    resultTyped, resultKind⟩
  exact ⟨base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped, rhsKind,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated,
    resultTyped, resultKind⟩

/- Consumers that check the final recursor application need only the target-side
   translated expression and its terminal type/kind.  Keep this endpoint named
   so they do not have to reopen the complete generated constructor package. -/
abbrev GeneratedRecursorRuleIotaTargetResult
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (motives minors : Array Expr) (ctx : Context) (constructor : Constructor)
    (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
    (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift)))
      (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count
      (resultType.lift' insertionLift)

theorem GeneratedRecursorRuleIotaKind.targetResult
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (iota : GeneratedRecursorRuleIotaKind env universes stats motives minors ctx constructor minor rule) :
    GeneratedRecursorRuleIotaTargetResult env universes stats motives minors ctx constructor minor rule := by
  rcases iota with ⟨base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped, rhsKind,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated,
    resultTyped, resultKind⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    resultTranslated, resultTyped, resultKind⟩

theorem GeneratedRecursorRuleIotaKind.baseResult
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (iota : GeneratedRecursorRuleIotaKind env universes stats motives minors ctx constructor minor rule) :
    ∃ (base : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType := by
  rcases iota with ⟨base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped, rhsKind,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated,
    resultTyped, resultKind⟩
  exact ⟨base, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    baseResultTranslated, baseResultTyped, baseResultKind⟩

/- Preserve the shared witnesses when a consumer needs both pre-lift and
   target-side endpoints together. -/
abbrev GeneratedRecursorRuleIotaBaseAndTargetResults
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (motives minors : Array Expr) (ctx : Context) (constructor : Constructor)
    (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (base target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
    (insertionLift : Lift) (replacements : List Expr) (rhsSemantic rhsType : VExpr),
    TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
    env.HasType universes.length base.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
    env.SortArity universes.length base.vlctx.toCtx count resultType ∧
    TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
    env.HasType universes.length target.vlctx.toCtx
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) (resultType.lift' insertionLift) ∧
    env.SortArity universes.length target.vlctx.toCtx count (resultType.lift' insertionLift)

theorem GeneratedRecursorRuleIotaKind.baseAndTargetResults
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (iota : GeneratedRecursorRuleIotaKind env universes stats motives minors ctx constructor minor rule) :
    GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
      constructor minor rule := by
  rcases iota with ⟨base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped, rhsKind,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated,
    resultTyped, resultKind⟩
  exact ⟨base, target, count, arguments, resultType, insertionLift, replacements, rhsSemantic, rhsType,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated, resultTyped, resultKind⟩

/- Keep the complete generated constructor-RHS package together with the
   paired pre-lift and target iota endpoint. -/
theorem GeneratedConstructorRuleRhsResult.resultAndIota
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
      (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
      (constructor := constructor) (minor := minor) (rule := rule)) :
    GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        constructor minor rule :=
  ⟨result, GeneratedRecursorRuleIotaKind.baseAndTargetResults result.iotaKind⟩

/- Explicitly name the paired base/target endpoint exposed by the complete
   generated constructor-RHS result. -/
theorem GeneratedConstructorRuleRhsResult.resultAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
      (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
      (constructor := constructor) (minor := minor) (rule := rule)) :
    GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        constructor minor rule := by
  exact result.resultAndIota


/- Canonical same-witness pairing for consumers that already hold the full
   generated recursor-rule result. -/
theorem GeneratedRecursorRuleResult.resultAndIota
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule) :
    GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        constructor minor rule :=
  ⟨result, GeneratedRecursorRuleIotaKind.baseAndTargetResults result.iotaKind⟩

/- Explicitly name the paired base/target endpoint exposed by a complete
   generated recursor-rule result. -/
theorem GeneratedRecursorRuleResult.resultAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (result : GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule) :
    GeneratedRecursorRuleResult env universes stats motives minors ctx constructor minor rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        constructor minor rule := by
  exact result.resultAndIota


/- Named eliminators for the paired endpoint let consumers select one side
   without reopening the full generated-rule receipt. -/
theorem GeneratedRecursorRuleIotaBaseAndTargetResults.baseResult
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (results : GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
      ctx constructor minor rule) :
    ∃ (base : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic rhsType : VExpr),
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType := by
  rcases results with ⟨base, _target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, baseTranslated, baseTyped, baseKind, _targetTranslated,
    _targetTyped, _targetKind⟩
  exact ⟨base, count, arguments, resultType, insertionLift, replacements, rhsSemantic, rhsType,
    baseTranslated, baseTyped, baseKind⟩

theorem GeneratedRecursorRuleIotaBaseAndTargetResults.targetResult
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (results : GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
      ctx constructor minor rule) :
    GeneratedRecursorRuleIotaTargetResult env universes stats motives minors ctx constructor minor rule := by
  rcases results with ⟨_base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, _rhsType, _baseTranslated, _baseTyped, _baseKind, targetTranslated,
    targetTyped, targetKind⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    targetTranslated, targetTyped, targetKind⟩

/- Named eliminators expose the individual target obligations to consumers that
   only need the translated RHS, terminal typing, or sort information. -/
theorem GeneratedRecursorRuleIotaTargetResult.translated
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (targetResult : GeneratedRecursorRuleIotaTargetResult env universes stats motives minors
      ctx constructor minor rule) :
    ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) := by
  rcases targetResult with ⟨target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, translated, _typed, _sortArity⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic, translated⟩

theorem GeneratedRecursorRuleIotaTargetResult.hasType
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (targetResult : GeneratedRecursorRuleIotaTargetResult env universes stats motives minors
      ctx constructor minor rule) :
    ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) := by
  rcases targetResult with ⟨target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, _translated, typed, _sortArity⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic, typed⟩

theorem GeneratedRecursorRuleIotaTargetResult.sortArity
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    (targetResult : GeneratedRecursorRuleIotaTargetResult env universes stats motives minors
      ctx constructor minor rule) :
    ∃ (target : MLCtx) (count : Nat) (arguments : List VExpr) (resultType : VExpr)
      (insertionLift : Lift) (replacements : List Expr) (rhsSemantic : VExpr),
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  rcases targetResult with ⟨target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, _translated, _typed, sortArity⟩
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic, sortArity⟩

/- Lift the explicit generated constructor-RHS package through every aligned
   rule.  The callback remains the producer/consumer boundary: it supplies
   the minor step, opening, extension, and context premises needed to obtain
   the package, while this theorem preserves constructor/index and rule order. -/
theorem RecursorRuleRhsScope.impGeneratedConstructorRuleRhs
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule))
      (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts head

/- The indexed local form keeps the recursor and minor lookups in addition to
   the explicit generated result package. -/
theorem LocalRecursorRuleRhsScope.impGeneratedConstructorRuleRhs
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
            (stats := stats) (motives := infos.map (·.motive))
            (minors := infos.flatMap (·.minors)) (ctx := ctx)
            (constructor := ctor) (minor := minor) (rule := rule) := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor,
    head parent recursor index ctor rule minor hreceipt (hreceipt.fvars.counts.receipt)⟩

/- The generated-result consumer needs the same exact stored-rule coverage as
   `completeRuleSemantics`, while retaining the constructor, minor, and source
   index that determine the dependent package.  Ordered recursor rules supplies
   the length agreement needed to recover that indexed witness from list
   membership. -/
theorem LocalRecursorRuleRhsScope.completeRuleResultSemantics
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    {env : VEnv} {universes : List Name}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (ordered : OrderedRecursorRules types kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
      (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ rule ∈ recursor.rules, ∃ (index : Nat) (ctor : Constructor) (minor : Expr)
        (semantic : VExpr),
        types[parent]!.ctors[index]? = some ctor ∧
        infos[parent]!.minors[index]? = some minor ∧
        recursor.rules[index]? = some rule ∧
        TrExprS env universes [] rule.rhs semantic ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule) := by
  intro parent bound
  obtain ⟨recursor, lookup, entries⟩ := hscope parent bound
  obtain ⟨stored, storedLookup, _, count⟩ := ordered parent bound
  have same : recursor = stored := ConstantInfo.recInfo.inj
    (Option.some.inj (lookup.symm.trans storedLookup))
  subst stored
  refine ⟨recursor, lookup, ?_⟩
  intro rule member
  obtain ⟨index, indexBound, atIndex⟩ := List.mem_iff_getElem.mp member
  have ctorBound : index < types[parent]!.ctors.length := by omega
  have ctorLookup : types[parent]!.ctors[index]? = some types[parent]!.ctors[index] :=
    List.getElem?_eq_getElem ctorBound
  obtain ⟨matched, minor, ruleLookup, minorLookup, receipt⟩ :=
    entries index _ ctorLookup
  have sameRule : matched = rule := by
    exact Option.some.inj (ruleLookup.symm.trans
      ((List.getElem?_eq_getElem indexBound).trans (congrArg some atIndex)))
  subst matched
  obtain ⟨⟨semantic, translated⟩, generated⟩ := head parent recursor index _ rule minor receipt
    receipt.fvars.counts.receipt
  exact ⟨index, _, minor, semantic, ctorLookup, minorLookup, ruleLookup, translated, generated⟩

/- Named-result wrappers avoid unfolding the generated package at each caller. -/
theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResult
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResult env universes stats motives minors ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule => GeneratedRecursorRuleResult env universes stats motives minors ctx
      entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules := by
  exact hscope.impGeneratedConstructorRuleRhs (fun entry rule scopedReceipt ordinaryReceipt =>
    head entry rule scopedReceipt ordinaryReceipt)

theorem RecursorRuleRhsScope.impGeneratedRecursorRuleIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
          ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule => GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
      motives minors ctx entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts (fun entry rule scopedReceipt ordinaryReceipt =>
    head entry rule scopedReceipt ordinaryReceipt)

/- Pair the complete generated result with its iota endpoint while traversing
   the same scoped and ordinary rule receipts. -/
theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResultAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResult env universes stats motives minors ctx entry.1 minors[entry.2]! rule ∧
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
          ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResult env universes stats motives minors ctx entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts (fun entry rule scopedReceipt ordinaryReceipt =>
    head entry rule scopedReceipt ordinaryReceipt)

/- Explicitly name the paired base/target endpoint in the scoped traversal. -/
theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResultAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResult env universes stats motives minors ctx entry.1 minors[entry.2]! rule ∧
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
          ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResult env universes stats motives minors ctx entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules := by
  exact hscope.impGeneratedRecursorRuleResultAndIota head


theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResult
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule := by
  exact hscope.impGeneratedConstructorRuleRhs
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
      head parent recursor index ctor rule minor scopedReceipt ordinaryReceipt)

theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule := by
  exact hscope.impScopedReceipts
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
      head parent recursor index ctor rule minor scopedReceipt ordinaryReceipt)

/- Indexed counterpart of the paired generated-result/iota traversal. -/
theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResultAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule ∧
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
          GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule := by
  exact hscope.impScopedReceipts
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
      head parent recursor index ctor rule minor scopedReceipt ordinaryReceipt)

/- Explicitly name the paired base/target endpoint in the indexed local
   traversal. -/
theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResultAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule ∧
        GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
          (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleResult env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
          GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule := by
  exact hscope.impGeneratedRecursorRuleResultAndIota head


theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResultSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
          entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule => GeneratedRecursorRuleResultSemantics env universes stats
      motives minors ctx entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts (fun entry rule scopedReceipt ordinaryReceipt =>
    head entry rule scopedReceipt ordinaryReceipt)

theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResultSemanticsAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors
          ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResultSemantics env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts (fun entry rule scopedReceipt ordinaryReceipt => by
    obtain ⟨semantic, generated⟩ := head entry rule scopedReceipt ordinaryReceipt
    exact ⟨⟨semantic, generated⟩, generated.iotaKind.baseAndTargetResults⟩)

/- Explicitly name the paired base/target endpoint for scoped semantic
   generated-result traversal. -/
theorem RecursorRuleRhsScope.impGeneratedRecursorRuleResultSemanticsAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors
          ctx entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResultSemantics env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors
        ctx entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impGeneratedRecursorRuleResultSemanticsAndIota head


theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResultSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  obtain ⟨semantic, translated⟩ := head parent recursor index ctor rule minor hreceipt
    hreceipt.fvars.counts.receipt
  exact ⟨rule, minor, hrule, hminor, semantic, translated⟩

theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResultSemanticsAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
           GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule) := by
  exact hscope.impScopedReceipts
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt => by
      obtain ⟨semantic, generated⟩ :=
        head parent recursor index ctor rule minor scopedReceipt ordinaryReceipt
      exact ⟨⟨semantic, generated⟩, generated.iotaKind.baseAndTargetResults⟩)

/- Explicitly name the paired base/target endpoint for indexed local semantic
   generated-result traversal. -/
theorem LocalRecursorRuleRhsScope.impGeneratedRecursorRuleResultSemanticsAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
           GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule) := by
  exact hscope.impGeneratedRecursorRuleResultSemanticsAndIota head


/- Registration-facing names make the callback shape explicit at the consumer
   boundary; the proof remains the indexed receipt transport above. -/
theorem RecursorRuleRhsScope.registrationRuleHead
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
          entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule => GeneratedRecursorRuleResultSemantics env universes stats
      motives minors ctx entry.1 minors[entry.2]! rule) (ctors.zipIdx initial) rules :=
  hscope.impGeneratedRecursorRuleResultSemantics head

theorem RecursorRuleRhsScope.registrationRuleHeadAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
          entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules :=
  hscope.impGeneratedRecursorRuleResultSemanticsAndIota head

theorem RecursorRuleRhsScope.registrationRuleHeadAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
          entry.1 minors[entry.2]! rule) :
    List.Forall₂ (fun entry rule =>
      GeneratedRecursorRuleResultSemantics env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.registrationRuleHeadAndIota head

theorem LocalRecursorRuleRhsScope.registrationRuleHead
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule :=
  hscope.impGeneratedRecursorRuleResultSemantics head

theorem LocalRecursorRuleRhsScope.registrationRuleHeadAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
           GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule) :=
  hscope.impGeneratedRecursorRuleResultSemanticsAndIota head

theorem LocalRecursorRuleRhsScope.registrationRuleHeadAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
          (infos.flatMap (·.minors)) ctx ctor minor rule) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (GeneratedRecursorRuleResultSemantics env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule ∧
           GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats (infos.map (·.motive))
            (infos.flatMap (·.minors)) ctx ctor minor rule) := by
  exact hscope.registrationRuleHeadAndIota head

/- Pair the closed rule-body semantic witness required by registration with the
   generated applied-result package.  This is the local indexed seam used by
   the recursor registration consumer. -/
theorem LocalRecursorRuleRhsScope.ruleResultSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
            (stats := stats) (motives := infos.map (·.motive))
            (minors := infos.flatMap (·.minors)) (ctx := ctx)
            (constructor := ctor) (minor := minor) (rule := rule) := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor,
    head parent recursor index ctor rule minor hreceipt (hreceipt.fvars.counts.receipt)⟩

/- Preserve the generated package and expose its paired base/target iota
   endpoint at the indexed recursor boundary.  The pair is projected from the
   same result supplied by the producer, so constructor/rule alignment and the
   closed RHS semantic witness remain unchanged. -/
theorem LocalRecursorRuleRhsScope.ruleResultSemanticsAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
            (stats := stats) (motives := infos.map (·.motive))
            (minors := infos.flatMap (·.minors)) (ctx := ctx)
            (constructor := ctor) (minor := minor) (rule := rule) ∧
          GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  obtain ⟨closed, generated⟩ :=
    head parent recursor index ctor rule minor hreceipt (hreceipt.fvars.counts.receipt)
  obtain ⟨semantic, translated⟩ := closed
  exact ⟨rule, minor, hrule, hminor, ⟨semantic, translated⟩, generated,
    generated.iotaKind.baseAndTargetResults⟩

theorem LocalRecursorRuleRhsScope.ruleResultSemanticsAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (head : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
            (stats := stats) (motives := infos.map (·.motive))
            (minors := infos.flatMap (·.minors)) (ctx := ctx)
            (constructor := ctor) (minor := minor) (rule := rule) ∧
          GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
            (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule := by
  exact hscope.ruleResultSemanticsAndIota head

/- Keep the closed RHS translation and the generated applied-result package as
   separate producer callbacks until the indexed registration boundary pairs
   them.  This mirrors the distinct complete-rule callback in the CPS layer. -/
theorem LocalRecursorRuleRhsScope.ruleResultSemanticsSplit
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {types : Array InductiveType} {infos : Array RecInfo}
    {ctx : Context} {kernelEnv : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx kernelEnv)
    (closedHead : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat)
      (ctor : Constructor) (rule : RecursorRule) (minor : Expr),
      RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors))
          ctx ctor minor rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := infos.map (·.motive))
          (minors := infos.flatMap (·.minors)) (ctx := ctx)
          (constructor := ctor) (minor := minor) (rule := rule)) :
    ∀ parent, parent < types.size → ∃ recursor,
      kernelEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          infos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
            (stats := stats) (motives := infos.map (·.motive))
            (minors := infos.flatMap (·.minors)) (ctx := ctx)
            (constructor := ctor) (minor := minor) (rule := rule) := by
  exact hscope.ruleResultSemantics (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
    ⟨closedHead parent recursor index ctor rule minor scopedReceipt ordinaryReceipt,
      generatedHead parent recursor index ctor rule minor scopedReceipt ordinaryReceipt⟩)

/- The aligned all-rule form preserves constructor/index and stored-rule order
   while returning the same closed semantic and generated-result pair. -/
theorem RecursorRuleRhsScope.impRuleResultSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule))
      (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts head

/- The aligned all-rule consumer can retain the paired base/target iota
   endpoint alongside the closed semantic and generated package.  The
   projection is taken from the same generated witness supplied by `head`, so
   constructor/rule order and all producer obligations remain unchanged. -/
theorem RecursorRuleRhsScope.impRuleResultSemanticsAndIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule) ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impScopedReceipts (fun entry rule scopedReceipt ordinaryReceipt => by
    obtain ⟨closed, generated⟩ := head entry rule scopedReceipt ordinaryReceipt
    exact ⟨closed, generated, generated.iotaKind.baseAndTargetResults⟩)

theorem RecursorRuleRhsScope.impRuleResultSemanticsAndIotaBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule) ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impRuleResultSemanticsAndIota head

/- The all-rule consumer has the same split form as the indexed consumer: keep
   the closed translation and generated package callbacks independent, then
   preserve their chronological constructor/rule alignment. -/
theorem RecursorRuleRhsScope.impRuleResultSemanticsSplit
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (closedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule))
      (ctors.zipIdx initial) rules := by
  exact hscope.impRuleResultSemantics (fun entry rule scopedReceipt ordinaryReceipt =>
    ⟨closedHead entry rule scopedReceipt ordinaryReceipt,
      generatedHead entry rule scopedReceipt ordinaryReceipt⟩)

/- The split all-rule consumer can also retain the paired base/target iota
   endpoint.  Closed semantics and generated packages remain independent
   callbacks until the aligned receipt boundary combines them. -/
theorem RecursorRuleRhsScope.impRuleResultSemanticsAndIotaSplit
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (closedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule) ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impRuleResultSemanticsAndIota
    (fun entry rule scopedReceipt ordinaryReceipt => by
      exact ⟨closedHead entry rule scopedReceipt ordinaryReceipt,
        generatedHead entry rule scopedReceipt ordinaryReceipt⟩)

theorem RecursorRuleRhsScope.impRuleResultSemanticsAndIotaSplitBaseAndTargetResults
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (closedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule =>
      (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
      GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
        (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
        (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule) ∧
      GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx
        entry.1 minors[entry.2]! rule)
      (ctors.zipIdx initial) rules := by
  exact hscope.impRuleResultSemanticsAndIotaSplit closedHead generatedHead

/- Registration only needs the closed RHS translation from the paired result
   callback.  Project it without reopening or rebuilding the generated package.
   The aligned rule list remains available to the continuation unchanged. -/
theorem RecursorRuleRhsScope.impRuleSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
        GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
          (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
          (constructor := entry.1) (minor := minors[entry.2]!) (rule := rule)) :
    List.Forall₂ (fun entry rule => ∃ semantic, TrExprS env universes [] rule.rhs semantic)
      (ctors.zipIdx initial) rules := by
  exact List.Forall₂.imp (fun _ _ result => result.1) (hscope.impRuleResultSemantics head)


end Lean4Lean.AddInductive
