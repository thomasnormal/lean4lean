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
