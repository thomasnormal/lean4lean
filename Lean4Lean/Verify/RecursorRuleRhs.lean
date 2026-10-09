import Lean4Lean.Verify.RecursorMinorIndexing

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.loopCtorArgs_frame from Lean4Lean.Verify.RecursorInfoFrame
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

def recursorRuleRhs (stats : InductiveStats) (motives minors fields values : Array Expr)
    (lctx : LocalContext) (minor : Expr) : Expr :=
  lctx.mkLambda stats.params <| lctx.mkLambda motives <|
    lctx.mkLambda minors <| lctx.mkLambda fields <| mkAppN (mkAppN minor fields) values

def RecursorRuleRhsReceipt (stats : InductiveStats) (motives minors : Array Expr)
    (ctx : Context) (ctor : Constructor) (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (fields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
    rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
    rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor

def RecursorRuleRhs (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat) : Prop :=
  List.Forall₂ (fun entry rule =>
    RecursorRuleRhsReceipt stats motives minors ctx entry.1 minors[entry.2]! rule)
    (ctors.zipIdx initial) rules

private theorem forall₂_at {relation : α → β → Prop} {left : List α} {right : List β}
    (halignment : List.Forall₂ relation left right) (index : Nat) (item : α)
    (hitem : left[index]? = some item) :
    ∃ other, right[index]? = some other ∧ relation item other := by
  induction halignment generalizing index with
  | nil => simp at hitem
  | cons hhead htail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hitem
      subst item
      exact ⟨_, rfl, hhead⟩
    | succ index => exact ih index (by simpa using hitem)

private theorem forall₂_length {relation : α → β → Prop} {left : List α} {right : List β}
    (halignment : List.Forall₂ relation left right) : left.length = right.length := by
  induction halignment with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem RecursorRuleRhs.count {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hrhs : RecursorRuleRhs stats motives minors ctx ctors rules initial) :
    rules.length = ctors.length := by
  simpa using (forall₂_length hrhs).symm

theorem RecursorRuleRhs.at {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hrhs : RecursorRuleRhs stats motives minors ctx ctors rules initial)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsReceipt stats motives minors ctx ctor minors[initial + index]! rule := by
  apply forall₂_at hrhs index (ctor, initial + index)
  simp [hctor]

private theorem loopU_context (types : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (levels : List Level) (fields : Array Expr)
    (index : Nat) (values : Array Expr) (next : Array Expr → M (RecursorRule × Nat))
    (ctx : Context) (post : RecursorRule × Nat → Prop)
    (hnext : ∀ values, (next values ctx).WF post) :
    (mkRecRules.loopU types stats motives minors levels fields index values next ctx).WF post := by
  rw [mkRecRules.loopU.eq_def]
  split
  · apply Lean4Lean.AddInductive.bindWF
    intro value
    apply loopU_context
    exact hnext
  · exact hnext values
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

private theorem forIn_rhs (ctors : List Constructor) (initial : Array RecursorRule)
    (state : Nat) (ctx : Context) (receipt : Constructor → Nat → RecursorRule → Prop)
    (step : Constructor → Array RecursorRule → StateT Nat M (ForInStep (Array RecursorRule)))
    (hstep : ∀ ctor rules state, (step ctor rules state ctx).WF fun result =>
      ∃ rule, result.1 = .yield (rules.push rule) ∧ receipt ctor state rule ∧ result.2 = state + 1) :
    (forIn ctors initial step state ctx).WF fun result =>
      ∃ added, result.1.toList = initial.toList ++ added ∧
        List.Forall₂ (fun entry rule => receipt entry.1 entry.2 rule) (ctors.zipIdx state) added ∧
        result.2 = state + ctors.length := by
  induction ctors generalizing initial state with
  | nil => exact .pure ⟨[], by simp, .nil, by simp⟩
  | cons ctor ctors ih =>
    rw [List.forIn_cons]
    refine (hstep ctor initial state).bind ?_
    rintro ⟨result, nextState⟩ ⟨rule, hyield, hreceipt, hstate⟩
    dsimp only at hyield hstate
    subst result
    subst nextState
    refine (ih (initial.push rule) (state + 1)).mono ?_
    rintro result ⟨added, hadded, halignment, hfinal⟩
    refine ⟨rule :: added, ?_, ?_, ?_⟩
    · simpa [Array.toList_push, List.append_assoc] using hadded
    · exact .cons hreceipt halignment
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

theorem mkRecRules.rhs (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (parent : Nat) (motives minors : Array Expr)
    (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhs stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply forIn_rhs (receipt := fun ctor minorIndex rule =>
      RecursorRuleRhsReceipt stats motives minors ctx ctor minors[minorIndex]! rule)
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      RecursorRuleRhsReceipt stats motives minors ctx ctor minors[minorIndex]! result.1 ∧
        result.2 = minorIndex + 1) ?_ ?_
    · apply Lean4Lean.AddInductive.loopCtorArgs_frame
      intro type fields recursiveFields current hframe
      apply loopU_context
      intro values
      apply Lean4Lean.AddInductive.getLCtxWF
      exact .pure ⟨⟨fields, values, current, hframe, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hreceipt, hstate⟩
      exact .pure ⟨rule, rfl, hreceipt, hstate⟩
  · rintro result ⟨added, hadded, halignment, hfinal⟩
    simp only [List.nil_append] at hadded
    exact ⟨by simpa only [RecursorRuleRhs, hadded] using halignment, hfinal⟩

def LocalRecursorRuleRhs (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ parent, parent < types.size → ∃ recursor : RecursorVal,
    env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
    ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
      ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
        infos[parent]!.minors[index]? = some minor ∧
        RecursorRuleRhsReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule

theorem InductiveStats.RecursorOffsetMetadata.localRuleRhs {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) : LocalRecursorRuleRhs stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hsource⟩ := hmetadata.sourceRules parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  have hindex : index < types[parent]!.ctors.length := by
    by_contra hbound
    simp [List.getElem?_eq_none (show types[parent]!.ctors.length ≤ index by omega)] at hctor
  obtain ⟨hrhs, _⟩ := mkRecRules.rhs types elimLevel stats parent (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset types parent) ctx _ hsource
  obtain ⟨rule, hrule, hreceipt⟩ := hrhs.at index ctor hctor
  obtain ⟨hlocal, _, _⟩ := hcounts.minorIndexing parent hparent index hindex
  refine ⟨rule, infos[parent]!.minors[index]!, hrule, ?_, ?_⟩
  · simpa only [getElem!_pos, hlocal] using (Array.getElem?_eq_getElem hlocal)
  · simpa only [hcounts.minorIndexing.getElem! parent hparent index hindex] using hreceipt

theorem InductiveStats.SafeRunMinorOffsets.localRuleRhs {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhs stats types infos source env := by
  obtain ⟨_, infos, source, _, hframe, hcounts, hmetadata⟩ := hoffsets.recursors
  exact ⟨infos, source, hframe, hcounts, hmetadata.localRuleRhs hcounts⟩

theorem run.safeRuleRhs (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMinorOffsets nparams types.toArray numNested ctx root constructors env ∧
        ∃ (infos : Array RecInfo) (source : Context),
          ({ root with env := constructors } : Context).HeaderFrame source ∧
          RecursorInfoCounts types.toArray infos ∧ LocalRecursorRuleRhs stats types.toArray infos source env := by
  refine (run.safeMinorOffsets nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hoffsets⟩
  exact ⟨stats, root, constructors, hoffsets, hoffsets.localRuleRhs⟩

end Lean4Lean.AddInductive
