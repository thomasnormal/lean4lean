import Lean4Lean.Verify.RecursorRuleRhsCounts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  Lean4Lean.AddInductive.withLocalDeclWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.forall₂_at Lean4Lean.AddInductive.forIn_rhs
  from Lean4Lean.Verify.RecursorRuleRhs
open private Lean4Lean.AddInductive.forall₂_mono from Lean4Lean.Verify.RecursorRuleRhsCounts
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

def RecursorFieldsAreFVars (fields : Array Expr) : Prop :=
  ∀ field ∈ fields, field.isFVar = true

theorem RecursorFieldsAreFVars.push {fields : Array Expr} (hfields : RecursorFieldsAreFVars fields)
    {field : Expr} (hfield : field.isFVar = true) : RecursorFieldsAreFVars (fields.push field) := by
  intro entry hentry
  obtain hentry | rfl := Array.mem_push.mp hentry
  · exact hfields entry hentry
  · exact hfield

theorem RecursorFieldsAreFVars.sublist {fields selected : Array Expr}
    (hfields : RecursorFieldsAreFVars fields) (hselected : selected.toList.Sublist fields.toList) :
    RecursorFieldsAreFVars selected := by
  intro field hfield
  apply hfields field
  have hmem : field ∈ selected.toList := by simpa using hfield
  simpa using hselected.subset hmem

private theorem loopCtorArgs_loop_fvars (stats : InductiveStats) (type : Expr)
    (index : Nat) (fields recursiveFields : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hfvars : RecursorFieldsAreFVars fields) (hselected : recursiveFields.toList.Sublist fields.toList)
    (hnext : ∀ result finalFields finalRecursive current, ctx.HeaderFrame current →
      RecursorFieldsAreFVars finalFields → finalRecursive.toList.Sublist finalFields.toList →
      (next result finalFields finalRecursive current).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx).WF post := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · split
      · exact ih _ _ _ _ ctx hfvars hselected hnext
      · apply Lean4Lean.AddInductive.withLocalDeclWF
        intro arg current harg _ _ hframe
        apply Lean4Lean.AddInductive.bindWF
        intro recursive
        apply ih
        · exact hfvars.push harg
        · split
          · simpa only [Array.toList_push] using hselected.append (List.Sublist.refl [arg])
          · simpa only [Array.toList_push] using (List.sublist_append_of_sublist_left hselected (l₂ := [arg]))
        · intro result finalFields finalRecursive final hfinal hvars hselection
          exact hnext result finalFields finalRecursive final (hframe.trans hfinal) hvars hselection
    · exact hnext type fields recursiveFields ctx (.refl ctx) hfvars hselected

theorem mkRecInfos.loopCtorArgs.fvars (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hnext : ∀ result fields recursiveFields current, ctx.HeaderFrame current →
      RecursorFieldsAreFVars fields → recursiveFields.toList.Sublist fields.toList →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  apply loopCtorArgs_loop_fvars stats type 0 #[] #[] ctx.fuel.inductiveFuel next ctx post
  · intro field hfield
    simp at hfield
  · exact .refl []
  · exact hnext

def RecursorRuleRhsFVarReceipt (stats : InductiveStats) (motives minors : Array Expr)
    (ctx : Context) (ctor : Constructor) (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
    RecursorFieldsAreFVars fields ∧ recursiveFields.toList.Sublist fields.toList ∧
    values.size = recursiveFields.size ∧ rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
    rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor

theorem RecursorRuleRhsFVarReceipt.counts {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hvars : RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsCountReceipt stats motives minors ctx ctor minor rule := by
  obtain ⟨fields, recursiveFields, values, current, hframe, _, hselected, hvalues, hname, hfields, hrhs⟩ := hvars
  exact ⟨fields, recursiveFields, values, current, hframe, hselected, hvalues, hname, hfields, hrhs⟩

theorem RecursorRuleRhsFVarReceipt.shapes {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hvars : RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.HeaderFrame current ∧
      RecursorFieldsAreFVars fields ∧ RecursorFieldsAreFVars recursiveFields ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧ values.size ≤ rule.nfields ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor := by
  obtain ⟨fields, recursiveFields, values, current, hframe, hfvars, hselected, hvalues, hname, hfields, hrhs⟩ := hvars
  have hbound : recursiveFields.size ≤ fields.size := by simpa using hselected.length_le
  exact ⟨fields, recursiveFields, values, current, hframe, hfvars, hfvars.sublist hselected,
    hselected, hvalues, hname, hfields, by omega, hrhs⟩

def RecursorRuleRhsFVars (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat) : Prop :=
  List.Forall₂ (fun entry rule =>
    RecursorRuleRhsFVarReceipt stats motives minors ctx entry.1 minors[entry.2]! rule)
    (ctors.zipIdx initial) rules

theorem RecursorRuleRhsFVars.counts {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hvars : RecursorRuleRhsFVars stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsCounts stats motives minors ctx ctors rules initial :=
  Lean4Lean.AddInductive.forall₂_mono (fun _ _ hreceipt => hreceipt.counts) hvars

theorem RecursorRuleRhsFVars.at {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hvars : RecursorRuleRhsFVars stats motives minors ctx ctors rules initial)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minors[initial + index]! rule := by
  apply Lean4Lean.AddInductive.forall₂_at hvars index (ctor, initial + index)
  simp [hctor]

theorem mkRecRules.rhsFVars (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (parent : Nat) (motives minors : Array Expr)
    (initial : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsFVars stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply Lean4Lean.AddInductive.forIn_rhs (receipt := fun ctor minorIndex rule =>
      RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minors[minorIndex]! rule)
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minors[minorIndex]! result.1 ∧
        result.2 = minorIndex + 1) ?_ ?_
    · apply mkRecInfos.loopCtorArgs.fvars
      intro type fields recursiveFields current hframe hfvars hselected
      apply mkRecRules.loopU.counts
      intro values hvalues
      apply Lean4Lean.AddInductive.getLCtxWF
      exact .pure ⟨⟨fields, recursiveFields, values, current, hframe, hfvars, hselected,
        by simpa using hvalues, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hreceipt, hstate⟩
      exact .pure ⟨rule, rfl, hreceipt, hstate⟩
  · rintro result ⟨added, hadded, halignment, hfinal⟩
    simp only [List.nil_append] at hadded
    exact ⟨by simpa only [RecursorRuleRhsFVars, hadded] using halignment, hfinal⟩

def LocalRecursorRuleRhsFVars (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ parent, parent < types.size → ∃ recursor : RecursorVal,
    env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
    ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
      ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
        infos[parent]!.minors[index]? = some minor ∧
        RecursorRuleRhsFVarReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule

theorem InductiveStats.RecursorOffsetMetadata.localRuleRhsFVars {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) : LocalRecursorRuleRhsFVars stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hsource⟩ := hmetadata.sourceRules parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  have hindex : index < types[parent]!.ctors.length := by
    by_contra hbound
    simp [List.getElem?_eq_none (show types[parent]!.ctors.length ≤ index by omega)] at hctor
  obtain ⟨hrhs, _⟩ := mkRecRules.rhsFVars types elimLevel stats parent (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset types parent) ctx _ hsource
  obtain ⟨rule, hrule, hreceipt⟩ := hrhs.at index ctor hctor
  obtain ⟨hlocal, _, _⟩ := hcounts.minorIndexing parent hparent index hindex
  refine ⟨rule, infos[parent]!.minors[index]!, hrule, ?_, ?_⟩
  · simpa only [getElem!_pos, hlocal] using (Array.getElem?_eq_getElem hlocal)
  · simpa only [hcounts.minorIndexing.getElem! parent hparent index hindex] using hreceipt

theorem InductiveStats.SafeRunMinorOffsets.localRuleRhsFVars {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhsFVars stats types infos source env := by
  obtain ⟨_, infos, source, _, hframe, hcounts, hmetadata⟩ := hoffsets.recursors
  exact ⟨infos, source, hframe, hcounts, hmetadata.localRuleRhsFVars hcounts⟩

theorem run.safeRuleRhsFVars (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMinorOffsets nparams types.toArray numNested ctx root constructors env ∧
        ∃ (infos : Array RecInfo) (source : Context),
          ({ root with env := constructors } : Context).HeaderFrame source ∧
          RecursorInfoCounts types.toArray infos ∧ LocalRecursorRuleRhsFVars stats types.toArray infos source env := by
  refine (run.safeMinorOffsets nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hoffsets⟩
  exact ⟨stats, root, constructors, hoffsets, hoffsets.localRuleRhsFVars⟩

end Lean4Lean.AddInductive
