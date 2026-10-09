import Lean4Lean.Verify.RecursorInfoScope

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.withLocalDeclScopeWF from Lean4Lean.Verify.RecursorFieldScope
open private Lean4Lean.AddInductive.forall₂_at Lean4Lean.AddInductive.forIn_rhs
  from Lean4Lean.Verify.RecursorRuleRhs
open private Lean4Lean.AddInductive.forall₂_mono from Lean4Lean.Verify.RecursorRuleRhsCounts
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

theorem RecursorFieldsDeclared.fresh {ctx : Context} {fields : Array Expr}
    (hfields : RecursorFieldsDeclared ctx.lctx fields) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    Expr.fvar ⟨ctx.ngen.curr⟩ ∉ fields.toList := by
  intro hmem
  obtain ⟨decl, hlookup, hexpr, _⟩ := hfields.lookup hwf (.fvar ⟨ctx.ngen.curr⟩) (by simpa using hmem)
  have hid : decl.fvarId = ⟨ctx.ngen.curr⟩ := Expr.fvar.inj hexpr
  rw [hid, hreserved.fresh hwf] at hlookup
  contradiction

theorem RecursorFieldsDeclared.nodup_push {ctx : Context} {fields : Array Expr}
    (hfields : RecursorFieldsDeclared ctx.lctx fields) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (hnodup : fields.toList.Nodup) :
    (fields.push (.fvar ⟨ctx.ngen.curr⟩)).toList.Nodup := by
  rw [Array.toList_push, List.nodup_append]
  refine ⟨hnodup, by simp, ?_⟩
  intro field hfield other hother
  simp only [List.mem_singleton] at hother
  subst other
  intro heq
  exact hfields.fresh hwf hreserved (heq ▸ hfield)

private theorem loopCtorArgs_loop_distinct (stats : InductiveStats) (type : Expr)
    (index : Nat) (fields recursiveFields : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → Array Expr → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hfields : RecursorFieldsDeclared ctx.lctx fields) (hnodup : fields.toList.Nodup)
    (hselected : recursiveFields.toList.Sublist fields.toList)
    (hnext : ∀ result finalFields finalRecursive current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx finalFields → finalFields.toList.Nodup →
      finalRecursive.toList.Sublist finalFields.toList → (next result finalFields finalRecursive current).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx).WF post := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · split
      · exact ih _ _ _ _ ctx hwf hreserved hfields hnodup hselected hnext
      · rename_i name domain body bi _ _
        have hframe := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
        apply Lean4Lean.AddInductive.withLocalDeclScopeWF
        apply Lean4Lean.AddInductive.bindWF
        intro recursive
        apply ih
        · exact hframe.wf
        · exact hframe.reserved
        · exact hfields.push ⟨ctx.ngen.curr⟩ name (peelTypeAnnotations domain) bi
        · exact hfields.nodup_push hwf hreserved hnodup
        · split
          · simpa only [Array.toList_push] using hselected.append (List.Sublist.refl [.fvar ⟨ctx.ngen.curr⟩])
          · simpa only [Array.toList_push] using
              (List.sublist_append_of_sublist_left hselected (l₂ := [.fvar ⟨ctx.ngen.curr⟩]))
        · intro result finalFields finalRecursive current hfinal hdeclared hdistinct hselection
          exact hnext result finalFields finalRecursive current (hframe.trans hfinal) hdeclared hdistinct hselection
    · exact hnext type fields recursiveFields ctx (.refl ctx hwf hreserved) hfields hnodup hselected

theorem mkRecInfos.loopCtorArgs.distinct (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M ResultType) (ctx : Context) (post : ResultType → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ result fields recursiveFields current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx fields → fields.toList.Nodup →
      recursiveFields.toList.Sublist fields.toList → (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  apply loopCtorArgs_loop_distinct stats type 0 #[] #[] ctx.fuel.inductiveFuel next ctx post hwf hreserved
  · intro field hfield
    simp at hfield
  · simp
  · exact .refl []
  · exact hnext

def RecursorRuleRhsDistinctReceipt (stats : InductiveStats) (motives minors : Array Expr)
    (ctx : Context) (ctor : Constructor) (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
    RecursorFieldsDeclared current.lctx fields ∧ fields.toList.Nodup ∧
    recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
    rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
    rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor

theorem RecursorRuleRhsDistinctReceipt.scope {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hdistinct : RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule := by
  obtain ⟨fields, recursiveFields, values, current, hframe, hdeclared, _, hrest⟩ := hdistinct
  exact ⟨fields, recursiveFields, values, current, hframe, hdeclared, hrest⟩

theorem RecursorRuleRhsDistinctReceipt.selected {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hdistinct : RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
      RecursorFieldsDeclared current.lctx fields ∧ fields.toList.Nodup ∧ recursiveFields.toList.Nodup ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor := by
  obtain ⟨fields, recursiveFields, values, current, hframe, hdeclared, hnodup, hselected, hrest⟩ := hdistinct
  exact ⟨fields, recursiveFields, values, current, hframe, hdeclared, hnodup,
    hnodup.sublist hselected, hselected, hrest⟩

def RecursorRuleRhsDistinct (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat) : Prop :=
  List.Forall₂ (fun entry rule =>
    RecursorRuleRhsDistinctReceipt stats motives minors ctx entry.1 minors[entry.2]! rule)
    (ctors.zipIdx initial) rules

theorem RecursorRuleRhsDistinct.scope {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hdistinct : RecursorRuleRhsDistinct stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsScope stats motives minors ctx ctors rules initial :=
  Lean4Lean.AddInductive.forall₂_mono (fun _ _ hreceipt => hreceipt.scope) hdistinct

theorem RecursorRuleRhsDistinct.at {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hdistinct : RecursorRuleRhsDistinct stats motives minors ctx ctors rules initial)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minors[initial + index]! rule := by
  apply Lean4Lean.AddInductive.forall₂_at hdistinct index (ctor, initial + index)
  simp [hctor]

theorem mkRecRules.rhsDistinct (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (parent : Nat) (motives minors : Array Expr)
    (initial : Nat) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsDistinct stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply Lean4Lean.AddInductive.forIn_rhs (receipt := fun ctor minorIndex rule =>
      RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minors[minorIndex]! rule)
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      RecursorRuleRhsDistinctReceipt stats motives minors ctx ctor minors[minorIndex]! result.1 ∧
        result.2 = minorIndex + 1) ?_ ?_
    · apply mkRecInfos.loopCtorArgs.distinct
      · exact hwf
      · exact hreserved
      intro type fields recursiveFields current hframe hdeclared hnodup hselected
      apply mkRecRules.loopU.counts
      intro values hvalues
      apply Lean4Lean.AddInductive.getLCtxWF
      exact .pure ⟨⟨fields, recursiveFields, values, current, hframe, hdeclared, hnodup, hselected,
        by simpa using hvalues, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hreceipt, hstate⟩
      exact .pure ⟨rule, rfl, hreceipt, hstate⟩
  · rintro result ⟨added, hadded, halignment, hfinal⟩
    simp only [List.nil_append] at hadded
    exact ⟨by simpa only [RecursorRuleRhsDistinct, hadded] using halignment, hfinal⟩

def LocalRecursorRuleRhsDistinct (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ parent, parent < types.size → ∃ recursor : RecursorVal,
    env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
    ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
      ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
        infos[parent]!.minors[index]? = some minor ∧
        RecursorRuleRhsDistinctReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule

theorem LocalRecursorRuleRhsDistinct.scope {stats : InductiveStats} {types : Array InductiveType}
    {infos : Array RecInfo} {ctx : Context} {env : Kernel.Environment}
    (hdistinct : LocalRecursorRuleRhsDistinct stats types infos ctx env) :
    LocalRecursorRuleRhsScope stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hdistinct parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hreceipt.scope⟩

theorem InductiveStats.RecursorOffsetMetadata.localRuleRhsDistinct {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) : LocalRecursorRuleRhsDistinct stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hsource⟩ := hmetadata.sourceRules parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  have hindex : index < types[parent]!.ctors.length := by
    by_contra hbound
    simp [List.getElem?_eq_none (show types[parent]!.ctors.length ≤ index by omega)] at hctor
  obtain ⟨hrhs, _⟩ := mkRecRules.rhsDistinct types elimLevel stats parent (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset types parent) ctx hwf hreserved _ hsource
  obtain ⟨rule, hrule, hreceipt⟩ := hrhs.at index ctor hctor
  obtain ⟨hlocal, _, _⟩ := hcounts.minorIndexing parent hparent index hindex
  refine ⟨rule, infos[parent]!.minors[index]!, hrule, ?_, ?_⟩
  · simpa only [getElem!_pos, hlocal] using (Array.getElem?_eq_getElem hlocal)
  · simpa only [hcounts.minorIndexing.getElem! parent hparent index hindex] using hreceipt

theorem mkRecInfos.registeredDistinct (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (lparams : List Name) (isK isUnsafe : Bool) (ctx : Context)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (henv : ctx.env.constants.WF) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe ctx).WF fun result =>
      ctx.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      result.1.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsDistinct stats types result.2.1 result.2.2 result.1 := by
  intro result hresult
  obtain ⟨hframe, hcounts, hmap, hkeep, hmetadata, _⟩ :=
    mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe ctx hwf hreserved henv result hresult
  exact ⟨hframe, hcounts, hmap, hkeep, hmetadata,
    hmetadata.localRuleRhsDistinct hcounts hframe.wf hframe.reserved⟩

end Lean4Lean.AddInductive
