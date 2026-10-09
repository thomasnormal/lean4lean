import Lean4Lean.Verify.RecursorRuleRhsFVars
import Lean4Lean.Verify.InductiveParamValidity

namespace Lean.LocalContext

theorem WF.find?_of_mem {lctx : LocalContext} (hwf : lctx.WF)
    {decl : LocalDecl} (hdecl : decl ∈ lctx.toList) :
    lctx.find? decl.fvarId = some decl := by
  have hkeys : (lctx.toList.map fun entry => (entry.fvarId, entry)).NodupKeys := by
    simpa [List.NodupKeys, List.map_map] using hwf.nodup
  rw [hwf.find?_eq_find?_toList, ← List.map_fst_lookup]
  exact hkeys.lookup_eq_some.mpr (List.mem_map.mpr ⟨decl, hdecl, rfl⟩)

end Lean.LocalContext

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.forall₂_at Lean4Lean.AddInductive.forIn_rhs
  from Lean4Lean.Verify.RecursorRuleRhs
open private Lean4Lean.AddInductive.forall₂_mono from Lean4Lean.Verify.RecursorRuleRhsCounts
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

structure Context.RecursorScopeFrame (original current : Context) : Prop
    extends original.HeaderFrame current where
  wf : current.lctx.WF
  reserved : ContextReserved current.lctx current.ngen
  declarations : original.lctx.toList.Sublist current.lctx.toList

theorem Context.RecursorScopeFrame.refl (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) : ctx.RecursorScopeFrame ctx :=
  ⟨.refl ctx, hwf, hreserved, .refl _⟩

theorem Context.RecursorScopeFrame.trans {original middle current : Context}
    (hfirst : original.RecursorScopeFrame middle) (hsecond : middle.RecursorScopeFrame current) :
    original.RecursorScopeFrame current :=
  ⟨hfirst.toHeaderFrame.trans hsecond.toHeaderFrame, hsecond.wf, hsecond.reserved,
    hfirst.declarations.trans hsecond.declarations⟩

theorem Context.RecursorScopeFrame.push (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (name : Name) (bi : BinderInfo) (domain : Expr) :
    ctx.RecursorScopeFrame { ctx with
      ngen := ctx.ngen.next
      lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name domain bi } := by
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, hwf.mkLocalDecl (hreserved.fresh hwf),
    hreserved.push_current name domain bi, ?_⟩
  simp only [LocalContext.mkLocalDecl_toList]
  exact List.sublist_cons_self _ _

theorem Context.RecursorScopeFrame.oldLookup {original current : Context}
    (hframe : original.RecursorScopeFrame current) (hwf : original.lctx.WF)
    {fvar : FVarId} {decl : LocalDecl} (hlookup : original.lctx.find? fvar = some decl) :
    current.lctx.find? fvar = some decl := by
  rw [hwf.find?_eq_find?_toList] at hlookup
  have hdecl := List.mem_of_find?_eq_some hlookup
  have hid := List.find?_some hlookup
  have heq : fvar = decl.fvarId := by simpa only [beq_iff_eq] using hid
  rw [heq]
  exact hframe.wf.find?_of_mem (hframe.declarations.subset hdecl)

def RecursorFieldsDeclared (lctx : LocalContext) (fields : Array Expr) : Prop :=
  ∀ field ∈ fields, ∃ decl ∈ lctx.toList, decl.toExpr = field ∧
    decl.value? (allowNondep := true) = none ∧ decl.kind = .default

theorem RecursorFieldsDeclared.fvars {lctx : LocalContext} {fields : Array Expr}
    (hfields : RecursorFieldsDeclared lctx fields) : RecursorFieldsAreFVars fields := by
  intro field hfield
  obtain ⟨decl, _, rfl, _, _⟩ := hfields field hfield
  cases decl <;> rfl

theorem RecursorFieldsDeclared.sublist {lctx : LocalContext} {fields selected : Array Expr}
    (hfields : RecursorFieldsDeclared lctx fields) (hselected : selected.toList.Sublist fields.toList) :
    RecursorFieldsDeclared lctx selected := by
  intro field hfield
  apply hfields field
  have hmem : field ∈ selected.toList := by simpa using hfield
  simpa using hselected.subset hmem

theorem RecursorFieldsDeclared.push {lctx : LocalContext} {fields : Array Expr}
    (hfields : RecursorFieldsDeclared lctx fields) (fvar : FVarId) (name : Name)
    (domain : Expr) (bi : BinderInfo) :
    RecursorFieldsDeclared (lctx.mkLocalDecl fvar name domain bi) (fields.push (.fvar fvar)) := by
  intro field hfield
  obtain hfield | rfl := Array.mem_push.mp hfield
  · obtain ⟨decl, hdecl, hshape⟩ := hfields field hfield
    exact ⟨decl, by simp only [LocalContext.mkLocalDecl_toList, List.mem_cons]; exact .inr hdecl, hshape⟩
  · exact ⟨.cdecl lctx.decls.size fvar name domain bi .default,
      by simp only [LocalContext.mkLocalDecl_toList, List.mem_cons]; exact .inl trivial, rfl, rfl, rfl⟩

theorem RecursorFieldsDeclared.lookup {lctx : LocalContext} {fields : Array Expr}
    (hfields : RecursorFieldsDeclared lctx fields) (hwf : lctx.WF) :
    ∀ field ∈ fields, ∃ decl, lctx.find? decl.fvarId = some decl ∧ decl.toExpr = field ∧
      decl.value? (allowNondep := true) = none ∧ decl.kind = .default := by
  intro field hfield
  obtain ⟨decl, hdecl, hshape⟩ := hfields field hfield
  exact ⟨decl, hwf.find?_of_mem hdecl, hshape⟩

private theorem withLocalDeclScopeWF {ctx : Context} {name : Name} {bi : BinderInfo} {type : Expr}
    {next : Expr → M α} {post : α → Prop}
    (hnext : (next (.fvar ⟨ctx.ngen.curr⟩) { ctx with
      ngen := ctx.ngen.next
      lctx := ctx.lctx.mkLocalDecl ⟨ctx.ngen.curr⟩ name type bi }).WF post) :
    (withLocalDecl name bi type next ctx).WF post := hnext

private theorem loopCtorArgs_loop_scope (stats : InductiveStats) (type : Expr)
    (index : Nat) (fields recursiveFields : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hfields : RecursorFieldsDeclared ctx.lctx fields)
    (hselected : recursiveFields.toList.Sublist fields.toList)
    (hnext : ∀ result finalFields finalRecursive current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx finalFields →
      finalRecursive.toList.Sublist finalFields.toList → (next result finalFields finalRecursive current).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx).WF post := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · split
      · exact ih _ _ _ _ ctx hwf hreserved hfields hselected hnext
      · rename_i name domain body bi _ _
        have hframe := Context.RecursorScopeFrame.push ctx hwf hreserved name bi domain.consumeTypeAnnotations
        apply withLocalDeclScopeWF
        apply Lean4Lean.AddInductive.bindWF
        intro recursive
        apply ih
        · exact hframe.wf
        · exact hframe.reserved
        · exact hfields.push ⟨ctx.ngen.curr⟩ name domain.consumeTypeAnnotations bi
        · split
          · simpa only [Array.toList_push] using hselected.append (List.Sublist.refl [.fvar ⟨ctx.ngen.curr⟩])
          · simpa only [Array.toList_push] using (List.sublist_append_of_sublist_left hselected (l₂ := [.fvar ⟨ctx.ngen.curr⟩]))
        · intro result finalFields finalRecursive current hfinal hdeclared hselection
          exact hnext result finalFields finalRecursive current (hframe.trans hfinal) hdeclared hselection
    · exact hnext type fields recursiveFields ctx (.refl ctx hwf hreserved) hfields hselected

theorem mkRecInfos.loopCtorArgs.scope (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (hnext : ∀ result fields recursiveFields current, ctx.RecursorScopeFrame current →
      RecursorFieldsDeclared current.lctx fields → recursiveFields.toList.Sublist fields.toList →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  apply loopCtorArgs_loop_scope stats type 0 #[] #[] ctx.fuel.inductiveFuel next ctx post hwf hreserved
  · intro field hfield
    simp at hfield
  · exact .refl []
  · exact hnext

def RecursorRuleRhsScopeReceipt (stats : InductiveStats) (motives minors : Array Expr)
    (ctx : Context) (ctor : Constructor) (minor : Expr) (rule : RecursorRule) : Prop :=
  ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
    RecursorFieldsDeclared current.lctx fields ∧ recursiveFields.toList.Sublist fields.toList ∧
    values.size = recursiveFields.size ∧ rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
    rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor

theorem RecursorRuleRhsScopeReceipt.fvars {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hscope : RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule) :
    RecursorRuleRhsFVarReceipt stats motives minors ctx ctor minor rule := by
  obtain ⟨fields, recursiveFields, values, current, hframe, hdeclared, hrest⟩ := hscope
  exact ⟨fields, recursiveFields, values, current, hframe.toHeaderFrame, hdeclared.fvars, hrest⟩

theorem RecursorRuleRhsScopeReceipt.lookups {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {ctor : Constructor} {minor : Expr} {rule : RecursorRule}
    (hscope : RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minor rule) :
    ∃ (fields recursiveFields values : Array Expr) (current : Context), ctx.RecursorScopeFrame current ∧
      (∀ field ∈ fields, ∃ decl, current.lctx.find? decl.fvarId = some decl ∧ decl.toExpr = field ∧
        decl.value? (allowNondep := true) = none ∧ decl.kind = .default) ∧
      (∀ field ∈ recursiveFields, ∃ decl, current.lctx.find? decl.fvarId = some decl ∧ decl.toExpr = field ∧
        decl.value? (allowNondep := true) = none ∧ decl.kind = .default) ∧
      recursiveFields.toList.Sublist fields.toList ∧ values.size = recursiveFields.size ∧
      rule.ctor = ctor.name ∧ rule.nfields = fields.size ∧
      rule.rhs = recursorRuleRhs stats motives minors fields values current.lctx minor := by
  obtain ⟨fields, recursiveFields, values, current, hframe, hdeclared, hselected, hrest⟩ := hscope
  exact ⟨fields, recursiveFields, values, current, hframe, hdeclared.lookup hframe.wf,
    (hdeclared.sublist hselected).lookup hframe.wf, hselected, hrest⟩

def RecursorRuleRhsScope (stats : InductiveStats) (motives minors : Array Expr) (ctx : Context)
    (ctors : List Constructor) (rules : List RecursorRule) (initial : Nat) : Prop :=
  List.Forall₂ (fun entry rule =>
    RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule)
    (ctors.zipIdx initial) rules

theorem RecursorRuleRhsScope.fvars {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial) :
    RecursorRuleRhsFVars stats motives minors ctx ctors rules initial :=
  Lean4Lean.AddInductive.forall₂_mono (fun _ _ hreceipt => hreceipt.fvars) hscope

theorem RecursorRuleRhsScope.at {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧
      RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minors[initial + index]! rule := by
  apply Lean4Lean.AddInductive.forall₂_at hscope index (ctor, initial + index)
  simp [hctor]

theorem mkRecRules.rhsScope (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (parent : Nat) (motives minors : Array Expr)
    (initial : Nat) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (mkRecRules types elimLevel stats parent motives minors initial ctx).WF fun result =>
      RecursorRuleRhsScope stats motives minors ctx types[parent]!.ctors result.1 initial ∧
      result.2 = initial + types[parent]!.ctors.length := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply Lean4Lean.AddInductive.forIn_rhs (receipt := fun ctor minorIndex rule =>
      RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minors[minorIndex]! rule)
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      RecursorRuleRhsScopeReceipt stats motives minors ctx ctor minors[minorIndex]! result.1 ∧
        result.2 = minorIndex + 1) ?_ ?_
    · apply mkRecInfos.loopCtorArgs.scope
      · exact hwf
      · exact hreserved
      intro type fields recursiveFields current hframe hdeclared hselected
      apply mkRecRules.loopU.counts
      intro values hvalues
      apply Lean4Lean.AddInductive.getLCtxWF
      exact .pure ⟨⟨fields, recursiveFields, values, current, hframe, hdeclared, hselected,
        by simpa using hvalues, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hreceipt, hstate⟩
      exact .pure ⟨rule, rfl, hreceipt, hstate⟩
  · rintro result ⟨added, hadded, halignment, hfinal⟩
    simp only [List.nil_append] at hadded
    exact ⟨by simpa only [RecursorRuleRhsScope, hadded] using halignment, hfinal⟩

def LocalRecursorRuleRhsScope (stats : InductiveStats) (types : Array InductiveType)
    (infos : Array RecInfo) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ parent, parent < types.size → ∃ recursor : RecursorVal,
    env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
    ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
      ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
        infos[parent]!.minors[index]? = some minor ∧
        RecursorRuleRhsScopeReceipt stats (infos.map (·.motive)) (infos.flatMap (·.minors)) ctx ctor minor rule

theorem LocalRecursorRuleRhsScope.fvars {stats : InductiveStats} {types : Array InductiveType}
    {infos : Array RecInfo} {ctx : Context} {env : Kernel.Environment}
    (hscope : LocalRecursorRuleRhsScope stats types infos ctx env) :
    LocalRecursorRuleRhsFVars stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hreceipts⟩ := hscope parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hreceipts index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hreceipt.fvars⟩

theorem InductiveStats.RecursorOffsetMetadata.localRuleRhsScope {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hcounts : RecursorInfoCounts types infos) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) : LocalRecursorRuleRhsScope stats types infos ctx env := by
  intro parent hparent
  obtain ⟨recursor, hfind, hsource⟩ := hmetadata.sourceRules parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  have hindex : index < types[parent]!.ctors.length := by
    by_contra hbound
    simp [List.getElem?_eq_none (show types[parent]!.ctors.length ≤ index by omega)] at hctor
  obtain ⟨hrhs, _⟩ := mkRecRules.rhsScope types elimLevel stats parent (infos.map (·.motive))
    (infos.flatMap (·.minors)) (recursorMinorOffset types parent) ctx hwf hreserved _ hsource
  obtain ⟨rule, hrule, hreceipt⟩ := hrhs.at index ctor hctor
  obtain ⟨hlocal, _, _⟩ := hcounts.minorIndexing parent hparent index hindex
  refine ⟨rule, infos[parent]!.minors[index]!, hrule, ?_, ?_⟩
  · simpa only [getElem!_pos, hlocal] using (Array.getElem?_eq_getElem hlocal)
  · simpa only [hcounts.minorIndexing.getElem! parent hparent index hindex] using hreceipt

end Lean4Lean.AddInductive
