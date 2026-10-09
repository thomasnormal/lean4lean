import Lean4Lean.Verify.InductiveIndexLookupSubstitution
import Lean4Lean.Verify.InductiveIndexLookupSupport
import Lean4Lean.Verify.InductiveBinderSupportAlignment
import Lean4Lean.Verify.InductiveParamReconstruction

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved SourceReserved)

private theorem nodupAppendFresh {ids : List FVarId} {id : FVarId}
    (distinct : ids.Nodup) (outside : id ∉ ids) : (ids ++ [id]).Nodup := by
  rw [List.nodup_append]
  refine ⟨distinct, by simp, ?_⟩
  intro before hbefore after hafter
  have hafterId : after = id := List.mem_singleton.mp hafter
  subst after
  intro heq
  exact outside (heq ▸ hbefore)

theorem IndexPairInjection.appendFresh {pairs : List (FVarId × FVarId)} {source target : FVarId}
    (injection : IndexPairInjection pairs) (hsource : source ∉ pairs.map Prod.fst)
    (htarget : target ∉ pairs.map Prod.snd) : IndexPairInjection (pairs ++ [(source, target)]) := by
  simp only [IndexPairInjection, List.map_append, List.map_cons, List.map_nil]
  exact ⟨nodupAppendFresh injection.1 hsource, nodupAppendFresh injection.2 htarget⟩

theorem IndexParameterSupport.appendFresh {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {source target : FVarId} (support : IndexParameterSupport pairs params) (outside : source ∉ params) :
    IndexParameterSupport (pairs ++ [(source, target)]) params := by
  intro id hparam hmem
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at hmem
  obtain hprevious | hnew := hmem
  · exact support id hparam hprevious
  · change id = source at hnew
    subst id
    exact outside hparam

theorem BinderValuesBefore.currentFresh {ctx : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (⟨ctx.ngen.curr⟩ : FVarId) ∉ values.map Expr.fvarId! := by
  intro hmem
  obtain ⟨value, hvalue, hid⟩ := List.mem_map.mp hmem
  obtain ⟨decl, hlookup, _, _⟩ := support value hvalue
  rw [hid, hreserved.fresh hwf] at hlookup
  cases hlookup

theorem IndexLookupRenaming.openFreshIndex' {pairs : List (FVarId × FVarId)}
    {left right : Expr} {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (avoids : IndexAvoids source left) (fresh : source ∉ pairs.map Prod.fst) (depth : Nat) :
    IndexLookupRenaming (pairs ++ [(source, target)])
      (left.instantiate1' (.fvar source) depth) (right.instantiate1' (.fvar target) depth) := by
  have hbody : IndexLookupRenaming (pairs ++ [(source, target)]) left right := by
    change indexRenameExpr (pairs ++ [(source, target)]) left = right
    rw [indexRenameExpr_append_of_avoids avoids]
    exact related
  have hvalue : IndexLookupRenaming (pairs ++ [(source, target)]) (.fvar source) (.fvar target) := by
    simp only [IndexLookupRenaming, indexRenameExpr, indexLookup_append_fresh fresh]
  exact hbody.instantiate1' hvalue depth

theorem IndexLookupRenaming.openFreshIndex {pairs : List (FVarId × FVarId)}
    {left right : Expr} {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (avoids : IndexAvoids source left) (fresh : source ∉ pairs.map Prod.fst) :
    IndexLookupRenaming (pairs ++ [(source, target)])
      (left.instantiate1 (.fvar source)) (right.instantiate1 (.fvar target)) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  exact related.openFreshIndex' avoids fresh 0

theorem IndexLookupRenaming.openMappedIndex' {pairs : List (FVarId × FVarId)}
    {left right : Expr} {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (injection : IndexPairInjection pairs) (hpair : (source, target) ∈ pairs) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' (.fvar source) depth)
      (right.instantiate1' (.fvar target) depth) :=
  related.instantiate1' (.fvar_of_mem injection hpair) depth

theorem IndexLookupRenaming.openMappedIndex {pairs : List (FVarId × FVarId)}
    {left right : Expr} {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (injection : IndexPairInjection pairs) (hpair : (source, target) ∈ pairs) :
    IndexLookupRenaming pairs (left.instantiate1 (.fvar source)) (right.instantiate1 (.fvar target)) :=
  related.instantiate1 (.fvar_of_mem injection hpair)

theorem IndexLookupRenaming.openFixedParameters' {pairs : List (FVarId × FVarId)}
    {params : List FVarId} {left right value : Expr} (related : IndexLookupRenaming pairs left right)
    (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' value depth) (right.instantiate1' value depth) :=
  related.instantiate1' (indexRenameExpr_fixedParameters support within) depth

theorem IndexLookupRenaming.openFixedParameters {pairs : List (FVarId × FVarId)}
    {params : List FVarId} {left right value : Expr} (related : IndexLookupRenaming pairs left right)
    (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) :
    IndexLookupRenaming pairs (left.instantiate1 value) (right.instantiate1 value) :=
  related.instantiate1 (indexRenameExpr_fixedParameters support within)

theorem indexSourceFresh_of_declared {ctx : Context} {pairs : List (FVarId × FVarId)}
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (declared : ∀ id ∈ pairs.map Prod.fst, ∃ decl, ctx.lctx.find? id = some decl) :
    (⟨ctx.ngen.curr⟩ : FVarId) ∉ pairs.map Prod.fst := by
  intro hmem
  obtain ⟨decl, hlookup⟩ := declared _ hmem
  rw [hreserved.fresh hwf] at hlookup
  cases hlookup

theorem IndexLookupRenaming.openCurrentIndex {ctx : Context} {pairs : List (FVarId × FVarId)}
    {left right : Expr} {target : FVarId} (related : IndexLookupRenaming pairs left right)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (declared : ∀ id ∈ pairs.map Prod.fst, ∃ decl, ctx.lctx.find? id = some decl)
    (sourceReserved : SourceReserved left ctx.ngen) :
    IndexLookupRenaming (pairs ++ [(⟨ctx.ngen.curr⟩, target)])
      (left.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) (right.instantiate1 (.fvar target)) :=
  related.openFreshIndex (IndexAvoids.of_not_mem sourceReserved.current_fresh)
    (indexSourceFresh_of_declared hwf hreserved declared)

def IndexOpeningLookup (pairs : List (FVarId × FVarId)) (params : List FVarId) : Prop :=
  (∀ source target, (source, target) ∈ pairs → ∀ left right depth,
    IndexLookupRenaming pairs left right →
    IndexLookupRenaming pairs (left.instantiate1' (.fvar source) depth)
      (right.instantiate1' (.fvar target) depth)) ∧
  (∀ value, IndexFVarsWithin params value → ∀ left right depth,
    IndexLookupRenaming pairs left right →
    IndexLookupRenaming pairs (left.instantiate1' value depth) (right.instantiate1' value depth))

theorem IndexOpeningLookup.ofInjectionSupport {pairs : List (FVarId × FVarId)} {params : List FVarId}
    (injection : IndexPairInjection pairs) (support : IndexParameterSupport pairs params) :
    IndexOpeningLookup pairs params :=
  ⟨fun _ _ hpair _ _ depth related => related.openMappedIndex' injection hpair depth,
    fun _ within _ _ depth related => related.openFixedParameters' support within depth⟩

theorem ParentBinderSupportAlignment.openingLookup {stats : InductiveStats}
    {types : Array InductiveType} {parent : Nat} {checkedRoot current : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checkedRoot current info) :
    ∃ checkedIds pairs,
      checkedIds.length = stats.nindices[parent]! ∧
      pairs = checkedIds.zip (info.indices.toList.map Expr.fvarId!) ∧
      pairs.map Prod.fst = checkedIds ∧
      pairs.map Prod.snd = info.indices.toList.map Expr.fvarId! ∧ IndexPairInjection pairs ∧
      IndexParameterSupport pairs (stats.params.toList.map Expr.fvarId!) ∧
      (∀ id ∈ stats.params.toList.map Expr.fvarId!, id ∉ pairs.map Prod.snd) ∧
      IndexOpeningLookup pairs (stats.params.toList.map Expr.fvarId!) := by
  obtain ⟨checkedIds, pairs, hcount, hpairs, hfst, hsnd, hinjection, hsupport, htarget, _, _⟩ :=
    alignment.injectiveIndexLookup
  exact ⟨checkedIds, pairs, hcount, hpairs, hfst, hsnd, hinjection, hsupport, htarget,
    .ofInjectionSupport hinjection hsupport⟩

end Lean4Lean.AddInductive
