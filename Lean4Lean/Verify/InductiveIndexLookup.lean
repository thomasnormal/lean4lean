import Lean4Lean.Verify.InductiveIndexPositions
import Lean4Lean.Verify.InductiveIndexRenaming

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def indexLookup (pairs : List (FVarId × FVarId)) (id : FVarId) : FVarId :=
  (pairs.lookup id).getD id

def IndexParameterSupport (pairs : List (FVarId × FVarId)) (params : List FVarId) : Prop :=
  ∀ id ∈ params, id ∉ pairs.map Prod.fst

theorem indexLookup_of_mem {pairs : List (FVarId × FVarId)} {id image : FVarId}
    (injection : IndexPairInjection pairs) (hpair : (id, image) ∈ pairs) :
    indexLookup pairs id = image := by
  have hkeys : pairs.NodupKeys := injection.1
  simp only [indexLookup, hkeys.lookup_eq_some.mpr hpair, Option.getD_some]

theorem indexLookup_eq_self_of_not_mem {pairs : List (FVarId × FVarId)} {id : FVarId}
    (hsupport : id ∉ pairs.map Prod.fst) : indexLookup pairs id = id := by
  have hlookup : pairs.lookup id = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair hpair
    apply bne_iff_ne.mpr
    intro heq
    exact hsupport (List.mem_map.mpr ⟨pair, hpair, heq.symm⟩)
  simp only [indexLookup, hlookup, Option.getD_none]

theorem indexLookup_fixedParameters {pairs : List (FVarId × FVarId)} {params : List FVarId}
    (support : IndexParameterSupport pairs params) {id : FVarId} (hparam : id ∈ params) :
    indexLookup pairs id = id :=
  indexLookup_eq_self_of_not_mem (support id hparam)

theorem indexLookup_mem_or_eq (pairs : List (FVarId × FVarId)) (id : FVarId) :
    id = indexLookup pairs id ∨ (id, indexLookup pairs id) ∈ pairs := by
  cases hlookup : pairs.lookup id with
  | none => simp only [indexLookup, hlookup, Option.getD_none, true_or]
  | some image =>
    simp only [indexLookup, hlookup, Option.getD_some]
    obtain ⟨before, after, hpairs, _⟩ := List.lookup_eq_some_iff.mp hlookup
    exact .inr (hpairs ▸ List.mem_append_right before (List.mem_cons_self))

def indexRenameExpr (pairs : List (FVarId × FVarId)) : Expr → Expr
  | .bvar index => .bvar index
  | .sort level => .sort level
  | .const name levels => .const name levels
  | .lit literal => .lit literal
  | .mvar id => .mvar id
  | .fvar id => .fvar (indexLookup pairs id)
  | .app function argument => .app (indexRenameExpr pairs function) (indexRenameExpr pairs argument)
  | .lam name domain body bi => .lam name (indexRenameExpr pairs domain) (indexRenameExpr pairs body) bi
  | .forallE name domain body bi =>
      .forallE name (indexRenameExpr pairs domain) (indexRenameExpr pairs body) bi
  | .letE name domain value body nondep =>
      .letE name (indexRenameExpr pairs domain) (indexRenameExpr pairs value)
        (indexRenameExpr pairs body) nondep
  | .mdata data body => .mdata data (indexRenameExpr pairs body)
  | .proj name index body => .proj name index (indexRenameExpr pairs body)

def IndexLookupRenaming (pairs : List (FVarId × FVarId)) (left right : Expr) : Prop :=
  indexRenameExpr pairs left = right

theorem indexRenameExpr_related (pairs : List (FVarId × FVarId)) (value : Expr) :
    IndexRenaming pairs value (indexRenameExpr pairs value) := by
  induction value with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | mvar id => exact .mvar id
  | fvar id => exact .fvar (indexLookup_mem_or_eq pairs id)
  | app function argument ihFn ihArg => exact .app ihFn ihArg
  | lam name domain body bi ihDomain ihBody => exact .lam name bi ihDomain ihBody
  | forallE name domain body bi ihDomain ihBody => exact .forallE name bi ihDomain ihBody
  | letE name domain value body nondep ihDomain ihValue ihBody => exact .letE name nondep ihDomain ihValue ihBody
  | mdata data body ih => exact .mdata data ih
  | proj name index body ih => exact .proj name index ih

theorem IndexLookupRenaming.functional {pairs : List (FVarId × FVarId)}
    {left first second : Expr} (hfirst : IndexLookupRenaming pairs left first)
    (hsecond : IndexLookupRenaming pairs left second) : first = second :=
  hfirst.symm.trans hsecond

theorem IndexLookupRenaming.related {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) : IndexRenaming pairs left right := by
  rw [← related]
  exact indexRenameExpr_related pairs left

theorem IndexLookupRenaming.fvar_of_mem {pairs : List (FVarId × FVarId)} {id image : FVarId}
    (injection : IndexPairInjection pairs) (hpair : (id, image) ∈ pairs) :
    IndexLookupRenaming pairs (.fvar id) (.fvar image) := by
  simp only [IndexLookupRenaming, indexRenameExpr, indexLookup_of_mem injection hpair]

theorem IndexLookupRenaming.fvar_of_not_mem {pairs : List (FVarId × FVarId)} {id : FVarId}
    (hsupport : id ∉ pairs.map Prod.fst) : IndexLookupRenaming pairs (.fvar id) (.fvar id) := by
  simp only [IndexLookupRenaming, indexRenameExpr, indexLookup_eq_self_of_not_mem hsupport]

theorem IndexLookupRenaming.fixedParameter {pairs : List (FVarId × FVarId)} {params : List FVarId}
    (support : IndexParameterSupport pairs params) {id : FVarId} (hparam : id ∈ params) :
    IndexLookupRenaming pairs (.fvar id) (.fvar id) :=
  .fvar_of_not_mem (support id hparam)

end Lean4Lean.AddInductive
