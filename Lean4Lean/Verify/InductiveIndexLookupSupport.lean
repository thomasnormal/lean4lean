import Lean4Lean.Verify.InductiveIndexLookup

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open scoped List

def IndexFVarsWithin (ids : List FVarId) : Expr → Prop
  | .fvar id => id ∈ ids
  | .app function argument => IndexFVarsWithin ids function ∧ IndexFVarsWithin ids argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      IndexFVarsWithin ids domain ∧ IndexFVarsWithin ids body
  | .letE _ domain value body _ =>
      IndexFVarsWithin ids domain ∧ IndexFVarsWithin ids value ∧ IndexFVarsWithin ids body
  | .mdata _ body | .proj _ _ body => IndexFVarsWithin ids body
  | _ => True

def IndexAvoids (source : FVarId) : Expr → Prop
  | .fvar id => id ≠ source
  | .app function argument => IndexAvoids source function ∧ IndexAvoids source argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      IndexAvoids source domain ∧ IndexAvoids source body
  | .letE _ domain value body _ =>
      IndexAvoids source domain ∧ IndexAvoids source value ∧ IndexAvoids source body
  | .mdata _ body | .proj _ _ body => IndexAvoids source body
  | _ => True

theorem indexLookup_append_fresh {pairs : List (FVarId × FVarId)} {source target : FVarId}
    (hfresh : source ∉ pairs.map Prod.fst) :
    indexLookup (pairs ++ [(source, target)]) source = target := by
  have hlookup : pairs.lookup source = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair hpair
    apply bne_iff_ne.mpr
    intro heq
    exact hfresh (List.mem_map.mpr ⟨pair, hpair, heq.symm⟩)
  simp only [indexLookup, List.lookup_append, hlookup, Option.none_or,
    List.lookup_cons_self, Option.getD_some]

theorem indexLookup_append_of_ne {pairs : List (FVarId × FVarId)} {source target id : FVarId}
    (hne : id ≠ source) :
    indexLookup (pairs ++ [(source, target)]) id = indexLookup pairs id := by
  have hbeq : (id == source) = false := beq_eq_false_iff_ne.mpr hne
  simp [indexLookup, List.lookup_append, List.lookup_cons, hbeq]

theorem IndexAvoids.iff_not_mem {source : FVarId} {value : Expr} :
    IndexAvoids source value ↔ source ∉ value.fvarsList := by
  induction value <;> simp_all [IndexAvoids, Expr.fvarsList, ne_comm]

theorem IndexAvoids.of_not_mem {source : FVarId} {value : Expr}
    (havoids : source ∉ value.fvarsList) : IndexAvoids source value :=
  iff_not_mem.mpr havoids

theorem IndexFVarsWithin.iff_subset {ids : List FVarId} {value : Expr} :
    IndexFVarsWithin ids value ↔ value.fvarsList ⊆ ids := by
  induction value <;> simp_all [IndexFVarsWithin, Expr.fvarsList, List.append_subset]

theorem IndexFVarsWithin.of_subset {ids : List FVarId} {value : Expr}
    (hwithin : value.fvarsList ⊆ ids) : IndexFVarsWithin ids value :=
  iff_subset.mpr hwithin

theorem IndexFVarsWithin.avoids {ids : List FVarId} {value : Expr} {source : FVarId}
    (within : IndexFVarsWithin ids value) (houtside : source ∉ ids) : IndexAvoids source value := by
  induction value with
  | bvar index => trivial
  | sort level => trivial
  | const name levels => trivial
  | lit literal => trivial
  | mvar id => trivial
  | fvar id => exact fun heq => houtside (heq ▸ within)
  | app function argument ihFn ihArg => exact ⟨ihFn within.1, ihArg within.2⟩
  | lam name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1, ihBody within.2⟩
  | forallE name domain body bi ihDomain ihBody => exact ⟨ihDomain within.1, ihBody within.2⟩
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    exact ⟨ihDomain within.1, ihValue within.2.1, ihBody within.2.2⟩
  | mdata data body ih => exact ih within
  | proj name index body ih => exact ih within

theorem indexRenameExpr_append_of_avoids {pairs : List (FVarId × FVarId)}
    {source target : FVarId} {value : Expr} (avoids : IndexAvoids source value) :
    indexRenameExpr (pairs ++ [(source, target)]) value = indexRenameExpr pairs value := by
  induction value with
  | bvar index => rfl
  | sort level => rfl
  | const name levels => rfl
  | lit literal => rfl
  | mvar id => rfl
  | fvar id => simp only [indexRenameExpr, indexLookup_append_of_ne avoids]
  | app function argument ihFn ihArg =>
    simp only [indexRenameExpr, ihFn avoids.1, ihArg avoids.2]
  | lam name domain body bi ihDomain ihBody =>
    simp only [indexRenameExpr, ihDomain avoids.1, ihBody avoids.2]
  | forallE name domain body bi ihDomain ihBody =>
    simp only [indexRenameExpr, ihDomain avoids.1, ihBody avoids.2]
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    simp only [indexRenameExpr, ihDomain avoids.1, ihValue avoids.2.1, ihBody avoids.2.2]
  | mdata data body ih => simp only [indexRenameExpr, ih avoids]
  | proj name index body ih => simp only [indexRenameExpr, ih avoids]

theorem indexRenameExpr_fixedParameters {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {value : Expr} (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) :
    indexRenameExpr pairs value = value := by
  induction value with
  | bvar index => rfl
  | sort level => rfl
  | const name levels => rfl
  | lit literal => rfl
  | mvar id => rfl
  | fvar id => simp only [indexRenameExpr, indexLookup_fixedParameters support within]
  | app function argument ihFn ihArg =>
    simp only [indexRenameExpr, ihFn within.1, ihArg within.2]
  | lam name domain body bi ihDomain ihBody =>
    simp only [indexRenameExpr, ihDomain within.1, ihBody within.2]
  | forallE name domain body bi ihDomain ihBody =>
    simp only [indexRenameExpr, ihDomain within.1, ihBody within.2]
  | letE name domain value body nondep ihDomain ihValue ihBody =>
    simp only [indexRenameExpr, ihDomain within.1, ihValue within.2.1, ihBody within.2.2]
  | mdata data body ih => simp only [indexRenameExpr, ih within]
  | proj name index body ih => simp only [indexRenameExpr, ih within]

end Lean4Lean.AddInductive
