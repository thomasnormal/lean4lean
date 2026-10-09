import Lean4Lean.Verify.InductiveBinderFVarsIn

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

theorem Inner.inferType'_hasLooseBVars_eq_false {value inferred : Expr}
    {inferOnly : Bool} {methods : Methods} {context : Context} {state nextState : State}
    (success : Inner.inferType' value inferOnly methods context state =
      .ok (inferred, nextState)) : value.hasLooseBVars = false := by
  by_contra rejected
  have loose : value.hasLooseBVars = true := by
    cases flag : value.hasLooseBVars <;> simp_all
  unfold Inner.inferType' at success
  simp only [loose, ↓reduceIte] at success
  cases success

theorem Methods.withFuel_inferType_hasLooseBVars_eq_false {value inferred : Expr}
    {inferOnly : Bool} {depth : Nat} {context : Context} {state nextState : State}
    (success : (Methods.withFuel depth).inferType value inferOnly context state =
      .ok (inferred, nextState)) : value.hasLooseBVars = false := by
  cases depth with
  | zero => cases success
  | succ depth => exact Inner.inferType'_hasLooseBVars_eq_false success

theorem checkType_hasLooseBVars_eq_false {value inferred : Expr}
    {context : Context} {state nextState : State}
    (success : checkType value context state = .ok (inferred, nextState)) :
    value.hasLooseBVars = false := by
  exact Methods.withFuel_inferType_hasLooseBVars_eq_false success

theorem checkType_run_hasLooseBVars_eq_false {value inferred : Expr}
    {env : Environment} {safety : DefinitionSafety} {lctx : LocalContext}
    {lparams : List Name} {fuel : FuelConfig}
    (success : M.run env safety lctx lparams fuel (checkType value) = .ok inferred) :
    value.hasLooseBVars = false := by
  unfold M.run StateT.run' at success
  cases checked : checkType value { env, safety, lctx, lparams, fuel } {} with
  | error error => simp [checked] at success
  | ok result => exact checkType_hasLooseBVars_eq_false checked

end TypeChecker

theorem FVarsIn.closed_of_looseBVarRange'_le {predicate : FVarId → Prop}
    {value : Expr} {depth : Nat} (within : value.FVarsIn predicate)
    (range : value.looseBVarRange' ≤ depth) : value.Closed depth := by
  induction value generalizing depth <;>
    simp_all [Closed, FVarsIn, Expr.looseBVarRange', Nat.max_le]
  all_goals omega

namespace AddInductive

theorem CheckedHeaderSource.sourceHasLooseBVars_eq_false {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current) :
    types[parent]!.type.hasLooseBVars = false := by
  obtain ⟨entry, stats, inferred, normalized, terminal, finalStats, binderCtx, sorted,
    hentry, hguard, hinferred, hnormalized, hind, hconst, hparamCount, htrace, hparams,
    hsort, hcurrent⟩ := source
  exact TypeChecker.checkType_run_hasLooseBVars_eq_false hinferred

theorem CheckedHeaderSource.sourceClosed_of_rangeZeroReflects {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (reflects : types[parent]!.type.looseBVarRange = 0 →
      types[parent]!.type.looseBVarRange' = 0) :
    types[parent]!.type.Closed := by
  have guard := source.sourceHasLooseBVars_eq_false
  simp only [Expr.hasLooseBVars, decide_eq_false_iff_not, Nat.not_lt] at guard
  exact source.sourceFVarsIn.closed_of_looseBVarRange'_le
    (Nat.le_of_eq (reflects (Nat.eq_zero_of_le_zero guard)))

theorem CheckedHeaderSource.sourceClosed_of_rangeAccurate {nparams parent count : Nat}
    {types : Array InductiveType} {original current : Context} {params : Array Expr}
    (source : CheckedHeaderSource nparams types parent original params count current)
    (accurate : types[parent]!.type.looseBVarRange = types[parent]!.type.looseBVarRange') :
    types[parent]!.type.Closed :=
  source.sourceClosed_of_rangeZeroReflects fun zero => accurate.symm.trans zero

end AddInductive
end Lean4Lean
