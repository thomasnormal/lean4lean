import Lean4Lean.Verify.StagedLocals
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.TypeChecker
open private Lean.Kernel.Environment.add from Lean.Environment

namespace StagedLocalsTest

private def native := Kernel.Environment.empty `StagedLocalsTest

private theorem primitiveSafety : NativePrimitiveSafety native :=
  NativePrimitiveSafety.of_native SMap.WF.empty
    (VEnvs.WF.empty `StagedLocalsTest).safePrimitives

private theorem primitives : VEnv.empty.HasPrimitives :=
  (VEnvs.WF.empty `StagedLocalsTest).hasPrimitives (safety := .safe)

private def context : RestrictedContext .safe native VEnv.empty :=
  RestrictedContext.emptyScope (CheckerEnv.empty _) primitives primitiveSafety []

private def methods : Methods := {
  isDefEqCore := fun _ _ => throw .deepRecursion
  whnfCore := fun _ _ _ => throw .deepRecursion
  whnf := fun expression => pure expression
  inferType := fun _ _ => throw .deepRecursion }

private def continuation : Expr → RecM Expr
  | .fvar identifier => fun _ reader state =>
    (Inner.inferFVar reader identifier).map fun result => (result, state)
  | _ => throw .deepRecursion

private theorem continuationWF (context : RestrictedContext .safe native VEnv.empty)
    {identifier : FVarId} {model : MLCtx}
    (extendedWF : model.WF
      VEnv.empty context.lparams) :
    (context.withMLC _ extendedWF).RunWF methods
      (context.withMLC _ extendedWF).StateWF
      (continuation (.fvar identifier)) fun result =>
        ∃ semantic type, TrTyping VEnv.empty
          (context.withMLC _ extendedWF).lparams
          (context.withMLC _ extendedWF).scope
          (.fvar identifier) result semantic type := by
  intro initial initialWF returned success
  change ((fun result => (result, initial)) <$>
    Inner.inferFVar (context.withMLC _ extendedWF).toContext identifier) = .ok returned at success
  cases headSuccess : Inner.inferFVar (context.withMLC _ extendedWF).toContext identifier with
  | error exception =>
    simp only [headSuccess, Functor.map, Except.map] at success
    cases success
  | ok result =>
    simp only [headSuccess, Functor.map, Except.map] at success
    cases success
    obtain ⟨semantic, type, translated, typed⟩ :=
      (context.withMLC _ extendedWF).inferFVar result headSuccess
    exact ⟨initialWF, semantic, type, translated, typed⟩

private theorem propHasType : VEnv.empty.HasType 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort (show VLevel.WF 0 .zero from by trivial)

private theorem propType : VEnv.empty.IsType 0 [] (.sort .zero) :=
  ⟨.succ .zero, propHasType⟩

private theorem localBinderWF :
    context.RunWF methods context.StateWF
      (withLocalDecl `argument .default q(Prop)
        (continuation)) fun _ =>
      True := by
  apply RestrictedContext.RunWF.withLocalDecl
    (domainTr := (TrExprS.sort (u := .zero) rfl))
    (domainType := propType)
  intro identifier extendedWF
  exact (continuationWF context extendedWF).mono fun _ _ => trivial

private theorem localLetWF :
    context.RunWF methods context.StateWF
      (withLetDecl `bound q(Type) q(Prop)
        continuation) fun _ =>
      True := by
  apply RestrictedContext.RunWF.withLetDecl
    (domainTr := (TrExprS.sort (u := .succ .zero) rfl))
    (valueTr := (TrExprS.sort (u := .zero) rfl))
    (valueType := propHasType)
  intro identifier extendedWF
  exact (continuationWF context extendedWF).mono fun _ _ => trivial

private theorem localBinderEmpty :
    context.StateWF ({ ngen := { namePrefix := `StagedLocalsTest, idx := 0 } } : State) := by
  apply RestrictedContext.StateWF.empty
  intro identifier member
  cases member

private def audit (name : Name) (expected : List Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.size == expected.length && axioms.all expected.contains do
    throwError "{name}: unexpected dependencies: {repr axioms}"
  logInfo m!"{name}: axioms = {repr axioms}"

run_meta
  let logical := [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]
  let cache := logical ++ [``Lean.PersistentHashMap.WF.find?_eq,
    ``Lean.PersistentArray.toList'_push, ``Lean.PersistentHashMap.WF.toList'_insert]
  let empty := logical ++ [``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel,
    ``Lean.Syntax.structEq_eq]
  for name in [``RestrictedContext.StateWF.find?_eq_none,
      ``RestrictedContext.StateWF.freshLambda, ``RestrictedContext.StateWF.restoreLambda,
      ``RestrictedContext.StateWF.freshLet, ``RestrictedContext.StateWF.restoreLet,
      ``RestrictedContext.inferFVar, ``RestrictedContext.RunWF.withLocalDecl,
      ``RestrictedContext.RunWF.withLetDecl] do
    audit name cache
  audit ``RestrictedContext.StateWF.empty empty
  audit ``localBinderEmpty (logical ++ [``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.Expr.eqv_eq, ``Lean.Level.instLawfulBEqLevel, ``Lean.Syntax.structEq_eq])
  audit ``continuationWF cache
  audit ``localBinderWF (logical ++ [``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentArray.toList'_push,
    ``Lean.PersistentHashMap.WF.toList'_insert])
  audit ``localLetWF (logical ++ [``Lean.PersistentHashMap.findAux_isSome,
    ``Lean.PersistentHashMap.WF.find?_eq, ``Lean.PersistentArray.toList'_push,
    ``Lean.PersistentHashMap.WF.toList'_insert])
  let initial : State := { ngen := { namePrefix := `StagedLocalsTest, idx := 0 } }
  let reader : Context := { env := native }
  let .ok (result, final) :=
      (withLocalDecl `argument .default q(Prop) continuation) methods reader initial
    | throwError "native local binder control failed"
  unless result == .sort .zero do
    throwError "native local binder returned the wrong type"
  unless final.ngen.namePrefix == `StagedLocalsTest && final.ngen.idx == 1 do
    throwError "native local binder did not advance and restore the state"
  let .ok (result, final) :=
      (withLetDecl `bound q(Type) q(Prop) continuation) methods reader initial
    | throwError "native local let control failed"
  unless result == .sort (.succ .zero) do
    throwError "native local let returned the wrong type"
  unless final.ngen.namePrefix == `StagedLocalsTest && final.ngen.idx == 1 do
    throwError "native local let did not advance and restore the state"
  logInfo "one native local-binder and one native local-let allocation, lookup, and restoration control"

end StagedLocalsTest
