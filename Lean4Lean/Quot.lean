import Batteries.Tactic.OpenPrivate
import Lean4Lean.Environment.Basic
import Lean4Lean.Expr
import Lean4Lean.Instantiate
import Lean4Lean.LocalContext

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add markQuotInit from Lean.Environment

abbrev ExprBuildT (m) := ReaderT LocalContext <| ReaderT NameGenerator m

def ExprBuildT.run [Monad m] (x : ExprBuildT m α) : m α := x {} {}

instance : MonadLocalNameGenerator (ExprBuildT m) where
  withFreshId x c ngen := x ngen.curr c ngen.next

private def eqTypeExpr (u : Name) : Expr :=
  .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0) (.forallE `b (.bvar 1) .prop .default) .default) .implicit

private def eqReflTypeExpr (u : Name) : Expr :=
  .forallE `α (.sort (.param u))
    (.forallE `a (.bvar 0)
      (mkApp3 (.const ``Eq [.param u]) (.bvar 1) (.bvar 0) (.bvar 0)) .default) .implicit

private def quotTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.arrow (.bvar 0) <| .arrow (.bvar 1) .prop)
      (.sort (.param `u)) .default) .implicit

private def quotMkTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.arrow (.bvar 0) <| .arrow (.bvar 1) .prop)
      (.forallE `a (.bvar 1)
        (mkApp2 (.const ``Quot [.param `u]) (.bvar 2) (.bvar 1)) .default) .default) .implicit

private def quotLiftTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.arrow (.bvar 0) <| .arrow (.bvar 1) .prop)
      (.forallE `β (.sort (.param `v))
        (.forallE `f (.arrow (.bvar 2) <| .bvar 1)
          (.forallE `c
            (.forallE `a (.bvar 3)
              (.forallE `b (.bvar 4)
                (.arrow (mkApp2 (.bvar 4) (.bvar 1) (.bvar 0))
                  (mkApp3 (.const ``Eq [.param `v]) (.bvar 4)
                    (.app (.bvar 3) (.bvar 2)) (.app (.bvar 3) (.bvar 1)))) .default) .default)
            (.arrow (mkApp2 (.const ``Quot [.param `u]) (.bvar 4) (.bvar 3)) (.bvar 3))
            .default) .default) .implicit) .implicit) .implicit

private def quotIndTypeExpr : Expr :=
  .forallE `α (.sort (.param `u))
    (.forallE `r (.arrow (.bvar 0) <| .arrow (.bvar 1) .prop)
      (.forallE `β
        (.forallE `q (mkApp2 (.const ``Quot [.param `u]) (.bvar 1) (.bvar 0)) .prop .default)
        (.forallE `mk
          (.forallE `a (.bvar 2)
            (.app (.bvar 1) (mkApp3 (.const ``Quot.mk [.param `u])
              (.bvar 3) (.bvar 2) (.bvar 0))) .default)
          (.forallE `q (mkApp2 (.const ``Quot [.param `u]) (.bvar 3) (.bvar 2))
            (.app (.bvar 2) (.bvar 0)) .default) .default) .implicit) .implicit) .implicit

private def eqReady? (env : Environment) : Bool :=
  match env.find? ``Eq with
  | some (.inductInfo info) =>
    match info.levelParams, info.ctors with
    | [u], [eqRefl] => !info.isUnsafe && info.type == eqTypeExpr u &&
      match env.find? eqRefl with
      | some (.ctorInfo info) =>
        match info.levelParams with
        | [u] => !info.isUnsafe && info.type == eqReflTypeExpr u
        | _ => false
      | _ => false
    | _, _ => false
  | _ => false

def checkEqType (env : Environment) : Except Exception Unit :=
  if eqReady? env then pure () else
    throw <| .other "failed to initialize quot module, unexpected declaration of 'Eq'"

def Environment.addQuot (env : Environment) : Except Exception Environment := do
  if env.quotInit then return env
  checkEqType env
  let env := env.add <| .quotInfo {
    name := ``Quot, kind := .type, levelParams := [`u], type := quotTypeExpr }
  let env := env.add <| .quotInfo {
    name := ``Quot.mk, kind := .ctor, levelParams := [`u], type := quotMkTypeExpr }
  let env := env.add <| .quotInfo {
    name := ``Quot.lift, kind := .lift, levelParams := [`u, `v], type := quotLiftTypeExpr }
  let env := env.add <| .quotInfo {
    name := ``Quot.ind, kind := .ind, levelParams := [`u], type := quotIndTypeExpr }
  return markQuotInit env

def quotReduceRec [Monad m] (e : Expr) (whnf : Expr → m Expr) : m (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  let cont mkPos argPos := do
    let args := e.getAppArgs
    if h : mkPos < args.size then
      let mk ← whnf args[mkPos]
      if !mk.isAppOfArity ``Quot.mk 3 then return none
      let mut r := Expr.app args[argPos]! mk.appArg!
      let elimArity := mkPos + 1
      if elimArity < args.size then
        r := mkAppRange r elimArity args.size args
      return some r
    else return none
  if fn == ``Quot.lift then cont 5 3
  else if fn == ``Quot.ind then cont 4 3
  else return none
