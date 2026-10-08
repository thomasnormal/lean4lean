import Lean4Lean.Primitive
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.Environment
open Lean hiding Environment Exception

inductive PrimitiveInductiveDecl : List Name → Nat → List InductiveType → Bool → Prop where
  | bool : PrimitiveInductiveDecl [] 0 [{
      name := ``Bool
      type := .sort (.succ .zero)
      ctors := [⟨``Bool.false, .const ``Bool []⟩, ⟨``Bool.true, .const ``Bool []⟩]
    }] false
  | nat (binderName : Name) (binderInfo : BinderInfo) : PrimitiveInductiveDecl [] 0 [{
      name := ``Nat
      type := .sort (.succ .zero)
      ctors := [⟨``Nat.zero, .const ``Nat []⟩,
        ⟨``Nat.succ, .forallE binderName (.const ``Nat []) (.const ``Nat []) binderInfo⟩]
    }] false

theorem checkPrimitiveInductive.eq_true_iff (env : Kernel.Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    checkPrimitiveInductive env lparams nparams types isUnsafe = .ok true ↔
      PrimitiveInductiveDecl lparams nparams types isUnsafe := by
  constructor
  · intro hcheck
    have hheader : !isUnsafe && lparams.isEmpty && nparams == 0 := by
      by_contra hheader
      simp [checkPrimitiveInductive, hheader, pure, Except.pure] at hcheck
    have ⟨⟨hsafe, hparams⟩, hnparams⟩ :
        (isUnsafe = false ∧ lparams = []) ∧ nparams = 0 := by simpa using hheader
    subst isUnsafe lparams nparams
    rcases types with _ | ⟨⟨name, type, ctors⟩, _ | ⟨other, types⟩⟩
    all_goals simp [checkPrimitiveInductive, pure, Except.pure, Bind.bind, Except.bind] at hcheck
    all_goals repeat' (split at hcheck <;> try simp_all [Expr.eqv_sort])
    all_goals first | exact .bool | exact .nat _ _
  · intro hdecl
    cases hdecl <;> simp [checkPrimitiveInductive, pure, Except.pure, Bind.bind, Except.bind]

theorem checkPrimitiveInductive.WF (env : Kernel.Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool) :
    (checkPrimitiveInductive env lparams nparams types isUnsafe).WF fun isPrimitive =>
      isPrimitive = true → PrimitiveInductiveDecl lparams nparams types isUnsafe := by
  intro isPrimitive hcheck htrue
  subst isPrimitive
  exact (checkPrimitiveInductive.eq_true_iff env lparams nparams types isUnsafe).mp hcheck

end Lean4Lean.Environment
