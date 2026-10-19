import Lean4Lean.Theory.Typing.HeadInjectivity.Model.Tele

/-! # Chain-level head injectivity

Adapted from PR #53 at 5a8c0d5f111809a95f4924c71e0e9bc8738d72e0.
This is the actual four-field chain contract, independent of admitted injectivity
and confluence. Its fields retain the original ordinary typed links.
-/

namespace Lean4Lean
namespace VEnv

/-- Chain-level head injectivity: the hypothesis of the syntactic layer.

The fields retain ordinary sort-typed chain links. The dependent Pi field relates
domains in the original context and codomains in the context extended by the left
domain. Rigid spines retain universe equivalence and actual typed argument equality. -/
structure ChainHeadInjectivity (env : VEnv) : Prop where
  sort_sort : ∀ {U Γ u v}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.sort u) (.sort v) → u ≈ v
  forallE_chain : ∀ {U Γ A B A' B'}, OnCtx Γ (env.IsType U) →
    env.TypeChain U Γ (.forallE A B) (.forallE A' B') →
    env.TypeChain U Γ A A' ∧ env.TypeChain U (A :: Γ) B B'
  rigid_rigid : ∀ {U Γ c c' ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.Rigid c' →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c' ls') args') →
    c = c' ∧ List.Forall₂ (· ≈ ·) ls ls' ∧ List.Forall₂ (env.IsDefEqU U Γ) args args'
  former_args : ∀ {U Γ c ci doms w ls ls' args args'}, OnCtx Γ (env.IsType U) →
    env.Rigid c → env.constants c = some ci → ci.type = .wrapForalls doms (.sort w) →
    env.TypeChain U Γ (.mkApps (.const c ls) args) (.mkApps (.const c ls') args') →
    SpineArgsEq env U Γ (ci.type.instL ls) args args'

end VEnv
end Lean4Lean
