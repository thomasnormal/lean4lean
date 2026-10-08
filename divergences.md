# Divergences from the Lean Kernel

This is a list of places where lean4lean deliberately has different behavior from the kernel. Unless specified here, any divergence between lean4lean and [lean4](https://github.com/leanprover/lean4/tree/master/src/kernel) is a bug.

* [`Lean4Lean.TypeChecker.Inner.reduceNative`](Lean4Lean/TypeChecker.lean): Lean4lean does not support reduction of `reduceBool`. This would involve implementing verified compilation, which while possible would be an additional chunk of work comparable to this entire repo.
* [`Lean4Lean.Environment.checkPrimitiveDef`](Lean4Lean/Primitive.lean), `checkPrimitiveInductive`: Lean does not check that primitives are declared with the correct types and definitional behavior, except in the case of `Eq` which is used in the declaration of `Quot`. This is required for soundness, but Lean is able to get away with it because Lean ships its prelude and using an alternative prelude is not supported.
* [`Lean4Lean.TypeChecker.Inner.inferType'`](Lean4Lean/TypeChecker.lean), literal case: The original code was not checking that the literal type actually exists. Again, this is okay provided that the prelude is trusted.
* [`Lean4Lean.TypeChecker.Inner.tryStringLitExpansionCore`](Lean4Lean/TypeChecker.lean): there is a counterproductive `whnf` call in this function which is removed in Lean4lean.
* [`Lean.Level.normalize'`](Lean4Lean/Level.lean), `isEquiv'`, `geq'`: Lean4lean implements an experimental new algorithm for level normalization, intended to be complete for level algebra. It is currently known to be incomplete in cases where Lean's algorithm is not (e.g. `max 2 v ≥ imax 2 v` fails, which is reachable from the inductive constructor universe check), so the plan of record is to verify the original algorithm and keep the new one as a backburner project, possibly as part of a hybrid approach to avoid the performance cost in the common case.
* [`Lean4Lean.addDefinition`](Lean4Lean/Environment.lean), `Lean4Lean.addTheorem`: two calls ([1](https://github.com/leanprover/lean4/blob/v4.26.0/src/kernel/environment.cpp#L183) [2](https://github.com/leanprover/lean4/blob/v4.26.0/src/kernel/environment.cpp#L203)) are redundant and have been removed.
* [`Lean4Lean.TypeChecker.Inner.inferLambda`](Lean4Lean/TypeChecker.lean), `inferLet`: lean4lean does the `ensureSort` call before extending the context, while [`infer_lambda`](https://github.com/leanprover/lean4/blob/v4.26.0/src/kernel/type_checker.cpp#L124-L126) does it afterward. It's not clear whether this is actually unsound but it would require some very weird invariants to justify having unchecked things in the local context and hoping that they won't be used in the typing proof of that same expression.
* [`Lean4Lean.checkConstantVal`](Lean4Lean/Environment.lean): The original implementation would call `check` which sets the level params and then unsets them afterward, and then `ensure_sort` would run in a context without any level params. In lean4lean the monad is parameterized over level params, so they remain the same across the two calls.

## Header parameter-normalization boundary (resolved 2026-10-08)

`AddInductive.checkInductiveTypes` weak-head normalizes a datatype's source type
before consuming declared parameters. Lean 4.29.0's native kernel requires those
parameter binders to be explicit in the input expression. With
`abbrev HiddenParameterAlias := Type → Type`, a datatype whose source type is
`.const ``HiddenParameterAlias []`, whose declared parameter count is one, and
whose constructor list is empty succeeds through lean4lean's checked-type/header/
constructor registration prefix. Native `Environment.addDeclCore`, with checking
enabled, rejects the same declaration with
`invalid inductive datatype declaration, incorrect number of parameters`.

This is **not a public frontend divergence or a kernel soundness bug**.
`Environment.addInductive` first calls `ElimNestedInductive.run`, whose
`withParams` operation consumes the first datatype's declared parameters without
normalizing. It already rejects this input with the same parameter-count
diagnostic, before the more permissive isolated prefix is reached. The staged
comparison omitted that earlier preprocessing guard; no executable fix is needed.

`Verify.InductiveParams` proves the exact rejection whenever the first source
datatype's raw leading binder count is below the declared parameter count, and
propagates it through preprocessing and `Environment.addInductive`.
`addDecl.inductiveParamArity` proves every successful nonempty inductive frontend
call satisfies that first-header bound, for either safety or checking flag and
any fuel configuration. It does not prove semantic inductive soundness.

Run the minimal boundary regression with
`lake env lean tests/InductiveHiddenParameter.lean`.
`tests/InductiveArity.lean` compares the isolated prefix, full lean4lean frontend,
and native kernel on 26 safe/unsafe inputs, including parameters hidden after an
explicit binder and behind annotation, beta, or let wrappers. The full frontends
agree: sixteen accept and ten reject; accepted cases check final header counts
and lean4lean's generated recursor. `tests/InductiveParams.lean` additionally
checks both frontend checking flags and zero inductive fuel. Recursor semantics
and unrestricted inductive soundness remain unverified.

Separately, aliases hiding only indices are accepted by both kernels and show
why checked parameter-plus-index counts need not equal raw syntactic binder
arity. The verified general header contract remains a lower bound, not equality;
the syntactic parameter guard must not reject legitimate normalized indices.

## Loose-variable abstraction interface boundary (observed 2026-10-08)

This is an existing **verification-interface scope mismatch**, not evidence of a
Lean kernel soundness bug or different public frontend acceptance. For any free
variable identifier `fvar`, evaluating `(Expr.bvar 0).abstract #[.fvar fvar]` with
Lean 4.29.0 returns `.bvar 0`. The structural model
`(Expr.bvar 0).abstractList [fvar]` returns `.bvar 1`: `Expr.abstract1` lifts existing
loose variables when introducing a binder. The unconditional `Expr.abstract_eq`
axiom in `Verify.Axioms` equates these expressions, so its full stated scope does
not match executable abstraction on bodies containing loose variables.

Run `lake env lean tests/InductiveParamBinding.lean`; `checkAbstractionBoundary`
asserts this minimal observation. With a one-parameter constant-declaration
context, executable `mkForall` therefore wraps `.bvar 0` as the new bound variable,
whereas an iterated structural `abstract1` fold would leave it at `.bvar 1`.
Neither behavior is a source-expression round-trip theorem on unscoped input.
Two additional fixtures show that extraction can capture a free variable already
present in its source when that identifier equals the generated parameter name.
These deliberately bypass source typing/freshness premises at the helper boundary;
they do not exercise public declaration acceptance.

`Verify.InductiveParamBinding` states the exact re-abstraction equation using
executable full-array/body and indexed-prefix/domain abstraction, rather than an
unrestricted iterated `abstract1` model. Its exact-equation audit uses no expression
interface axioms and the regression includes loose bodies and domains. Its raw
arity projection still inherits the existing `Expr.abstract_eq` interface, whose
scope issue remains unresolved. Restricting/replacing that interface and auditing
its callers, or establishing the appropriate well-scopedness premises, is separate
work; no new axiom or executable workaround is introduced here.

`Verify.InductiveParamScope` now proves a prerequisite for correctly scoped use:
parameter extraction from a source with structural `looseBVarRange' = 0` produces
range-zero local declaration domains and a range-zero remainder. It exposes actual
indexed getter domains and executable flag projections, and preserves the local
domain property through the preprocessing context frame. The proofs use no
expression-abstraction interfaces. This does not establish scope for opaque
rewritten bodies, source free-variable freshness, or the full caller audit needed
to restrict `Expr.abstract_eq`. Range zero also allows metavariables and therefore
is not the stronger existing `Expr.Closed` predicate. Run
`lake env lean tests/InductiveParamScope.lean` for the premise, metadata, and
ill-scoped/source-capture helper boundaries. The interface issue remains open.
