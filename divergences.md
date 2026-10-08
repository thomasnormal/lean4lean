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

## Abstraction and binding interface boundaries (observed 2026-10-08)

This is an existing **verification-interface scope mismatch**, not evidence of a
Lean kernel soundness bug or different public frontend acceptance. For any free
variable identifier `fvar`, evaluating `(Expr.bvar 0).abstract #[.fvar fvar]` with
Lean 4.29.0 returns `.bvar 0`. The structural model
`(Expr.bvar 0).abstractList [fvar]` returns `.bvar 1`: `Expr.abstract1` lifts existing
loose variables when introducing a binder. The former unconditional
`Expr.abstract_eq` axiom in `Verify.Axioms` equated these expressions, so its full
stated scope did not match executable abstraction on bodies containing loose
variables. The corrected specification described below replaces that equation.

A range-zero body alone is insufficient. Duplicate identifiers expose another
minimal mismatch, without any loose variables in the input:

```lean
import Lean4Lean.Verify.Axioms
open Lean

#eval
  let fvar : FVarId := ⟨`audit⟩
  ((Expr.fvar fvar).abstract #[.fvar fvar, .fvar fvar],
    (Expr.fvar fvar).abstractList [fvar, fvar])
```

The executable result is `.bvar 0`, while the structural result is `.bvar 1`.
Native abstraction selects the last array occurrence; sequential `abstract1`
replaces the first occurrence and then lifts it. Thus any bridge to this
sequential model must also require distinct identifiers, or change the model.
`tests/BindingScope.lean` checks the minimal observation and its forall/lambda
binding consequences with a closed declaration type and range-zero body.

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
arity projection now uses leading-binder preservation of the corrected raw
abstraction model. It still inherits the existing implementation-interface axiom,
but no longer equates native abstraction with unrestricted iterated `abstract1`.
Its arbitrary-body public contract is unchanged.

`Verify.InductiveParamScope` now proves a prerequisite for correctly scoped use:
parameter extraction from a source with structural `looseBVarRange' = 0` produces
range-zero local declaration domains and a range-zero remainder. It exposes actual
indexed getter domains and executable flag projections, and preserves the local
domain property through the preprocessing context frame. The proofs use no
expression-abstraction interfaces. This does not establish scope for opaque
rewritten bodies or source free-variable freshness. Range zero also allows
metavariables and therefore is not the stronger existing `Expr.Closed` predicate. Run
`lake env lean tests/InductiveParamScope.lean` for the premise, metadata, and
ill-scoped/source-capture helper boundaries.

The direct whole-expression reconstruction contracts are now scoped:
`LocalContext.mkBinding_eq` requires a range-zero body, `LocalContext.BindingScope`
(range-zero lookup declaration types and all let values, including nondependent
ones), and a `Nodup` identifier list. Closed bodies alone do not suffice when a
later declaration domain or let value contains loose variables: indexed-prefix
abstraction still differs. `MLCtx.WF.bindingScope` derives the context premise
from translated declarations. `MLCtx.WF.mkForall_partial`, `mkForall_eq`, and
`mkLambda_eq` now require range-zero bodies; their context and distinctness
premises follow from well-formedness. The two concrete callers, the lambda and
let branches in `Verify.TypeChecker.InferType`, obtain body scope from the
cheap-beta-reduced type's translation and the context's no-bound-variable fact.
The new regression reproduces both executable-to-structural and
executable-to-`MLCtx` failures for loose bodies, and indexed-domain/value failures.

### Corrected verification specification (2026-10-08)

`Expr.abstractFVars` is the raw structural model for a free-variable-only array:
it preserves existing bound variables and unmatched metavariables, searches
identifiers from the array's end, and adds the traversal depth to the selected
de Bruijn index. Binder domains and let values retain the current depth; binder
bodies increase it. This follows `lean_expr_abstract_core` in the pinned
Lean 4.29.0 `src/kernel/abstract.cpp`, without reproducing native caches or fast
paths. The existing `Expr.abstract_eq` axiom now relates native abstraction to
this model, not `abstractList`. No additional axiom is declared; this is a
correction of an existing trusted implementation specification, not a formal
proof of the C++ routine or a model for arrays containing metavariable entries.

`abstractFVars_eq_abstractList` proves the sequential model agrees under
structural range/depth scope and distinct identifiers. `abstract_eq_of_scope`
specializes that proof to native abstraction and a range-zero body.
`LocalContext.mkBinding_eq` now actually uses its body/context scope and
distinctness premises for the body and each declaration's indexed prefix.
`arity_abstractFVars` proves raw leading-binder preservation with no implementation
axiom; `arity_abstract` transfers it through the corrected native bridge. Thus
`ParamValidity.mkForall_arity` keeps its arbitrary-body statement without relying
on the incorrect whole-expression sequential equation.

Run `lake env lean tests/NativeAbstraction.lean`: fourteen proof regressions and
fifteen axiom audits accompany 912 raw native/model comparisons, 2736 native arity
checks, and 396 scoped/distinct sequential comparisons. Empty/single/multiple/wide
arrays, duplicate IDs in different positions, all expression constructors,
loose/bound variables, unmatched metavariables with matching free-variable names,
dependent domains/let values, both nondependent-let flags, and depths 0/1/2/33
are covered. The historical loose-variable and duplicate counterexamples remain
regressions against the old sequential specification, not counterexamples to
the corrected raw model. All new audits exclude `sorryAx`; native comparison
theorems inherit only the corrected `Expr.abstract_eq` beyond logical axioms.
No executable checker change, public frontend acceptance mismatch, or kernel
soundness bug is demonstrated. The native implementation bridge remains trusted.

### Scoped source reconstruction (2026-10-08)

`Verify.InductiveParamReconstruction` now proves the conditional source round
trip previously missing at this helper boundary. In addition to structural
range-zero scope, it requires `SourceReserved`: source free variables with the
generator's prefix have indices strictly below the initial generator index.
Other free variables are allowed. This sufficient condition prevents capture
by any generated parameter ID, including a later ID appearing in an earlier
source expression. A scoped source with `hasFVar = false` satisfies it for any
generator; expression and level metavariables need not be excluded.

Fresh instantiation followed by sequential abstraction is inverted structurally
even on loose-bound-variable input. The native source round trip additionally
uses the proved extracted-domain/remainder scope and distinct parameter IDs.
The parameter-context validity contract supplies `LocalContext.BindingScope`
because every extracted declaration is an ordinary constant binder, not a let.
No new axiom is introduced: native abstraction remains connected through the
corrected existing `Expr.abstract_eq` implementation bridge.

The native equality is also supplied to arbitrary continuations, and the direct
extraction-and-re-abstraction callback recovers its source on success.

Run `lake env lean tests/InductiveParamReconstruction.lean`: 624 source fixtures
compare native, sequential, and direct-callback reconstruction. They accompany
twelve current/future source-capture counterexamples,
six loose-source counterexamples, and three unchanged parameter-shortage
diagnostics. All sixteen axiom audits exclude `sorryAx`. The negative fixtures
deliberately bypass source typing/freshness at the extraction helper; they do
not exhibit a newly accepted invalid inductive declaration or a kernel bug.
Discharging these source premises from frontend checking and proving scope for
opaque rewritten constructor bodies remain separate verification obligations.

## Inductive source preflight (2026-10-08)

`Environment.addInductive` now calls `checkInductiveSources` before any parameter
extraction or nested rewriting. The preflight uniformly applies the existing
`checkNoMVarNoFVar` guard to every original header and constructor type; it does
not depend on datatype names, generator prefixes, or the availability of nested
inductive declarations. Header-first, constructor-list, and datatype-list order
determine the first reported error. Existing source metavariable/free-variable
diagnostics retain the offending original name and expression.

This intentionally rejects an invalid source that Lean 4.29.0's native kernel
accepts: a constructor free variable named `_nested_fresh.1` can be captured as
the newly generated parameter. The old lean4lean frontend similarly captures
`_nested_fresh.2`. See the minimal native reproducer and bounded unguarded-stage
regression documented in `bugs-found.md`. Neither observation alone establishes
logical unsoundness; this is a demonstrated source-validation/capture defect.

`Verify.InductiveSourceChecks` proves the preflight's no-metavariable/no-free-variable
contract for all original source types and derives generator-independent
`SourceReserved`. The actual successful `addInductive` and inductive `addDecl`
branches now carry that source contract. The preflight equals `pure ()` on sources
satisfying it, so it leaves valid source processing unchanged. Its eight axiom
audits exclude `sorryAx` and abstraction/instantiation interfaces; they use only
logical axioms and the existing variable-metadata bridges.

Early source errors now take precedence over the old syntactic parameter-count
diagnostic on inputs violating both guards. The frontend arity-rejection equation
records this preflight/error ordering; its unconditional successful-result arity
bound remains intact. Clean-source parameter-shortage diagnostics are unchanged.
The preflight does not prove absence of loose bound variables, semantic typing,
rewritten-body scope, or full inductive soundness. Lower-level preprocessing and
the staged checker remain available with their explicitly separate contracts.

### Adjacent parameterized nested scope gap (observed 2026-10-08)

Validation also exposes an existing downstream rejection, not changed by the
source preflight: a clean datatype `I (A : Type) : Type` with a constructor
`(A : Type) → List (I A) → I A` passes native Lean 4.29.0, but lean4lean reports
`type checker does not support loose bound variables, replace them with free
variables before invoking it`. Eight fixtures in `tests/InductiveSourceChecks.lean`
record this for one/two parameters, both safety modes, and both check settings.
Plain constructors and zero-parameter nested constructors still accept.
These inputs contain no source free variables/metavariables, so the new preflight
is a no-op. Resolving this auxiliary-expression scope/type-checking boundary is
a separate item; the source-capture fix does not establish full nested support.
