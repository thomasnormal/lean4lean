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

## Native binder naming preserves the model context (2026-10-19)

`TrExprS.inst_fvar` now renames an anonymous native binder directly. Its original
freshness/well-formedness premise prevents capture; naming either a lambda or a
let preserves the exact semantic context and expression. Projection evidence
is reused in that context, removing the inherited projection weakening and
instantiation admissions from the complete opening proof and the existing
`TrExpr.openFreshFVar` consumer. Their integration graphs retain exactly `TrProj`;
broader inference and frontend gaps remain. The original API and accepted inputs
are unchanged. See `tests/BinderOpening.lean`. This is a metatheory repair, not a
new native kernel discrepancy.

## Inhabited inverse weakening (2026-10-19)

General inverse weakening through an arbitrary unused binder is false for
semantic conversion; upstream issue #50 records the counterexample.
The substitution lemmas ported from upstream PR #51 prove the inhabited
special case with an explicit typed witness. `Reflection.ite_carrier` now
uses that case, substituting `Prop : Type` rather than the general admission.
The public theorem and executable behavior are unchanged. Its dependency
fixture excludes the false strengthening and confluence theorems while
retaining independent typing admissions. Proof-binder extraction in
`ite_witness` and `natDITE_witness` still uses general strengthening and remains
unrepaired; a witness must not be assumed for an arbitrary proposition.

## False quotient confluence simulation contract (2026-10-15)

This is a verification-model defect, not a newly introduced executable
divergence or a demonstrated native kernel soundness bug. The remaining
`NormalEq.parRed` application/extra contract cannot hold for the actual quotient
instance. In a well-formed context with `P : Prop`, `a : P`, `r : P → P → Prop`,
`f : P → Prop`, a respect proof, and `q : Quot r`, proof irrelevance gives
normal equality between the majors `q` and `Quot.mk r a`. Congruence therefore
gives normal equality between the corresponding `Quot.lift` applications.
The constructor application takes the registered quotient beta step to `f a`.
The neutral application cannot take any non-reflexive step in the current
reduction relation, and its normal equality to `f a` is impossible: neither
the eliminator nor its type-valued result can use proof irrelevance to erase
the distinct function heads.

`Theory.Typing.QuotConfluenceObstruction` proves this exact failure without
using the contradicted theorem, its confluence consequences, or the separately
reported `IsDefEqU.weakN_iff` strengthening admission (upstream issue #50). Its fixture
builds a concrete Eq-plus-Quot semantic environment, audits the independent
inherited typing/injectivity admissions, and keeps endpoint semantic equality
explicitly proved by congruence and beta. `tests/NativeQuotientProofIrrelevance.lean`
is a standalone native control on Lean 4.29.0 and 4.33.0-rc2: major proof
irrelevance and constructor beta close by `rfl`, while lifted congruence and
the final equality need explicit `congrArg`/transitivity proofs. This does not
imply that a checker returning false is unsound; completeness is not the
checker's proved success-only contract.

The existing admission remains visible and unchanged. Repair must preserve
propositional quotient elimination and its actual semantic conversions, not
add an unproved pattern-preservation premise, weaken the model, or reject
otherwise accepted declarations. Confluence-dependent verification claims must
remain conditional on this now-known-false interface until it is repaired.

The first checked repair ingredient is now `QuotPropReduction`: a total
syntax transformer recognizes every zero-equivalent source universe and
unfolds saturated lifts using a constructive `Quot.ind` proof selector.
Its semantic rule preserves the original result type, and its compatible
extension simulates the recorded obstruction. It neither changes native
execution nor rejects declarations. The old relation and its false theorem
remain unchanged; full confluence and downstream migration are not claimed.
Native controls on Lean 4.29.0 and 4.33.0-rc2 validate the selector/unfolding
equations, not completeness of native conversion. The selector direction
already appears in upstream draft PR #53. General soundness still inherits
independent typing admissions, with confluence and strengthening explicitly
excluded from the new dependency graph.

The compatible presentation now includes typed function eta and a complete
quotient-prefix transformer, so the semantic repair ingredient applies to
the bare lift constant and all partial applications, not only saturated
majors. The proof derives the residual signature typing internally and
preserves the original type. Native prefix/function equality controls pass on
Lean 4.29.0 and 4.33.0-rc2 with explicit extensionality and congruence; this
does not add those steps to either executable checker. General confluence,
critical-pair proofs, and downstream migration are still open.

## Candidate-step simulation boundary (2026-10-19)

`QuotCandidateSimulation.normal_candidate_simulates` now simulates every
candidate `Step` and finite `Steps` path from an actual `NormalEq`, using the
repaired left paths and a direct normal comparison at the endpoint. The proof
covers checked original reduction, Prop-source unfolding with neutral majors,
eta expansion, application/lambda/Pi congruence, changing dependent domains,
retained eta binders, and supplied result types. Its dependency audit excludes
the false `NormalEq.parRed`/`parRedS` contracts, `NormalEq.trans`, inverse
weakening, quotient injectivity, `TrProj`, admissions, and choice.

This simulation result does not establish confluence or normal-equality
composition. The existing `NormalEq.trans` implementation still reaches
`NormalEq.weakN_iff`, whose proof in `UniqueTyping.lean` contains the remaining
inverse-weakening admission; its eta-right/eta-left branch is exactly where a
lifted body comparison must be pulled back through a binder. Candidate
simulation composes paths only when an actual candidate path is supplied and
therefore cannot discharge that critical pair. The old theorem and its
downstream consumers remain unchanged and conditional. Any future repair must
prove the missing context conversion constructively before claiming candidate
confluence or unconditional frontend soundness.

## Total inductive elimination-universe selection (2026-10-15)

`AddInductive.getElimLevel` formerly used an opaque `partial` definition for its
unbounded first-unused universe-name search. It is now total, with termination
proved from the maximum string length of the finite input names and the decimal
representation length of each candidate index. No runtime fuel, failure case,
fallback name, or new rejection is added. The search still considers bare `u`
first, then `u_1`, `u_2`, and so on, and preserves the large-elimination
classifier's success and failure results.

The indexed candidates use ordinary verified `String.append` rather than
`Name.appendIndexAfter`, whose implementation calls opaque
`String.Internal.append`. The constructed names have the explicit same ASCII
decimal spelling; runtime tests compare against that original helper through
2049 consecutive indices and 96 large decimal boundary cases. There is no new
axiom equating the two append interfaces and no claimed kernel discrepancy.
Successful selection now proves freshness and scope in the generated recursor
universe telescope. This does not establish the semantic soundness of the
large-elimination classifier, inductive registration, or recursor equations.

## Closed quotient equation pattern boundary (repaired 2026-10-12)

The former `Theory.Typing.ChurchRosser.Params.extra_pat` specification required
every instantiated registered definitional equation to match a reduction pattern
at its root. `Pattern.Matches` only has constant/application cases, but the
actual `quotDefEq.lhs` is a six-lambda abstraction. Instantiating universe levels
preserves that outer lambda. `quotDefEq.not_matches` proves this obstruction for
every pattern and level instance, so the old premise excluded environments
registering the quotient equation even if all confluence admissions were closed.
This is a verification-specification mismatch, not a native kernel discrepancy.

`Pattern.Equation` now permits a guarded registered root reduction under shared
lambda binders. `Pattern.Equation.of_root` converts the exact former certificate,
so existing root rules retain their proof contract. Its `parRed` theorem derives
the actual parallel reduction using the existing rule and lambda constructors,
without borrowing the admitted confluence theorem. The real extra-equation case
of `IsDefEq.church_rosser` consumes the generalized certificate.

`Theory.Typing.QuotPattern` derives this certificate for the unchanged actual
quotient equation at arbitrary universe instances. Its `Quot.lift`/`Quot.mk`
pattern retains domain and relation equality checks; the six shared binders
supply both guards through real bound-variable typing. The equation/result
representation and those proofs have no inherited metatheory admissions.
Run `lake env lean tests/QuotientPatternEquation.lean` for the old root-match
negative, legacy compatibility, concrete and generic universe instances, guarded
quotient certificate, actual parallel-reduction contract and dependency audits.

Subsequent work proves the checked quotient rule's semantic soundness and
constructs a concrete definition/quotient `Params` model from semantic environment
WF. Quotient-type injectivity and automatic parameter alignment now supply a
proof of native `quotReduceRec.WF` and the unchanged `reduceRecursor.WF` contract
in the constructor-free model. These proofs inherit the remaining application/
extra confluence and typing admissions; genuine inductive recursor semantics
remain open. The actual
type checker, quotient registration worker and accepted declaration fragment are
unchanged.

## Reduction-model local contexts (repaired 2026-10-15)

`Theory.Typing.ChurchRosser.Params.pat_wf` formerly required rule soundness in
arbitrary local contexts without a context-WF premise. The actual quotient typing
and conversion proofs require that premise, while every use of the field already
has it. The model interface now receives `OnCtx` explicitly, and `ParRed.defeq`
forwards its existing context certificate at both uses. The parallel-reduction and
confluence theorem statements remain unchanged. This is a verification-interface
repair, not a native kernel discrepancy or an added runtime restriction.

`VEnv.WF.reductionParams` constructs the concrete registered definition/quotient
model with equation coverage and all non-overlap obligations proved from the WF
declaration history. `tests/ConcreteReduction.lean` checks actual reduction and
confluence consumers and rules out circular dependence of model construction on
those consumers. The remaining generic confluence and unique-typing admissions
are not removed by this interface repair or model construction.

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

### Parameterized nested auxiliary scope (resolved 2026-10-08)

Validation exposed an existing downstream rejection, unrelated to the source
preflight: a clean datatype `I (A : Type) : Type` with a constructor
`(A : Type) → List (I A) → I A` passes native Lean 4.29.0, but lean4lean reported
`type checker does not support loose bound variables, replace them with free
variables before invoking it`. Preprocessing and the staged inductive checker
both succeeded; the final auxiliary check passed parameter-abstracted expressions
directly to a checker expecting free variables in the retained local context.

Preprocessing now retains its actual chronological parameter array alongside
that context. `Result.openAux` uses reverse instantiation to open every auxiliary
before final type checking. No parameters are synthesized, no type checks are
skipped, and the existing loose-variable guard remains unchanged. All 24 clean
fixtures in `tests/InductiveSourceChecks.lean` now accept, including the eight
previously rejected parameterized nested inputs.

`Verify.InductiveNestedScope` proves that successful preprocessing retains the
exact parameter array with its context validity and order. It proves that opening
an expression whose structural bound-variable range is at most the parameter
count leaves range zero, and connects this to the actual loose-variable flag.
The auxiliary-range premise remains explicit: this does not prove range bounds
for arbitrary nested rewrites, semantic auxiliary typing, positivity, recursors,
or full inductive soundness. The eight audits exclude `sorryAx`; they inherit only
logical axioms and existing context/instantiation/range interfaces.

Run `lake env lean tests/InductiveNestedScope.lean` for the stage-isolated
raw/opened regression, 36 retained-context scope checks, and 144 native/frontend
acceptance and restored-type comparisons. Fixtures cover zero through four
parameters, dependent parameter domains, concrete/polymorphic universes,
`List`, `Option`, and composed nesting, both safety modes, and both check settings.
Out-of-range auxiliary variables still retain loose-variable metadata.

### Nested parameter rebinding scope bridge (2026-10-08)

`Verify.InductiveNestedRebinding` now derives the auxiliary-range bound for the
actual `replaceParams`/final-abstraction/opening chain, provided its original
nested parameter prefix has range zero and its source/target parameter arrays
come from equal-sized structural parameter contexts. Native abstraction is
bounded by the maximum of the original range and parameter count. Rebinding
then leaves range zero and preserves the preprocessing state; final abstraction
has range at most the parameter count, and `Result.openAux` discharges the actual
loose-variable flag. This chain no longer assumes scope of its rewritten output.

The general raw abstraction bound also holds under arbitrary binder depths,
duplicate identifiers, and initially loose source expressions. It introduces no
new admission or implementation axiom. Eight axiom audits exclude `sorryAx`;
only the existing logical, abstraction/instantiation, and range-metadata
interfaces are inherited. No executable checker change is required.

Run `lake env lean tests/InductiveNestedRebinding.lean` for 216 scoped
rebinding/auxiliary comparisons using actual parameter extraction/preprocessing,
300 structural/native abstraction comparisons, and two necessary-premise
boundaries. Fixtures cover zero through 65 parameters, dependent domains,
different generators, all expression constructors, duplicate identifiers,
existing loose variables, and four binder depths.

The negative helper fixtures deliberately bypass the nested-app guard: a loose
source bound variable can become a target free variable during rebinding, while
a target containing a bound variable can introduce a scope error. These do not
exhibit newly accepted invalid frontend declarations or a kernel bug. Proving
the complete traversal/auxiliary map scope remains the next step; the guard's
parameter-prefix scope is now proved below. Semantic typing,
positivity, recursors, and full inductive soundness remain separate.

### Checked nested-app parameter scope (2026-10-08)

`Verify.InductiveNestedGuard` proves the existing classifier's successful-result
contract: state identity, a constant head, enough arguments, and no loose bound
variables in each parameter argument. It derives structural range zero and the
actual loose-variable metadata flag for the exact parameter prefix passed to
`replaceParams`. The checked rebinding/final-abstraction/opening chain now needs
parameter-context validity but no separate source-prefix or output-range premise.

This contract does not claim scope of the entire application. Loose indices are
permitted when the parameter prefix is scoped; an indexed-family regression
records that boundary. A non-nested expression with loose arguments still returns
`none`, and insufficient arguments take precedence over the loose-parameter
diagnostic. The executable guard, diagnostics, and error order are unchanged.

Run `lake env lean tests/InductiveNestedGuard.lean`: seven axiom audits accompany
768 guard/rebinding fixtures (672 accepts/96 `none`), 168 loose-parameter
rejections, 64 arity-boundary `none` cases, and seven classification/index
boundaries. Native-checked containers span zero through 65 parameters; local
fixtures cover different generators, zero through 33 extracted parameters, and
all expression constructors. Those fixtures test classifier/rebinding scope,
not semantic typing or acceptance of complete invalid declarations.

Both classifier/frame audits use only logical axioms; the remaining audits use
only the existing range-metadata/application-building/abstraction/instantiation
interfaces and exclude `sorryAx`. No new implementation axiom, admission, checker
workaround, or kernel discrepancy is introduced. Scope propagation through the
complete rewrite traversal and auxiliary map, auxiliary semantic typing,
positivity, recursors, and full inductive soundness remain separate obligations.

## Trusted native instantiation specification mismatch (2026-10-10)

The pinned Lean **4.29.0** native substitution is simultaneous, but before the
repair below the `Verify.Axioms.Expr.instantiate_eq` interface universally
identified it with sequential structural `instantiateList`. That former
specification is false for replacement arrays containing loose bound variables.
For example, native `(Expr.bvar 0).instantiateRev #[.sort .zero, .bvar 0]`
returns `.bvar 0`.
The corresponding structural `instantiateRevList` first inserts `.bvar 0`,
then substitutes through that inserted value and returns `.sort .zero`.
The same discrepancy occurs for forward instantiation with the reversed array
and beneath a lambda binder. `Expr.instantiateRev_eq`, which relates the two
native array orders, is not itself contradicted by these examples.

Run `lake env lean tests/NativeInstantiation.lean`. It reproduces these three
loose-argument boundaries and checks the corrected simultaneous model on raw
loose/mixed/closed arrays as well as 72 sequential comparisons for closed
replacement arrays. The counterexamples concern an
existing trusted verification specification, not a C++ kernel bug or a newly
accepted invalid declaration. No executable checker change or proof of kernel
unsoundness is demonstrated.

The new whole-prefix replacement contract restricts raw native/structural
agreement to a range-zero body and structurally closed replacement arguments.
Its typed contract derives every replacement's closure from strict translation
in the remaining mixed base, so these negatives cannot supply its hypotheses.
It does not assume a latest dependent argument is already typed at an
unsubstituted source domain: chronological typed application checks each domain
after earlier arguments have been instantiated. The correction below replaces
the false implementation specification; inherited typing admissions and the
trusted native implementation bridge still preclude an unconditional kernel
soundness claim.

### Simultaneous model repair (2026-10-10)

`Expr.instantiateMany` now models the pinned native implementation directly:
protected bvars remain unchanged, array-selected arguments are inserted once
with the current binder-depth lift, and indices beyond the substitution prefix
are decremented by its length. Domains and let values use the current depth;
binder bodies increase it. Inserted replacement expressions are not recursively
substituted by later array entries. All expression constructors are covered.
The existing `Expr.instantiate_eq` axiom now relates native instantiation to
this simultaneous model. No new axiom is declared; this repairs a trusted
implementation specification, not a formal proof of the C++ routine.

Structural proofs establish empty/scalar instantiation, preservation below a
scope cutoff, general replacement range bounds, and agreement with sequential
`instantiateList` when replacements are closed. The corresponding native
forward/reverse sequential bridges retain that closure premise. The old
unrestricted `instantiateRev_push` equation also needed repair: the pushed
argument must be closed, while the earlier array entries may still be loose.
The historical counterexample remains a regression against the retired
sequential specification, not a counterexample to the corrected raw model.

Type-checker opening/inference and definitional-equality proofs now discharge
argument scope from actual fresh fvars or translated application arguments.
The internal lambda/forall comparison helpers make this formerly missing
closure receipt explicit; the public checked comparison contract is unchanged.
The general nested-rewrite range proof uses simultaneous replacement range
bounds and still allows nonzero-range replacement arguments. Scoped singleton
and whole-prefix parameter replacement retain their strict typing contracts
without adding a native interface or admission.

The raw native/model test matrix includes loose/mixed/wide arrays, large
representable bvar indices, all constructors, both let flags, metadata/projections
and binder depths 0/1/2/5/33. It passes 2640 raw comparisons and 3960 checks of
the repaired native push identity for a closed pushed value with arbitrary
earlier arrays; a separate loose-push negative pins the closure boundary.
The large-index case uses `2^19`: native expression metadata has a 20-bit
loose-variable range, so `2^40` is outside its supported representation and
panics during expression construction, before substitution.
Structural proof audits exclude `sorryAx` and native interfaces; the native
bridges admit only the existing
general/reverse instantiation interfaces. Existing typing admissions, remaining
native implementation bridges and full inductive frontend correctness remain
separate obligations.

## Upstream empty-environment stage compatibility (2026-10-12)

During the local rebase onto official `67f63b0`, the existing empty translation
constructor described only the default `SMap` stage-1 map, but upstream's actual
`Kernel.Environment.empty` defaults to an empty stage-2 map. Both maps have no
constants; their stage flag determines which storage receives later insertions.
Merely changing the checker proof's fuel parameter does not restore the fork's
empty-environment semantic contract across this difference.

The isolated, validated replay checkpoint `c83d6b0` generalizes the empty
`TrEnv'` and alignment constructors over the stage flag, proves empty lookup and
well-formedness for both storage stages, and derives `VEnvs.WF.empty` for the
actual upstream default. This is a translation-domain compatibility repair,
**not a native kernel bug or a runtime acceptance change**. It does not switch
upstream to stage 1, add an axiom, or claim inductive registration is verified.
The actual non-inductive batch/from-empty proofs compile and pass their direct
admission/dependency audit on Lean 4.33.0-rc2, with inherited checker admissions
and native interfaces still present. This checkpoint is unpublished; the full
rebase and final integration validation remain unfinished.

## Primitive compatibility during upstream rebase (2026-10-12)

The historical safe-definition patch temporarily removed all binary native
arithmetic and its model invariants while literal primitive extension was being
proved. Current official upstream already supplies the full primitive-spec
preservation and reduction proofs. The isolated replay `dc21754` therefore keeps
those stronger guarantees rather than mechanically reinstating the old removals
or replacing the new primitive table with the old literal-only record.

It also retains official `67f63b0`'s metadata-aware header comparison and checks
the declaration type/body before recognizer comparisons. Candidate regressions
exercise actual fresh-slot addition for `Nat.add`, `Char.ofNat`, and
`String.ofList`: domain metadata accepts, misplaced codomain metadata rejects,
unsafe/partial or extra-universe primitive headers reject, missing String
constructor dependencies reject, and an ill-typed body yields the body-check
diagnostic before any recognizer probe. Direct native arithmetic/predicate
results are checked without fallback unfolding. These native-prelude controls
are runtime evidence, not a `TrEnv` model for that prelude.

The primitive-only extension theorem is a consequence of the stronger actual
declaration proof, and the actual checker exposes a primitive preservation
receipt. No new admission or axiom is introduced; their inherited checker and
native-interface assumptions remain explicit. This is a local integration
checkpoint, not publication of the rebase or removal of the published branch's
four disabled-operation boundaries.

## Non-inductive frontend compatibility during upstream rebase (2026-10-12)

The isolated checkpoints `9a95087` and `f9879f7` restore the verified frontend
wrapper and its all-non-inductive preservation contract on the current upstream
workers. Older unsafe-header/mutual-block scaffolding is superseded by the
stronger checked `TrDefBlock`/block-extension model, not reinstated alongside it.
The historical safe-only delta restriction is also superseded locally by
upstream's native `deltaValue?` semantics and actual unfolding proof: definitions
and theorems qualify at the right universe arity, opaques do not, and safe
declarations still cannot use unsafe or partial dependencies. The published
branch's behavior has not changed.

The fuel-sensitive `addQuotVerified` worker is retained separately from the
official quotient worker. It checks each generated header and fresh name,
rejects exhausted callback fuel before initialization, and is idempotent after
initialization. Equality readiness retains the fork's safety and genuine
constructor-kind guards without deleting upstream's type-shape or quotient
freshness checks. These controls are tested against native-prelude inputs;
manually malformed environment variants are rejection fixtures, not evidence
of a native declaration-acceptance bug.

The current model still cannot contain inductive `Eq`. Consequently, the actual
and verified quotient preservation proofs have an impossible successful
uninitialized case. The original low-level quotient insertion scaffolding is
not presented as a constructive model for the native prelude. Proving such a
model remains an inductive-registration obligation. Direct-admission and
dependency audits pass, with inherited checker admissions and native interfaces
unchanged; neither the full rebase nor admission-free kernel soundness is
established by this checkpoint.

## Level comparison compatibility during upstream rebase (2026-10-12)

The isolated checkpoint `785d1da` keeps the official native-fast-path plus
complete canonical `geq'`/`isEquiv'` APIs and their completeness proofs. The
historical total flatten/sort/subsume normalizer and its evaluation theorem are
restored alongside them, not used to overwrite those stronger public APIs.
The separate native correspondence helper retains the `geqCoreStd` name, so
neither comparator silently shadows the other.

The old fixture required equality between native and fork acceptance. That is
no longer the right contract: native fast paths are deliberately incomplete.
New controls prove and exercise the actual complete checker on
`max left (imax right left) ≡ imax right left` and
`imax (max left right) condition ≥ imax left condition`, both rejected by the
installed native fast path. Generated controls retain all native acceptances
while allowing additional valid ones. This is preservation of already-upstream
completeness, not a newly found native soundness bug or an original proof to send
back upstream.

The total helper's normal-form agreement remains regression evidence, not a
universal syntactic theorem. Its evaluation theorem uses the existing
named-valuation semantics; public virtual-level completeness requires a
successful translation and does not include metavariables. Six metavariable
controls check syntax only. Sixteen audited level contracts have no direct or
inherited admissions, but still depend on existing named native interfaces,
including the tree-map `all`/`any` specifications and native level operations.
`Std.TreeMap.any_eq_any_toList` was already in the canonical-level proof
baseline; it is not a newly added axiom or an excuse to claim the wider kernel
dependency stack is admission-free. The final rebase is still unfinished.

## Nat.add primitive compatibility during upstream rebase (2026-10-12)

The isolated checkpoints `0af54e3` and `0fb93bc` retain the stronger upstream
primitive architecture. The replay cleanup keeps the actual module-region
projection before region release. The historical primitive commit's edits to an
older monolithic `checkPrimitiveDef` are superseded by upstream's extracted
typed local-probe clauses; no obsolete wrapper or arithmetic implementation is
reintroduced just to reproduce historical source shape.

The useful semantic part is retained as `VEnv.NatAddSpec`: open zero/successor
equations imply literal evaluation and reflection after a checked definition is
identified with the translated function. `tests/RebasedNatAdd.lean` audits the
contract, and `tests/Primitive.lean` checks positive lambda wrappers plus
negative forall and wrong-domain wrappers. The current primitive clauses and
their `PrimitiveResult` remain the actual recognizer-preservation proof. The
Nat.add compatibility lemmas have no direct admission or new axiom declarations,
but their transitive typing/equation proof uses the existing `sorryAx`, classical,
and quotient/interface baseline; it is not advertised as admission-free kernel
soundness. No native binary arithmetic operation is re-enabled by this replay.
## AddInduct registration boundary (2026-10-19)

`NativeInductive.RegistrationEvidence.aligned` proves the staged semantic
alignment that is available today: header constants are added against the
pre-block model environment, constructor constants against the header
environment, and each phase preserves freshness and the native/model constant
map. The theorem also composes the existing native `addInduct`-with-recursor
receipt, but it does not claim recursor or ι-rule semantics.

The remaining `Verify.Environment.Basic.AddInduct` relation is intentionally
constructor-free. Making it constructible from those receipts would change a
separate global contract: `TrEnv'.inductiveLookupRejected`,
`TrEnv.inductiveNotInModel`, and the projection, recursor, and comparison
consumers currently prove that no inductive-family lookup can enter the model.
An aligned header/constructor witness would make those rejection statements
false for a safe inductive block, so filling `AddInduct` requires a coordinated
migration of that noninductive fragment and a new model for generated
recursors. The staged alignment theorem is therefore recorded as a valid
registration prerequisite rather than being unsafely wired into `TrEnv`.

This is a semantic boundary, not an executable-kernel discrepancy. The next
inductive item must either replace the rejection contracts with an inductive-
aware environment relation or remain within the current constructor-free
fragment.
