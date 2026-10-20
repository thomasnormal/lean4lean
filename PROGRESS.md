# Progress and upstream comparison

Last reviewed: **2026-10-20 (UTC)**. This is the readable overview of the
`poc-verified-noninductive` branch; [PROOF_STATUS.md](PROOF_STATUS.md) holds the
detailed theorem contracts, dependency audits, and regression evidence.

## Bottom line

Our fork has substantial additional checker verification, primitive proofs,
inductive staging work, and regression coverage. It is **not a completed
verification of Lean's kernel**, and it is **not uniformly ahead of official
lean4lean**. Upstream has independently proved ordinary declaration checking
and added newer primitive and universe-level results that our branch has not
fully integrated into the published branch. Its admission-free simultaneous
substitution proof is narrowly ported here; that is foundation integration,
not completion of frontend soundness.

**Published versus upstream integration:** the main review branch retains its
older base on Lean **4.29.0**, including the direct binder-naming proof below.
This separate integration snapshot is based on official
`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` on Lean **4.33.0-rc2**,
extending checkpoint `c65a7a0`. It integrates the later quotient semantics,
the actual native quotient/recursor dispatcher proof, the checked confluence
obstruction, and the typed Prop-source/prefix repair ingredients. Upstream's
mutual-definition declarations and executable behavior are retained. This is
a partial integration: current reflection uses a different primitive architecture,
and later native restoration receipts still need replay. Publishing this snapshot
on a separate branch does not rebase or replace the main review branch.

**Inhabited telescope repair:** well-founded recursion now discharges two direct
inverse-weakening obligations by substituting zero for the Nat binders certified
by its existing guard. The new generic helpers support dependent telescopes and
a retained binder depending on the base context; their dependency audits exclude
admissions, choice, false strengthening and confluence. Public theorem premises
and executable behavior are unchanged. The full recursion theorem still inherits
general strengthening through checker dependencies. Three further context
extractions for the guarded measure telescope now use abstraction and typed zero instantiation, including
beneath the retained packed-argument binder. These native translation helpers
exclude false strengthening and confluence; they retain exactly the existing
projection definition, weakening and instantiation admissions, standard logic,
and three native persistent-container interfaces.
The abstraction/typed-zero direction also exists in draft
[upstream PR #53](https://github.com/digama0/lean4lean/pull/53), whose
`MLCtx.trExprS_dropN_nat` and larger recursion redesign were inspected at
`5a8c0d5`. This checkpoint repairs the current contracts and supplies explicit
trust audits; no duplicate upstream PR is opened.
The remaining direct fuel extraction now follows #53's same-context successor
replacement: the checked `succ t` witness stays under the original fuel binder,
and the induction consumes the resulting equality at adjacent fuel closings.
The intermediate `Step` witness states that equality instead of asserting an
outer-context translation. WF′/WF/WF₂ keep their exact top-level contracts.
All direct general-strengthening/extraction calls in WF′ are now removed;
transitive checker admissions remain. The new replacement helper pins three
inherited projection admissions, and its equality bridge pins three projection admissions.
Full default builds and all selected regression fixtures pass on both
toolchains. No new admission is introduced.

**Registered recursor checker extension (October 20):** the actual generated
recursor scope now supplies a model extension with `CheckerEnv`. The proof
constructs each constant from its generated-type receipt and follows the
native name checks to prove insertion succeeds in parent order, preserving
old constants, equations and value translations. Selected-domain and pass
support, parameter-free statistics, matching universe lists and an empty
initial virtual context remain explicit. The insertion theorem retains the
existing checker/value-translation admissions and native lookup interfaces;
no new admission is introduced. Complete inductive registration, rule/iota
semantics, consumer migration and `AddInduct` remain open.
The expanded recursor regression and full default builds pass on Lean 4.29.0
and the separate Lean 4.33.0-rc2 integration candidate.

**Recursive rule translation stage:** rule-body receipts now use the model
after all mutual recursor signatures are inserted. The old constructor-stage
premise is impossible for fresh recursive calls; a formal constant-occurrence
obstruction and exact generated single/mutual RHS controls establish why.
Recursor types still translate before insertion. All five checked rule bodies
typecheck after registration; recursive bodies fail on missing recursors
before it. The audit retains the existing projection admission and excludes
known-false strengthening/confluence dependencies. Full rule translation and
iota soundness remain open.

**Typed recursive calls and values:** a translated inserted recursor signature
now supplies a typed constant in the caller's universes and local context.
The application proof substitutes each actual argument through its dependent
telescope, derives the final major argument from the recursive-field opening
trace, and closes the higher-order field arguments with lambdas. Shared
selected declarations supply their argument receipts directly from context
well-formedness. The stored signature now also supplies its raw type through
the inverse implicit-binder pass. In the generated universe context, preserved
shared declarations derive the actual signature prefix; applying the changed
indices and closing the field arguments produces a value at its generated IH
domain. An alignment bridge supplies the annotation-peeled IH binder type.
This generated-context proof inherits 11 axioms on both toolchains; arbitrary
caller-universe instantiation retains its existing 16/19-axiom manifests.
The actual translated field terminal now supplies individual changed-index
typing from a typed partial family header and a native correspondence of
successively instantiated domains. This handles dependent indices without
assuming their individual translations or typings. The argument recovery
inherits seven axioms; the complete generated IH-value proof retains eleven
on both toolchains. The checked header batch now supplies the partial-family
input and its actual normalized residual signature. Native sort telescopes
discharge header/parameter normalization support constructively; general
headers retain those support obligations. The input transports through recursor
registration, universe extension and rule-context insertion. The older generic
checker normalization route still reaches known-false strengthening and is
excluded by the new proof audit. The actual translated index trace now
reconstructs a definitionally equal signature from the peeled declarations;
selected binding agreement derives native domain correspondence after changed
dependent substitutions. This removes the complete domain-correspondence premise
from the new field consumer. Its reconstruction/converted-consumer manifests
contain seven/eleven inherited axioms and exactly five existing projection
admission roots, excluding known-false strengthening/confluence. The new fixture
checks 384 actual generated telescopes, including 576 normalization changes and
384 peeled dependent domains. Formal canonical major/result alignment,
field-opening support and shared-binding preservation for every rule remain open.
Full RHS translation,
rule/iota semantics and frontend soundness remain open. The proofs exclude
known-false strengthening/confluence results and add no admission. Three
actual higher-order values in parameterized indexed and mutual indexed
families match their instantiated minor/IH domains; malformed indices,
other-parent motives and higher-order arguments are rejected on both versions.
A further fixture checks a fourth value with two dependent indices, rebuilding
the actual family prefix and substituting each index through its domain;
malformed final indices, mismatched domains and non-Pi sources are rejected.
Proof audits throughout the fixture suite now explicitly request theorem and
opaque values, covering Lean 4.33's changed accessor default. A regression
must reach an existing projection admission through a theorem proof and
reject that path when forbidden. All updated audits pass on their respective
toolchains. Three older quotient diagnostics now distinguish direct proof
checks from their measured inherited admissions. Kernel proof obligations
and admission counts are unchanged.

**Universal candidate reduction simulation:** every actual `NormalEq` in a
well-formed environment with the quotient rule registered now simulates every
candidate `Step`, and every finite candidate `Steps` path, using candidate
paths on the left and a direct final normal comparison. Both outputs retain
any supplied original type. This includes neutral Prop-source unfolding,
root eta expansion, original checked reduction and congruence under changing
dependent binders. All 155 audited roots exclude admissions and choice on
both versions. Confluence, admission-free normal-equality transitivity,
conversion-consumer migration and frontend soundness remain open.

**Inhabited normal-equality context conversion:** `NormalEq.weak_inv_of_hasType`
pulls a lifted normal equality back through one binder by instantiating a
typed inhabitant. The proof is a direct use of the admission-free simultaneous
normal-substitution API and its audit allows only `propext` and `Quot.sound`.
It supplies the constructive inhabited case while the unrestricted inverse
weakening theorem remains false and conditional.

**Constructive inductive registration alignment:**
`NativeInductive.RegistrationEvidence.aligned` now consumes the existing
header, constructor, and generated-recursor registration receipts and
transports `Aligned` through all three staged model extensions. The proof
checks each native constant's translated type, freshness, model-name shape,
and map equation against the corresponding `VEnv` insertion. It covers
arbitrary definition-safety levels by lowering the safe receipt. The
executable frontend is unchanged; `AddInduct` and full recursor semantics
remain open.

**Universal original-core simulation:** every actual `NormalEq` in a
well-formed environment with the checked quotient rule registered now simulates
any original parallel step, and any finite original-core path, using the
repaired left paths. The complete application clause handles arbitrary left
functions and majors, actual capture reductions/checks, retained eta binders,
root beta and congruence. Both outputs keep the supplied original type. All 100
audited roots exclude admissions and choice on both versions. The original
Prop-source counterexample is simulated by repaired paths and still refutes
the old core-only target. The broader candidate-step and finite-path result
is proved above; confluence, consumer migration and frontend soundness remain open.

**Nonzero quotient exposure and actual EXTRA replay:** a normal comparison
with `Quot.mk` now exposes an actual left constructor at a nonzero source.
Actual Quot rigidity and sort typing eliminate the residual eta/Pi alternative.
For an explicit left `Quot.lift α r β f c major` prefix, recursive simulations
of the function capture and original major now suffice to replay actual root
EXTRA after every right capture reduces. The proof reconstructs both actual
pattern checks and retains the original result type. Controls start with a
left major that does not match, distinct domain/relation parameters, and a
retained dependent binder. All 65 audited roots exclude admissions and choice
on both versions. This explicit-prefix result is generalized by the complete
application and universal core-simulation theorems above; confluence repair
and frontend soundness remain open.

**Type uniqueness and dependent Pi injectivity:** the original stratified Pi
inversion now has a proof with both exact height bounds. Structural Strong
uniqueness gives heterogeneous type chains; collapsing them at the actual left
universe proves ordinary uniqueness and inverts arbitrary untyped Pi equality.
The original `IsDefEq.uniq` proof is unchanged and now excludes admissions,
choice and confluence. Its equality/conversion consequences are independently
audited. Dependent beta domains/codomains, heterogeneous chains, real delta and
quotient derivations, converted types, and unequal heights with distinct
but equivalent codomain universes pass on both toolchains. The lower uniqueness
module has no import path through the original consumers or confluence.
Inverse weakening later in `UniqueTyping.lean`, the false reduction/confluence
contract, projection translation and frontend soundness remain open.

**Ordinary soundness and head separation:** the original sort-injectivity and
sort/Pi-separation admissions are now proved with unchanged contracts, using
only `propext` and `Quot.sound`. Actual ordinary derivations inherit simultaneous
model soundness through the independently clean Strong conversion. Actual WF
history supplies all four chain-injectivity fields: universe equality, dependent
Pi chains, rigid head/argument equality and stored-telescope argument equality.
The model also separates actual rigid Quot spines from Pi types. Its import
graph excludes the old injectivity, uniqueness and confluence modules. Strict
197/204-root audits include the moved foundational helpers and existing
consumer names. Dependent beta chains, real ordinary/Strong quotient EXTRA
and a two-argument Quot spine are checked. Original dependent-Pi injectivity
and type uniqueness are now proved above; concrete nonzero root replay is supplied
above, and universal original-core simulation is now proved with repaired paths.
Universal candidate-step simulation is also proved above; confluence and
frontend soundness remain open.
Earlier dated checkpoint accounts below are superseded by this boundary.

**Actual rule validity and Strong-derivation soundness:** declaration history now
supplies quotient constants, family/constructor rigidity and unique ownership.
The actual quotient equation is valid at its stored type, including its
zero-level proof-field case. Together with delta validity this discharges every
stored-rule obligation of the simultaneous induction. `sound_of_wf` proves both
semantic inclusions and both endpoint semantic typings for actual Strong
derivations in a well-formed source included in a well-formed target. Its 131
strictly audited roots exclude admissions and choice. Ordinary frontend
soundness and the remaining consumer migration remain open; ordinary source
soundness and head separation are supplied above.

**Constructor-pattern rule soundness:** the rule argument now proves both
semantic inclusions for the current constructor-observation and proof-binding
alternatives. It retains actual stored membership, head-type filtering,
dependent binder typing and the actual endpoint equality. Finite extraction,
first occurrences, field indices and the level-zero decision avoid choice.
Actual declaration history identifies every stored constructor pattern as the
quotient equation and excludes competing delta equations at its head. All 200
audited roots exclude admissions and choice. The remaining quotient family
and proof-field premises are now instantiated by actual quotient validity above.

**Finite dependent telescope round trips:** reverse spine transfer now
recovers actual argument typings and reconstructs each domain/result type
observation as a chain at the stored constant type. Actual argument observation
sets form a typed valuation of every prefix of a sound telescope. Finite demands
then produce finite backed keys, including earlier demands needed to type later
ones; winding those keys rebuilds a typed head observation at the actual
application class. Controls exercise a dependent two-argument spine through
beta conversion, partial application, representative replacement and discovery
of an earlier demand omitted from the input. All 138 audited roots exclude
admissions and choice on both versions. Actual quotient-rule validity is now
supplied above.

**Constructive rule binding:** the rule-soundness foundation now recovers
actual dependent binder types, splits typed key telescopes, transfers typed
valuations between related anchors, and inverts rigid and constructor spines.
Every binder's observation set has a finite list representation selected by
finite induction, without choice. Controls transfer nonempty observations
between distinct beta-equivalent anchors and recover the actual third argument
class of the installed Quot.mk constructor. The exact 173-root audit excludes
admissions, choice and the false confluence foundation on both versions.
Actual quotient validity and Strong-derivation soundness are now supplied above;
ordinary frontend foundations remain open.

**Actual delta-rule validity:** every stored bare-constant equation of a
well-formed environment is now valid in its observation model, using actual
declaration-history lookup, head ownership and constructor rigidity. The
simultaneous induction therefore proves soundness and semantic typing of both
endpoints for actual strong derivations in well-formed source environments
without the quotient equation. They can be interpreted in later well-formed
environments containing the actual quotient equation. Controls include two
polymorphic unfoldings, related anchors, and a function-valued definition with
nonempty finite observation keys and a typed application. The 99-root audit
excludes admissions and choice on both versions. Validity of the quotient
equation and unrestricted Strong-derivation soundness are now supplied above;
the ordinary frontend foundation remains open.

**Semantic typing and simultaneous induction:** actual strong derivations now
produce observation soundness and semantic typing for both endpoints together,
conditional on validity of their actual stored equations. The no-equations
corollary discharges that premise from the source environment itself. Constant
spines recover the stored type, finite backed argument keys containing caller
demands, wrapped observation typing, and codomain/domain observation recovery.
Lambda spines recover body typing through dependent binders and nonreflexive
type conversion. The 121-root audit excludes admissions and choice on both
versions. HTS's syntax fallback alone does not certify actual typing; the
simultaneous theorem retains the actual strong derivation. Actual general
stored-rule and declaration-history validity and Strong-derivation soundness
are now supplied above; quotient/Pi separation and nonzero EXTRA remain open.

**Structural observation soundness:** application, lambda, conversion,
beta, eta, proof irrelevance and constant-level equality now preserve both
semantic inclusions and observation typing at related anchors. Together with
the variable, sort and Pi results below, every non-rule case of the actual
strong equality derivation has its simultaneous soundness proof. The
105-root audit excludes admissions and choice on both toolchains. Controls
reduce a dependent beta redex under a binder, change both an application's
function and argument, transport a lambda across different beta-equal anchors,
and retain duplicate eta demands and the original dependent result type.
These individual cases feed the simultaneous induction above. Actual stored-rule
soundness and declaration-history validity are now supplied above; quotient/Pi
separation and nonzero EXTRA remain open.

**Level invariance and dependent telescopes:** observations and their typing
now transfer across equivalent well-formed levels, including actual stored
rule bindings and delta bodies. Typed lambda/Pi telescopes can be constructed
and unwound; the dependent remainder transfers to any member of a key's
class using its codomain soundness induction hypothesis. Variable, sort and
the full dependent-Pi formation cases of simultaneous soundness are proved,
including typing at related anchors. The 115-root audit is admission-free
and choice-free on both toolchains. Controls derive their soundness premises
and change a beta-redex representative inside a genuinely dependent telescope.
Full expression/representative soundness, rule soundness and declaration-history
validity remain open, as do quotient/Pi separation and nonzero EXTRA.

**Expression observation interpretation:** anchored valuations now interpret
all six existing expression forms using actual stored constants and equations,
with typed backed keys and the original rule-binding conditions. Structural
weakening, substitution, instantiation, subsumption monotonicity, compactness,
closed-term invariance and hereditary backing are proved without admissions or
choice. The 139-root audit reads full types and bodies on both toolchains;
controls include a checked delta definition, the actual quotient equation and
nonempty finite demands under a binder. Level invariance and the initial
soundness cases are now supplied above. Full expression/representative and
rule/environment soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Constructive observation filter:** finite index maps now implement the
original contravariant coverage relation without global choice or decidable
equality on observations. Subsumption composes, finite demands admit
hereditary backing, and typed application survives coverage strengthening.
The filter's proof-irrelevance result and typed finite closure are proved;
86 roots have exact admission-free, choice-free manifests on both toolchains.
The structural interpreter is now supplied above. Interpretation soundness,
rule/environment soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Typed class foundation for separation:** heterogeneous sort-typed chains
and element-class collapse now yield actual typed definitional equalities,
without typing injectivity, confluence, admissions or choice. Application,
beta at any member of a typed argument class, related-anchor invariance and
actual function eta preserve the anchored classes. The 51-root audit pins
exact axiom manifests on both toolchains. This ports PR #53's necessary class
foundation; the constructive observation filter is now supplied above.
Interpretation soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Nonzero quotient-major classification:** actual sort typings now prove
source-universe agreement for definitionally equal quotient types and recover a
constructor's source universe from its supplied result type. Any proof inhabiting
a quotient forces a zero-equivalent source, even for a neutral major. At a
nonzero source, arbitrary normal comparison to a constructor now exposes an
actual core path either to a literal constructor with all three related captures,
or to a lambda carrying an explicit equality between the original quotient type
and a Pi type. This eliminates both proof alternatives without false confluence.
Excluding the eta alternative still needs quotient/Pi separation; nonzero EXTRA,
universal simulation and actual-consumer migration remain open.

**General Prop-source application EXTRA:** hereditary exposure now follows
actual checked quotient firing from an arbitrary normally related left source,
beneath any finite related argument list, including retained dependent eta
binders. The complete application induction clause uses only the original
function and argument simulation hypotheses. All eight right captures may
reduce; their actual definitional equalities transport both rule checks before
the exposed left witnesses are joined. Both endpoints retain the original
supplied type. Exact audits retain only the two existing typing admissions.
The nonzero-source EXTRA clause still needs hereditary major exposure and
actual matching/check recovery. Universal simulation, confluence and
actual-consumer migration remain open.

**Universal hereditary constant-spine exposure:** any normal comparison to a
constant applied to captures now produces an actual original-core reduction
path to a proof, a literal related constant spine, or retained eta binders with
recursively exposed bodies. Simultaneous related substitution preserves this
structure, including dependent binder domains; applying related arguments
consumes eta binders by actual beta steps. The complete application theorem
handles any finite pending argument list and preserves both endpoint typings
at the original supplied type, without a recursive simulation premise.
Exact audits retain only the two existing typing admissions. The Prop-source
interpretation is now proved above. Nonzero-source EXTRA still needs to expose
the major and recover actual matching and checks.
Universal simulation, confluence and actual-consumer migration remain open.

**Checked quotient firing across related sources:** when both terms actually
match the quotient pattern, normal equality of the captures now derives the
left rule's two equality checks from the right checks at any source universe.
Only the function and payload need recursive simulation. A separate Prop-source
clause unfolds a saturated left eliminator with an arbitrary major, including
a neutral one, and joins its selected proof to the reduced right payload.
Both clauses use the actual checked right EXTRA and every captured parallel
reduction, construct a left candidate path, and preserve both original endpoint
types. Their exact graphs retain only the two existing typing admissions and
exclude choice, false confluence, inverse transport and normal transitivity.
These are firing clauses with explicit matching/component hypotheses. The
exposure result above supplies hereditary prefix structure; interpreting it
for nonzero-source checked firing remains open, as do universal simulation,
confluence and actual-consumer migration.

**General application beta simulation:** an arbitrary normally related
function can now follow beta on the right, with different normally related
arguments, without a left lambda-shape restriction or recursive simulation
premise in the beta-joining theorem. Forward beta preservation beneath retained
eta spines replaces inverse weakening; simultaneous substitution replaces
normal transitivity. The general application beta clause consumes just the
function/argument induction hypotheses and retains both original endpoint
types. Proof-valued functions also have their complete application clause.
Exact audits retain only the two existing typing admissions and exclude choice
and false confluence. Nonzero-source checked EXTRA still needs to connect
hereditary major exposure to its actual firing clauses. Universal simulation,
confluence and consumer migration remain open.

**Simultaneous substitution and lambda beta simulation:** related arguments
can now be substituted simultaneously into both endpoints of normal equality,
including eta with different dependent binder domains. The general proof has no
inherited source admission in either fork snapshot and avoids normal
transitivity and inverse weakening. Arbitrary candidate argument paths propagate
through duplicated occurrences beneath dependent binders. The actual lambda
beta clause combines recursive body/argument simulation, converted domains and
both endpoint typings at the original application type. Its exact trust boundary
is the two existing typing admissions. The general beta clause is now proved
above; checked EXTRA and the universal simulation remain open. The independent
substitution proof and strict regression are submitted as
[upstream PR #65](https://github.com/digama0/lean4lean/pull/65), with the official
master's additional inductive admissions explicitly audited there.

**Eta joins and replacement simulation clauses:** root eta expansion now joins
EVERY finite candidate path at an identical endpoint, including unfolding and
further eta steps. Eta/application joins also allow simultaneous candidate paths
in the function and argument and retain the original dependent result type.
The replacement `CoreSimulates` obligation has proved recursive clauses for all
eight non-application normal-equality constructors and application congruence.
These clauses still take their recursive simulation hypotheses. The general
application beta clause is now proved above; checked EXTRA remains open.
The eta proofs exclude inverse weakening, false confluence and choice, with exactly the
two independent typing admissions. Actual consumer manifests are unchanged.

**Canonical unfolding versus arbitrary core reduction:** every original
parallel successor of an unfoldable quotient application now joins its canonical
unfolding modulo `NormalEq`, with both endpoints at the original result type.
The congruence case has an identical endpoint; the proof recovers argument
reductions by classifying all proper lift prefixes and handles checked EXTRA
through the prior selector join. Exact trust gates retain only the two independent
typing admissions and exclude choice/false confluence. General normal-equality
simulation, new-step overlaps and actual-consumer migration remain open.

**Quotient rewrite overlap:** canonical Prop-source unfolding now joins the
original checked quotient EXTRA rule modulo `NormalEq`, including arbitrary
parallel argument reductions, syntactically different checked constructor
parameters and zero-equivalent source universes. Both endpoints keep the original
application type. Its complete graph excludes false confluence, derived quotient
injectivity, inverse weakening, projections and choice; exactly two independent
typing admissions remain. General simulation and actual consumer migration are
still open.

**Local-let cache transport:** entering and leaving local definitions preserve
the exact model context and expressions. All five actual state/cache producer
and restoration proofs now avoid generic native/projection weakening, false
strengthening and confluence, with only the existing `TrProj` placeholder in
each complete graph. Equivalence-manager transport preserves reflexive nodes
that mention the fresh identifier and carries their checked leaves unchanged.
Cache definitions, theorem contracts and accepted inputs are unchanged. Generic
lambda paths and broader frontend/model obligations remain open. The focused
master-based [PR #64](https://github.com/digama0/lean4lean/pull/64) now covers both
directions, with its own full build and strict provenance gates.

**Conditional gadget extraction:** the actual conditional recognizer now
closes its two Nat binders at zero and its three dependent reflection binders
at the gadget's own checked arguments. This follows upstream draft #53,
with local projection-free transport proofs preserving the existing contracts.
Its complete extraction graph drops general strengthening and inherits exactly
three existing projection/typing gaps; the whole recognizer's 33-axiom manifest
and broader checker gaps remain. No executable behavior changes.

**Native binder naming:** the actual `TrExprS.inst_fvar` API now preserves the
exact semantic context directly, across both declaration kinds and nested native
binders/projections. Its complete graph drops projection weakening and
instantiation, retaining exactly the existing `TrProj` placeholder. The existing
`TrExpr.openFreshFVar` consumer shares that reduction. Contracts and executable
behavior are unchanged, and the proof is validated on both toolchains. Broader
inference/frontend admissions remain. A focused master-based candidate is kept
separate; draft PR #53 already repairs this API through its larger redesign,
so no duplicate upstream PR is opened.

**Unused-let telescope reconstruction:** the actual `mkForall_trS`,
`mkLambda_trS` and `mkLet_trS` proofs now erase an unused native let directly.
A local let contributes no semantic binder, so retained projection evidence stays
in its original context. Each complete structural builder graph now inherits
exactly `TrProj`, dropping projection weakening; the converted APIs still inherit
other typing gaps. Existing contracts and checker behavior are unchanged.
Dependent-context, mixed-telescope and retained-let controls pass on both
versions. The focused [PR #64](https://github.com/digama0/lean4lean/pull/64)
now includes this consumer of its structural let-erasure proof. Arbitrary lambda
strengthening and whole inference/frontend soundness remain open.

**Projection core contract:** the Lean 4.33.0-rc2 integration now proves the
existing `reduceProjCore.WF` contract used by lazy projection comparison and
scoped methods. Its constructor-head rejection argument is shared with WHNF,
including checked normalization of string literals. This replays the core proof
already submitted in [PR #57](https://github.com/digama0/lean4lean/pull/57);
no duplicate contribution is opened. The source census loses one admission.
The older main worker was already proved; its regression now pins exactly the
remaining `TrProj` admission and seven axioms instead of accepting the entire
method baseline. General projection and frontend soundness remain open.

**Quotient-prefix application overlap:** expanding any partial `Quot.lift`
prefix and applying its generated lambda now provably joins applying first and
expanding the next prefix. The endpoints are identical terms at the original
dependent application type. All six partial lengths and a retained dependent
proof binder are checked. Computation uses no source admissions; the typed joins
retain exactly the two existing universe/function injectivity gaps. This advances
the candidate reduction presentation. The original false confluence contract,
general simulation, other overlaps and migration of checker consumers remain open.

The main remaining barrier is semantic: the non-inductive frontend is proved
without a direct admission, but its dependencies still include `sorryAx`.
Actual checked inductive/model registration and recursor semantics remain open.
Our executable also deliberately differs from upstream; this is not just a
proof-only patch set.

## Comparison snapshot

Progress means extending an actual semantic guarantee, removing an admission
from its dependency chain, or repairing a demonstrated correctness obstruction.
More modules, commits, lines of code, and passing scaffolding tests do not by
themselves satisfy any of these goals.

| Goal | Our demonstrated result | Official snapshot | What still blocks completion |
| --- | --- | --- | --- |
| Preserve well-formedness through actual non-inductive declaration checking | **Conditional contract proved:** `addDecl.WF_noninductive`, including quotients, arbitrary fuel, batches, and empty-environment contracts. | Ordinary `addDecl.WF` cases are also proved, including quotients and mutual definitions. | Our theorem still inherits `sorryAx`; this is not unconditional kernel soundness. |
| Remove inherited admissions from the frontend | **Not complete.** Dependency audits identify the remaining trust gaps. | Foundational admissions also remain. | Must close the actual metatheory/checker dependencies, not add another wrapper around them. |
| Supply simultaneous substitution for arbitrary typing/equality derivations | **Proved API now available:** `55b7b4d` ports strong/weak cross-substitution and audits its dependencies as only `propext` and `Quot.sound`. | Already proved upstream in `6ba54db`/`8223d22`. | Foundation integration, not a newly solved upstream obligation; the frontend's inherited admissions remain. |
| Verify actual checked inductive registration | **Not complete.** Header/constructor checks and staging invariants are proved. | The inductive frontend case remains admitted. | Constructive `AddInduct`, model registration, constructor/recursor generation, and prelude translation. |
| Complete confluence and semantic reduction correctness | **Original simulation contract refuted:** the actual quotient model has a checked counterexample to `NormalEq.parRed`. Every actual normal equality now simulates every candidate step and finite candidate path, including original checked reduction, neutral Prop-source unfolding, eta expansion and congruence. Both outputs retain the supplied original type. | Confluence and related semantic obligations remain open. | Candidate confluence, admission-free normal-equality transitivity, migration of actual consumers, general strengthening, genuine projection and inductive recursor semantics. |
| Verify the full native arithmetic set | **Not complete:** many arithmetic contracts are proved, but GCD/AND/OR/XOR native reductions are disabled. | Newer primitive checking proofs and guards are available for review. | Restore those four operations with the actual primitive-extension proofs; close the well-founded validation gap. |
| Prevent demonstrated inductive source capture | **Concrete repair:** source preflight rejects capture inputs before generated names can bind them; native Lean 4.29.0 reproducer retained. | Native Lean 4.33.0-rc2 rejects this exact source constructor with `declHasFVars`, now regression-tested. | Version-bounded validation result, not a current native bug or a proof of logical unsoundness. |
| New semantic guarantees in the October 13 integration checkpoint | **None claimed.** Recursor/restoration, binder, header-typing, and transport proofs are restored against current APIs while preserving their existing contracts. | Compatibility preserves prior contracts; it is not a newly solved upstream obligation. | Submit only independently reviewable semantic or correctness changes after publication; keep compatibility repairs out of the progress score. |

Comparison anchors: our published proof source at
`4b3a958f89d999bc40ec6b409b135aa36108b8be`, and official
`digama0/lean4lean` master at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`
(2026-10-10). Our toolchain is Lean `v4.29.0`; official uses `v4.33.0-rc2`.
These pins make the claims reviewable without treating source volume as progress.

## Verification workstreams

“Proved” below describes the stated contract, not admission-free soundness of
the entire dependency stack.

| Workstream | Our branch | Upstream comparison / remaining limit |
| --- | --- | --- |
| Non-inductive declaration frontend | Actual `addDecl.WF_noninductive`, including quotient declarations, arbitrary fuel, batches, and empty-environment contracts. | Upstream's actual `addDecl.WF` already proves ordinary cases, including quotients and mutual definitions; its inductive case is admitted. Ours still inherits `sorryAx`. |
| Checker infrastructure | Extensive scope, free-variable, reader, cache, fuel, and callback proofs; actual-worker head/cache preservation. | Syntactic invariants are not semantic correctness of every reduction. In particular, `reduceRecursor.WF` remains unfinished. |
| Universe levels | Verified total level machinery and comparison path. | Upstream added newer standard-library normalization/comparison proofs and a SAT-hardness result. Our full syntactic agreement with its normalizer is regression-tested, not proved. |
| Primitive checking and arithmetic | Many primitive-extension and arithmetic contracts, with native regression receipts. | Upstream has newer primitive-table/guard proofs and refactorings. Our four disabled native operations and well-founded primitive-validation gap remain unfinished. |
| Inductive declarations | Source preflight, header/constructor checks, scope and registration-stage invariants, and primitive-inductive receipts. | Neither snapshot completes the constructive `AddInduct` model. Staging receipts do not prove actual checked inductive registration or translate the Lean prelude. |
| Metatheory and reductions | Recent quotient beta/alignment work, a proved constant confluence case, the actual closed quotient equation's guarded pattern certificate, and a targeted port of upstream's strong simultaneous substitution proof. | Full confluence, injectivity/strengthening, genuine projection semantics, and recursor soundness remain open. The substitution API does not itself remove these admissions. |

### Recent concrete progress

- Proved actual non-inductive frontend contracts, rather than relying only on
  restricted wrapper entry points; dependency audits still expose inherited
  admissions.
- Repaired source-variable capture handling in inductive preprocessing through
  checks on the original source, before generated names can capture it.
- Repaired the native-instantiation verification specification to model
  simultaneous substitution correctly, instead of adding a trusted assumption.
- `7682b23`: proved the constant/extra-rule case of parallel reduction modulo
  universe conversion, removing one confluence admission.
- `c0f9930`: repaired the root-only equation-pattern premise that excluded the
  real six-lambda quotient equation. The new guarded certificate is proved;
  arbitrary quotient-pattern soundness and a concrete quotient `Params`
  instance are not established.
- `55b7b4d`: ported upstream's simultaneous substitution proof, with strong and
  weak cross-substitution, typed context substitutions, and binder/identity
  support. All 34 owned theorem audits exclude inherited admissions; this does
  not change the frontend's existing `sorryAx` dependency.

## What upstream has that we should review

Upstream's changes include substantive proofs and correctness fixes, not merely
maintenance. Particularly relevant:

- `67f63b0` (2026-10-10): compare primitive types up to metadata.
- `6ba54db` and `8223d22` (2026-08-29): strong simultaneous substitution
  (`substDF`) and closure of substitution admissions. The foundational API is
  now ported; the newer primitive consumers still need review.
- `ac1498a`, `c195b64`, and related commits (2026-08-29): primitive checking
  invariants, clauses, and the inductive guard.
- `4b60e53` (2026-08-14): compute the K-target flag where the kernel does.
- The August level-normalization soundness/completeness work, lazy-delta and
  projection improvements, and stage-2 replay/toolchain updates.

Except for the explicitly noted substitution port, these are candidates for
targeted comparison, not evidence their changes are present here. No merge, rebase, cherry-pick, or
toolchain upgrade was performed for the published branch. Review overlapping
proofs before duplicating them; a wholesale integration needs compatibility
work because our checker and toolchain have diverged.

### Daily synchronization

The user requested a rebase on official upstream **daily** on 2026-10-12.
Before the first verification item each UTC day, fetch `origin/master`, rebase
on its current tip (or confirm it is already an ancestor), and record the
upstream hash, conflict resolution, build, regression, and trust-audit results.
Integration is a maintenance requirement, not a semantic milestone by itself.

This branch is published, so a nontrivial rebase requires a history-rewriting
push. Permission to use `--force-with-lease` is pending; the existing no-force
rule remains in effect until the user answers. Do not describe the branch as
rebased or synchronized until the rebase and publication have actually succeeded.

### Current integration checkpoint — October 19

Official `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` is an ancestor of this
integration; today's rebase check at its preceding checkpoint was a successful
no-op. The main Lean 4.29.0 review branch is still not based on that tip.
No force push is authorized or used. The validated snapshot is published
separately as `poc-verified-noninductive-upstream-20261019`.

The unchanged `reduceRecursor.WF` contract now composes the actual quotient
worker proof with inductive rejection in the constructor-free `TrEnv` model.
This removes its direct admission but retains inherited typing/confluence
admissions and native interface axioms. This upstream dispatcher accepts only
the expression argument; the older fork's cheap-flag interface is not added.
The abstract signature-registration model supplies constructive freshness,
lookup, extension, and orderedness proofs. It replaces three placeholders,
but does not establish positivity, generated recursor correctness, or genuine
checked inductive/model registration.

Rewrite metadata now handles every well-formed declaration history, including
upstream mutual definitions: all signatures are reserved before bodies are
checked, then their equations are registered. A new fixture checks a real
two-definition block whose second body uses the first constant, registered
equations and actual reduction, and duplicate-name rejection. These history
witnesses and general metadata proofs have no admissions or choice.

The quotient confluence obstruction is proved against the actual integration
model without depending on the refuted theorem, its confluence consequences,
derived quotient injectivity, or false strengthening. The typed Prop-source
and all-prefix unfolding preserve the original result type and are stable
under weakening, typed substitution, and context conversion. The strict
selector/completeness audits exclude admissions and choice. Full source typing
and model construction still inherit independent typing/injectivity admissions.
The old `NormalEq.parRed` contract remains false and admitted; general
simulation, confluence, eta overlaps, and downstream migration remain open.
The selector/prefix direction is attributed to upstream draft #53.

All 422 default build jobs and 33 fixtures pass on Lean 4.33.0-rc2,
including the quotient/model, primitive/frontend, and five existing integration
trust fixtures. Audits inspect theorem and opaque
bodies explicitly using `value? (allowOpaque := true)`, as required by the
newer API; no dependency allowlist is broadened. The source census decreases
from 129 matching lines / 133 occurrences to 125 / 129. This is evidence of
four direct admission removals, not unconditional frontend soundness.
Detailed contracts and receipts are in `PROOF_STATUS.md`.

### Earlier integration receipts — October 12

The following records describe intermediate checkpoints, not the current full
integration gate. The October 13 checkpoint above supersedes their stopping
points and broad statements about passing candidate targets.

Preparation on 2026-10-12 fetched the official snapshot above. A non-mutating
tip-to-tip merge preview reports conflicts across core checker and proof files;
it is not evidence of a completed rebase. Preserve both upstream correctness
fixes and this fork's verified contracts when resolving the integration.

An actual rebase is now **in progress in an isolated detached worktree**, based
on the same official tip. The published branch remains unchanged by that rebase.
The first environment/frontend replay is now reconciled at detached checkpoint
`c83d6b01209f9320fed46d11cc1e187a8c84219e`. It retains upstream's
body-before-primitive checks, mutual-block model, and theorem-as-Prop-constant
semantics while recovering this fork's **actual non-inductive, arbitrary-fuel,
batch, and empty-environment contracts**. The empty-model proof also accounts for
upstream's stage-2 constant map instead of changing runtime defaults.

That intermediate checkpoint passes **all default targets on Lean 4.33.0-rc2**
(161 jobs), a 20-theorem direct-admission/dependency audit, and three actual
checked runtime pipelines using different fuel configurations. The audit excludes
dependency on the admitted whole `addDecl.WF` theorem, but still inherits
`sorryAx` and the existing checker/native-interface axioms. No semantic admission
has been removed by this integration. The remaining fork commits are **not yet
replayed**: a green intermediate checkpoint is **not a completed rebase or
validation of the final branch**.

The next safe-definition replay is also reconciled at detached checkpoint
`dc217549a0e08a2f7006ba32a865867bf589765f`. It keeps upstream's stronger
primitive-extension proofs, metadata-aware type comparisons, and all fourteen
binary native arithmetic/predicate branches instead of replaying the fork's
historical temporary arithmetic removals. The fork's primitive-only extension
contract is recovered from the actual, stronger declaration theorem.

All default targets and both candidate fixtures pass. Actual fresh-slot checks
for `Nat.add`, `Char.ofNat`, and `String.ofList` accept domain metadata, reject
misplaced metadata and invalid safety/universe parameters, and check the String
constructor dependencies. An ill-typed primitive body is rejected before
recognizer probes. Direct native reductions pass without fallback unfolding.
These runtime controls use a native prelude and are **not a proof of its model
translation**; primitive proof audits still inherit the upstream checker trust
baseline. This is compatibility/preservation evidence, not a newly completed
primitive soundness milestone. The published branch's four disabled operations
remain disabled until the full rebase is validated and published.

The restricted and remaining-non-inductive frontend replays are reconciled at
`9a95087ca626e04ecaf2c4557f0992102531dac6` and
`f9879f700b003dc6e517edf550bb95873f6eb353`. The actual verified wrapper again
handles every non-inductive declaration form with arbitrary fuel, retaining
upstream's checked unsafe/mutual-block model and the fork's fuel-sensitive,
fresh-name-checked quotient worker. Native-prelude controls check quotient
headers against the actual upstream worker, reject invalid equality/reflexivity
headers and name collisions, and preserve exhausted-fuel rejection and
initialized idempotence. Three additional checked pipelines accept recursive
unsafe/partial bodies while rejecting safe dependencies on them, invalid mutual
blocks, wrong proofs, duplicate names, and inductive declarations.

**The quotient semantic boundary is still open:** successful initialization
requires inductive `Eq`, which the current `TrEnv` cannot translate. Both
initialization preservation proofs are therefore vacuous in their uninitialized
case. Passing native-prelude bootstrap controls does not supply that missing
model or establish constructive quotient-registration soundness.

The candidate retains upstream's native `deltaValue?` semantics and its actual
unfolding proof instead of the fork's historical safe-only delta scaffolding;
wrong universe arities and opaque unfolding still reject. The published branch
continues to use its previous behavior. All default targets and four candidate
fixtures pass. Audited proof bodies introduce no direct admissions or new axioms,
but still inherit `sorryAx` and the existing native/checker interfaces. These are
preserved contracts and explicit remaining obligations, not an admission-free
frontend milestone.

The original-level-normalization replay is reconciled at
`785d1daba69314c7b09f3bec90b806cfe2a2a714`. It restores the total
flatten/sort/subsume helper and its named-valuation preservation proof **without
replacing upstream's complete canonical comparison/equivalence checks with the
older incomplete core-only path**. Sixteen level-contract audits exclude both
direct admissions and inherited `sorryAx`; existing native level and tree-map
interface axioms remain. The broader frontend still inherits admissions.

Candidate regressions reproduce valid inequalities/equivalences that the native
fast paths reject, and prove their acceptance using the actual public
completeness contracts. The total helper matches the installed native normalizer
on 3,280 small and 10,000 generated inputs; the complete fallback additionally
accepts 2,216 comparisons and 207 equivalences in that generated corpus. These
are controls against a semantic regression, not a proof of full syntactic
agreement with the native normalizer. Completeness still requires successful
`VLevel.ofLevel` translations; six metavariable controls establish syntax
agreement only. All default targets and five candidate proof/runtime fixtures
pass. The rebase stops cleanly before the module-region cleanup replay; final
integration and publication remain unfinished.

The module-region cleanup and Nat.add replay are now reconciled in the isolated
candidate at `0af54e3` and `0fb93bc`. The cleanup preserves upstream's stronger
`Replay.replayFromImports` lifetime fix: module-region handles are projected
before `Environment.freeRegions`, avoiding dangling references during deferred
decrements. The original primitive patch's historical `checkPrimitiveDef` was
superseded by upstream's extracted typed local-probe clauses, so its obsolete
wrapper edits are not mechanically reintroduced. The candidate retains the
actual current Nat.add checker and adds the original recurrence/evaluation and
reflection contract as `VEnv.NatAddSpec`, with direct proof-body audits and
negative/positive lambda-domain controls.

The Nat.add compatibility fixture validates literal evaluation and reflection
from the two open equations, while `tests/Primitive.lean` checks that equation
wrappers use well-typed lambda binders and reject forall-shaped or wrong-domain
wrappers. The stronger current primitive clause proof remains the source of
recognizer preservation; the compatibility contract is not a new admission-free
kernel theorem. Its arithmetic proof inherits the existing `sorryAx`/classical
typing baseline, which is recorded rather than hidden. All prior level,
environment, frontend, quotient, and primitive fixtures continue to pass. The
rebase is clean at deliberate break 15 of 327, before the primitive-frontend
connection replay; final integration and publication remain unfinished.

### Upstream contributions

After the initial rebase passes its full validation, submit one coherent,
reviewable proof or correctness fix **as soon as it is ready**, normally one
reviewable item at a time; batch tiny dependent changes. Do not accumulate
another large divergent stack or open PRs merely for module additions. Pending
review does not block continuing verification. Re-check official master to
avoid duplicate work, build on its current toolchain,
include regression and transitive-axiom evidence, and keep fork-only status
documents out of the PR. No PR has been opened for this integration checkpoint.

First evaluate the closed quotient-equation pattern repair and the constant-case
confluence proof. Do not submit the substitution port: it already came from
upstream. Reassess the source-preflight contribution against upstream's own
checks; the tested native capture input is already rejected by Lean 4.33.0-rc2.

## Behavioral differences and findings

Our executable includes a restricted verified frontend, additional primitive
validation, safe-only delta unfolding, a replacement level implementation, and
stricter inductive source preflight. The main Lean 4.29 worker still disables native `Nat.gcd`, `Nat.land`,
`Nat.lor`, and `Nat.xor`; this Lean 4.33 integration retains upstream's enabled
reductions and their existing verification obligations.

[bugs-found.md](bugs-found.md) documents a native inductive source-variable
capture reproducer on **Lean 4.29.0**. This is an input-validation bug, not a
demonstration of logical unsoundness. Native Lean **4.33.0-rc2 rejects this exact
input**, as checked by `tests/NativeInductiveSourceRejection433.lean`; no upstream
report has been submitted. The quotient
equation-pattern and native-instantiation repairs are specification mismatches,
not additional native kernel bugs. See [divergences.md](divergences.md) for the
precise boundaries and reproducers.

## Validation and admission accounting

The current main Lean 4.29.0 proof source passes all default targets (456 jobs)
and all 42 selected regressions on October 19. This Lean 4.33.0-rc2 integration
passes its full default build (459 jobs) and all 70 selected regressions. The
independent current-master substitution PR passes its default build and
standalone regression. Each receipt validates its respective source snapshot;
exact trust bounds are recorded in `PROOF_STATUS.md`.

| Whole-word `sorry` or `admit` source census, October 19 | Published proof source | Local integration | Official master |
| --- | --- | --- | --- |
| Matching lines | 116 | 121 | 133 |
| Files containing matches | 18 | 22 | 29 |
| Occurrences | 120 | 125 | 137 |

This deliberately includes comments and `Experimental` sources. It is a source
census, **not an audit of theorem trust**: removing one admission does not make
every theorem depending on it admission-free, and adding substantial proved
code does not make the raw totals comparable as percentages. Both branches
retain foundational admissions. Our actual frontend's transitive `sorryAx`
dependency is the more important signal.

This integration removes three abstract signature/model placeholders and the
actual recursor dispatcher admission. Proved sort injectivity and sort/Pi
separation remove two more occurrences in both trees; original dependent-Pi
injectivity removes another. Nonzero constructor exposure and actual EXTRA
replay add no admission. The remaining `sorryAx` dependencies, including the
known-false confluence contract, remain explicitly conditional. Raw counts do not replace the dependency audits.

## Next priorities

1. Finish the actual upstream rebase, preserve verified contracts and upstream
   fixes, validate it, and publish only with the required explicit lease permission.
   Then submit focused, validated upstream contributions rather than rebuilding
   a large divergent patch stack.
2. Repair the demonstrated false `NormalEq.parRed` contract while preserving
   semantic conversion and accepted declarations. Universal original-core
   simulation by repaired paths is proved. Complete candidate unfolding/eta
   simulation, confluence and downstream migration. Close inverse weakening and
   genuine projection/inductive recursor semantics; the dispatcher proof here
   still depends on those foundations and constructor-free rejection.
3. Connect the existing inductive stages to actual checked model registration,
   constructor/recursor generation, and a constructive `AddInduct` model.
4. Restore the four disabled native arithmetic operations with their proofs and
   close the well-founded primitive-validation gap.

## Keeping this overview current

Update this document at meaningful checkpoints, alongside the detailed
`PROOF_STATUS.md`: pin both source hashes and the review date, refresh the
scorecard and workstream boundaries, and record validation and dependency-audit changes.
Do not change a conditional or staging result to “complete” solely because
the default build passes.

Useful refresh commands (with `origin` pointing to official lean4lean):

```sh
git fetch origin master
git rev-parse HEAD origin/master
git merge-base origin/master HEAD
git rev-list --left-right --count origin/master...HEAD
git cherry -v origin/master HEAD
git diff --shortstat origin/master HEAD
git grep -n -w sorry HEAD -- ':(glob)Lean4Lean/**/*.lean'
git grep -n -w sorry origin/master -- ':(glob)Lean4Lean/**/*.lean'
```

The first ancestry count is upstream-only; the second is branch-only. Use
transitive theorem/axiom audits from the regression fixtures alongside these
source measurements. [PROOF_STATUS.md](PROOF_STATUS.md) remains the detailed
evidence record; this file is the maintained summary, not a replacement for it.
