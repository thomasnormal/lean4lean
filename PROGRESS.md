# Progress and upstream comparison

Last reviewed: **2026-10-13 (UTC)**. This is the readable overview of the
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

**Published versus local integration:** the published proof source remains
`4b3a958f89d999bc40ec6b409b135aa36108b8be` on Lean **4.29.0**, and its full
default build passes on October 13. The separate integration worktree is
based on official `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` on Lean
**4.33.0-rc2**. Today's fetch confirms that official tip is already an ancestor,
but integration's full build and regression gates are **not green**. Its
rewritten history has not been published. A current local base is not a
validated, published rebase.

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
| Complete confluence and semantic reduction correctness | **Partial progress:** `7682b23` removes the constant-case confluence admission; `c0f9930` repairs the incompatible quotient-equation premise. | Confluence and related semantic obligations remain open. | Application/extra confluence, injectivity/strengthening, genuine projection semantics, and `reduceRecursor.WF`. |
| Verify the full native arithmetic set | **Not complete:** many arithmetic contracts are proved, but GCD/AND/OR/XOR native reductions are disabled. | Newer primitive checking proofs and guards are available for review. | Restore those four operations with the actual primitive-extension proofs; close the well-founded validation gap. |
| Prevent demonstrated inductive source capture | **Concrete repair:** source preflight rejects capture inputs before generated names can bind them; native Lean 4.29.0 reproducer retained. | Native Lean 4.33.0-rc2 rejects this exact source constructor with `declHasFVars`, now regression-tested. | Version-bounded validation result, not a current native bug or a proof of logical unsoundness. |
| New semantic guarantees in the October 13 integration checkpoint | **None claimed.** Recursor/restoration, binder, header-typing, and transport proofs are being restored against current APIs. | Compatibility preserves prior contracts; it is not a newly solved upstream obligation. | Full build, regression, and transitive-trust gates must pass before calling integration validated. |

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

### Current integration checkpoint — October 13

The inbox is absent. The latest fetch confirms official master remains
`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, already an ancestor of detached
integration checkpoint `43a47d9`; today's daily rebase check is a successful
no-op. The published branch currently has 49 upstream-only and 329 branch-only
commits; the detached integration has zero upstream-only and 397 branch-only
commits. These are synchronization facts, not proof progress.

The detached integration now passes the full default build (all 414 jobs) and
all five current restoration/header regression fixtures. The final recursor-name
audit explicitly accounts for the native expression bridges used by the proof;
no allowlist was weakened and the 129-line / 133-occurrence admission census is
unchanged. This is compatibility maintenance, not a new semantic milestone.
The rewritten history remains unpublished because explicit `--force-with-lease`
authorization is still pending; the published branch remains the green Lean
4.29.0 source.

Regression results are stricter than the focused module builds. Current
receipts under `/var/tmp/thomas-ahle/fleet2/logs/` show passing controls for
`tests/InductiveHeaderTraces.lean`, `tests/InductiveFrontendRestoration.lean`,
`tests/InductiveSubstitutionStageEndpointRebase.lean`, and
`tests/InductiveHeaderNormalizationTransport.lean`, including
`tests/InductiveOriginalRecursorNames.lean` after its explicit native-bridge
classification. The default build and these five trust-boundary fixtures are
green; the integration still does not claim a new semantic milestone or
admission removal. No source admission is added or removed by the compatibility
adaptation.

Documentation is published by normal fast-forward without publishing the
unfinished integration. Preserve that worktree and reconcile this document
when the integration is ready.

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
documents out of the PR. **PR #55** is open for the focused constant-case
confluence proof, and **PR #56** is open for the independent closed
quotient-equation pattern repair; both branches are based directly on the
current official master.

The constant-case confluence proof was submitted as PR #55 after a 161-job
official-master build, a focused regression, and a transitive-axiom audit. The
patch removes one existing confluence admission and adds no new one. PR #56
generalizes the equation certificate under shared lambda binders without adding
an admission or claiming full quotient confluence. Do not submit the substitution
port: it already came from upstream.
The source-preflight contribution was rechecked and is not a PR candidate:
official upstream already performs the equivalent original-header and
constructor `checkNoMVarNoFVar` checks inline in `addInductive`, while Lean
4.33.0-rc2 rejects the historical capture input. It remains useful fork-side
regression evidence, not a duplicate upstream change.

## Behavioral differences and findings

Our executable includes a restricted verified frontend, additional primitive
validation, safe-only delta unfolding, a replacement level implementation, and
stricter inductive source preflight. Native `Nat.gcd`, `Nat.land`, `Nat.lor`, and
`Nat.xor` reductions are still disabled; restoring their verified support is
part of the unfinished work, not a completed optimization decision.

[bugs-found.md](bugs-found.md) documents a native inductive source-variable
capture reproducer on **Lean 4.29.0**. This is an input-validation bug, not a
demonstration of logical unsoundness. Native Lean **4.33.0-rc2 rejects this exact
input**, as checked by `tests/NativeInductiveSourceRejection433.lean`; no upstream
report has been submitted. The quotient
equation-pattern and native-instantiation repairs are specification mismatches,
not additional native kernel bugs. See [divergences.md](divergences.md) for the
precise boundaries and reproducers.

## Validation and admission accounting

At the published proof source, the full default `lake build` passes on
**October 13** (receipt `lean4lean-published-progress-build-20261013.log`
under `/var/tmp/thomas-ahle/fleet2/logs/`).
Ten focused fixtures also pass without warnings: `StrongSubstitution`,
`NativeInstantiation`, `Reflection`, `QuotientPatternEquation`,
`ConfluenceConstantReduction`, `NonInductiveDeclarationFrontend`, `Environment`,
`QuotientReductionAlignment`, `QuotientReductionSemantics`, and
`PrimitiveInductiveReceipt`. These fixtures are run separately from the default
build. These receipts describe the published source, not the partially rebased
candidate. Candidate focused builds and the version-specific native test above
are separate integration evidence, not a full build of upstream or the candidate.

| Whole-word `sorry` or `admit` source census, October 13 | Published proof source | Local integration | Official master |
| --- | --- | --- | --- |
| Matching lines | 126 | 129 | 133 |
| Files containing matches | 24 | 27 | 29 |
| Occurrences | 130 | 133 | 137 |

This deliberately includes comments and `Experimental` sources. It is a source
census, **not an audit of theorem trust**: removing one admission does not make
every theorem depending on it admission-free, and adding substantial proved
code does not make the raw totals comparable as percentages. Both branches
retain foundational admissions. Our actual frontend's transitive `sorryAx`
dependency is the more important signal.

The uncommitted integration adaptation leaves its starting census unchanged:
129 matching lines, 27 files, 133 occurrences. Differences between source and
toolchain snapshots are not new admissions added by this adaptation, and
unchanged text totals do not establish an unchanged transitive axiom set.

## Next priorities

1. Finish the actual upstream rebase, preserve verified contracts and upstream
   fixes, validate it, and publish only with the required explicit lease permission.
   Then submit focused, validated upstream contributions rather than rebuilding
   a large divergent patch stack.
2. Close semantic dependencies: the remaining application/extra confluence
   case, non-circular typing/injectivity foundations, genuine `TrProj`, and
   quotient/inductive `reduceRecursor.WF`.
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
