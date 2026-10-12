# Progress and upstream comparison

Last reviewed: **2026-10-12 (UTC)**. This is the readable overview of the
`poc-verified-noninductive` branch; [PROOF_STATUS.md](PROOF_STATUS.md) holds the
detailed theorem contracts, dependency audits, and regression evidence.

## Bottom line

The branch is locally rebased on official `origin/master` at
`67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, with no upstream-only commits.
The stack restores and checks constructor, recursor, metadata, preservation,
field-scope, inductive field/IH allocation, frontend restoration, and
restoration-metadata contracts on the current upstream API, but it is **not a
completed verification of Lean's kernel**. The default build still stops in
three downstream proof files, and the frontend's dependency chain still
contains `sorryAx`.

The main remaining barrier is semantic: the non-inductive frontend is proved
without a direct admission, but its dependencies still include `sorryAx`.
Actual checked inductive/model registration and recursor semantics remain open.
Our executable also deliberately differs from upstream; this is not just a
proof-only patch set.

## Comparison snapshot

This snapshot treats synchronization as maintenance and reports progress only
when a semantic contract, trust boundary, or correctness obstruction changes.

| Signal | Current evidence | Interpretation |
| --- | --- | --- |
| Upstream synchronization | `HEAD` `974a97f`; `origin/master` `67f63b0`; merge-base is `origin/master`; `0` upstream-only / `384` branch-only | The local rebase is current; history counts are synchronization data, not verification progress. |
| Semantic guarantees | Constructor/recursor metadata, registration, run-preservation, minor-indexing, recursor field/IH allocation, inductive frontend restoration and restoration-metadata contracts, and non-nested frontend-scope contracts build; the frontend-scope fixture exercises source, fuel, arity, freshness, universe, and reserved-prefix boundaries | These preserve executable contracts on upstream's API; they do not remove inherited trust or complete inductive checking. |
| Admission boundary | `129` matching lines in `27` files; `133` whole-word `sorry`/`admit` occurrences under `Lean4Lean/` | No admission was added or removed by this compatibility checkpoint; transitive `sorryAx` audits remain the trust signal. |
| Build status | `lake build Lean4Lean.Verify.InductiveRestorationMetadata` passes (160 jobs); the default build reaches all `414` targets and fails in `Verify.InductiveValueFrame`, `Verify.InductiveNestedRewrite`, and `Verify.InductiveHeaderTraces` | Restoration metadata is cleared; value-frame integration, nested-rewrite, and header-trace proof fronts remain before a green default build. |
| Publication and upstream contribution | The rebased tip is not force-pushed; no upstream PR has been opened from this compatibility-only checkpoint | Keep the fork review branch intact until rewrite authorization is explicit; submit only focused semantic fixes once validated. |

## Progress scorecard

Progress means extending an actual semantic guarantee, removing an admission
from its dependency chain, or repairing a demonstrated correctness obstruction.
More modules, commits, lines of code, and passing scaffolding tests do not by
themselves satisfy any of these goals.

| Goal | Our demonstrated result | Official snapshot | What still blocks completion |
| --- | --- | --- | --- |
| Preserve well-formedness through actual non-inductive declaration checking | **Conditional contract proved:** `addDecl.WF_noninductive`, including quotients, arbitrary fuel, batches, and empty-environment contracts. | Ordinary `addDecl.WF` cases are also proved, including quotients and mutual definitions. | Our theorem still inherits `sorryAx`; this is not unconditional kernel soundness. |
| Remove inherited admissions from the frontend | **Not complete.** Dependency audits identify the remaining trust gaps. | Foundational admissions also remain. | Must close the actual metatheory/checker dependencies, not add another wrapper around them. |
| Supply simultaneous substitution for arbitrary typing/equality derivations | **Proved API now available:** `55b7b4d` ports strong/weak cross-substitution and audits its dependencies as only `propext` and `Quot.sound`. | Already proved upstream in `6ba54db`/`8223d22`. | Foundation integration, not a newly solved upstream obligation; the frontend's inherited admissions remain. |
| Verify actual checked inductive registration | **Not complete.** Header/constructor checks, staging invariants, and the non-nested frontend scope are proved. | The inductive frontend case remains admitted. | Constructive `AddInduct`, model registration, constructor/recursor generation, nested restoration, and prelude translation. |
| Complete confluence and semantic reduction correctness | **Partial progress:** `7682b23` removes the constant-case confluence admission; `c0f9930` repairs the incompatible quotient-equation premise. | Confluence and related semantic obligations remain open. | Application/extra confluence, injectivity/strengthening, genuine projection semantics, and `reduceRecursor.WF`. |
| Verify the full native arithmetic set | **Not complete:** many arithmetic contracts are proved, but GCD/AND/OR/XOR native reductions are disabled. | Newer primitive checking proofs and guards are available for review. | Restore those four operations with the actual primitive-extension proofs; close the well-founded validation gap. |
| Prevent demonstrated inductive source capture | **Concrete repair:** source preflight rejects capture inputs before generated names can bind them; native Lean 4.29.0 reproducer retained. | Behavior on its newer toolchain has not been tested. | Do not generalize the finding to other Lean versions or claim it proves logical unsoundness. |

Comparison anchor: rebased stack through `d93279f038b8ac16295c3b3ce4ff2d013904e995`
and official `origin/master` `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`, both
using Lean `v4.33.0-rc2`. These pins make the claims reviewable without treating
source volume as progress.

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
- `9caa110`: threaded the upstream `checkNoNestedAux` preflight through the
  non-nested frontend-scope proof and added regression controls for reserved
  `_nested` constants and projections. This proves the scope contract for the
  current executable path without treating the preflight as an assumption.
- `d9d90df` and `d93279f`: normalized upstream `LocalDecl.cdecl` free-variable
  identities in constructor-field and induction-hypothesis allocation traces;
  field sequences and declaration-shape contracts are unchanged.
- `e235023` and `974a97f`: adapted frontend restoration and restoration-metadata
  contracts to upstream's `checkName` freshness result, reserved-prefix
  preflight, panic provenance, and generated StateT action shape.
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

Except for the explicitly noted substitution port and the compatibility commits
listed in the journal, these remain candidates for targeted comparison, not
evidence their changes are present here. Review overlapping proofs before
duplicating them; upstream contributions should be narrow, independently
reviewable semantic fixes.

### Daily synchronization

The user requested a rebase on official upstream **daily** on 2026-10-12.
Before the first verification item each UTC day, fetch `origin/master`, rebase
on its current tip (or confirm it is already an ancestor), and record the
upstream hash, conflict resolution, build, regression, and trust-audit results.
Integration is a maintenance requirement, not a semantic milestone by itself.

The 2026-10-12 rebase was completed locally on official `origin/master`, with
conflicts resolved in favor of preserving both upstream behavior and this
branch's verified contracts. The normal push was rejected as non-fast-forward;
no force push has been attempted while `--force-with-lease` authorization is
pending. Until publication is authorized, the fork's existing review branch is
unchanged and this work remains in the detached rebased worktree.

## Behavioral differences and findings

Our executable includes a restricted verified frontend, additional primitive
validation, safe-only delta unfolding, a replacement level implementation, and
stricter inductive source preflight. Native `Nat.gcd`, `Nat.land`, `Nat.lor`, and
`Nat.xor` reductions are still disabled; restoring their verified support is
part of the unfinished work, not a completed optimization decision.

[bugs-found.md](bugs-found.md) documents a native inductive source-variable
capture reproducer on **Lean 4.29.0**. This is an input-validation bug, not a
demonstration of logical unsoundness. Its status on upstream's newer toolchain
has not been tested, and no upstream report has been submitted. The quotient
equation-pattern and native-instantiation repairs are specification mismatches,
not additional native kernel bugs. See [divergences.md](divergences.md) for the
precise boundaries and reproducers.

## Validation and admission accounting

Focused `lake build Lean4Lean.Verify.InductiveRestorationMetadata` passes (160 jobs),
and `lake build Lean4Lean.Verify.InductiveFrontendRestoration` passes (159 jobs).
The direct restoration fixture remains blocked because rebuilding
`Verify.InductiveRestorationRecursors` reaches the existing nested-rewrite
failure. Focused
`lake build Lean4Lean.Verify.InductiveFrontendScope` also passes (158 jobs),
and `tests/InductiveFrontendScope.lean` passes 10 public fixtures plus 16
failure controls, including reserved-prefix rejection. The constructor-field
and IH trace targets pass focused builds (153 and 154 jobs respectively); their
translation fixtures remain downstream of unavailable binder-typing/header
objects. The existing
`RecursorFieldScope` and direct metadata/registration audits also pass with
exact generated-native provenance identities. The default `lake build` reaches
all `414` targets before failing in `Verify.InductiveNestedRewrite`,
`Verify.InductiveValueFrame`, and `Verify.InductiveHeaderTraces`; the receipt is
`/var/tmp/thomas-ahle/fleet2/logs/lean4lean-inductive-restoration-metadata-full.log`.
The aggregate
`tests/InductiveReturnTyping.lean`, `tests/InductiveValueFrame.lean`, and
later inductive frontend fixtures remain downstream of those blockers. Validation
runs on the same `v4.33.0-rc2` toolchain pinned by upstream.

Focused `lake build Lean4Lean.Verify.RecursorFieldScope` passes (148 jobs), and
`tests/RecursorFieldScope.lean` passes its transitive axiom audits, retained-field
lookup checks, failure controls, and scoped replay fixtures. The direct
`tests/RecursorRegistration.lean`, `tests/SafeConstructorRegistration.lean`,
`tests/InductiveMetadata.lean`, `tests/ConstructorMetadata.lean`, and
`tests/InductiveRunPreservation.lean` audits also pass with exact generated-native
provenance identities.

| Whole-word `sorry` source census under `Lean4Lean/` | Our fork | Upstream |
| --- | --- | --- |
| Matching lines | 129 | 133 |
| Files containing matches | 27 | 29 |
| Occurrences | 133 | 137 |

This deliberately includes comments and `Experimental` sources. It is a source
census, **not an audit of theorem trust**: removing one admission does not make
every theorem depending on it admission-free, and adding substantial proved
code does not make the raw totals comparable as percentages. Both branches
retain foundational admissions. Our actual frontend's transitive `sorryAx`
dependency is the more important signal.

## Next priorities

1. Review and selectively port valuable upstream fixes and proofs, especially
   metadata comparison, K-target computation, substitution, and primitive work.
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
