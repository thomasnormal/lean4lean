# Progress and upstream comparison

Last reviewed: **2026-10-12 (UTC)**. This is the readable overview of the
`poc-verified-noninductive` branch; [PROOF_STATUS.md](PROOF_STATUS.md) holds the
detailed theorem contracts, dependency audits, and regression evidence.

## Bottom line

Our fork has substantial additional checker verification, primitive proofs,
inductive staging work, and regression coverage. It is **not a completed
verification of Lean's kernel**, and it is **not uniformly ahead of official
lean4lean**. Upstream has independently proved ordinary declaration checking
and added newer primitive and universe-level results that our branch has not
fully integrated. Its admission-free simultaneous substitution proof is now
narrowly ported here; that is useful foundation integration, not completion of
the frontend's soundness proof or a full upstream rebase.

The main remaining barrier is semantic: the non-inductive frontend is proved
without a direct admission, but its dependencies still include `sorryAx`.
Actual checked inductive/model registration and recursor semantics remain open.
Our executable also deliberately differs from upstream; this is not just a
proof-only patch set.

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
| Verify actual checked inductive registration | **Not complete.** Header/constructor checks and staging invariants are proved. | The inductive frontend case remains admitted. | Constructive `AddInduct`, model registration, constructor/recursor generation, and prelude translation. |
| Complete confluence and semantic reduction correctness | **Partial progress:** `7682b23` removes the constant-case confluence admission; `c0f9930` repairs the incompatible quotient-equation premise. | Confluence and related semantic obligations remain open. | Application/extra confluence, injectivity/strengthening, genuine projection semantics, and `reduceRecursor.WF`. |
| Verify the full native arithmetic set | **Not complete:** many arithmetic contracts are proved, but GCD/AND/OR/XOR native reductions are disabled. | Newer primitive checking proofs and guards are available for review. | Restore those four operations with the actual primitive-extension proofs; close the well-founded validation gap. |
| Prevent demonstrated inductive source capture | **Concrete repair:** source preflight rejects capture inputs before generated names can bind them; native Lean 4.29.0 reproducer retained. | Native Lean 4.33.0-rc2 rejects this exact source constructor with `declHasFVars`, now regression-tested. | Version-bounded validation result, not a current native bug or a proof of logical unsoundness. |

Comparison anchors: our `poc-verified-noninductive` source at
`55b7b4dd061f580c88d8552315f350f866f0501f` (2026-10-12), and official
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

Preparation on 2026-10-12 fetched the official snapshot above. A non-mutating
tip-to-tip merge preview reports conflicts across core checker and proof files;
it is not evidence of a completed rebase. Preserve both upstream correctness
fixes and this fork's verified contracts when resolving the integration.

An actual rebase is now **in progress in an isolated detached worktree**, based
on the same official tip. The published branch remains unchanged by that rebase.
The integrated level layer passes its focused build on Lean 4.33.0-rc2; resolved
environment translation/alignment layers and runtime environment also pass
their focused builds. Integration preserves upstream's body-before-primitive
checks, mutual-block model, and theorem-as-Prop-constant semantics. The declaration
frontend replay remains unresolved: overlapping proof APIs and arbitrary-fuel
contracts still need reconciliation. There is **no full candidate build or
completed rebase**, and these maintenance checks remove no semantic admission.

### Upstream contributions

After the initial rebase passes its full validation, submit one coherent,
reviewable proof or correctness fix upstream when it is ready; batch small
dependent changes. Re-check official master, build on its current toolchain,
include regression and transitive-axiom evidence, and keep fork-only status
documents out of the PR. No PR has been opened for this integration checkpoint.

First evaluate the closed quotient-equation pattern repair and the constant-case
confluence proof. Do not submit the substitution port: it already came from
upstream. Reassess the source-preflight contribution against upstream's own
checks; the tested native capture input is already rejected by Lean 4.33.0-rc2.

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

At our source snapshot, the full default `lake build` passes **405 jobs**.
Ten focused fixtures also pass without warnings: `StrongSubstitution`,
`NativeInstantiation`, `Reflection`, `QuotientPatternEquation`,
`ConfluenceConstantReduction`, `NonInductiveDeclarationFrontend`, `Environment`,
`QuotientReductionAlignment`, `QuotientReductionSemantics`, and
`PrimitiveInductiveReceipt`. These fixtures are run separately from the default
build. These receipts describe the published source, not the partially rebased
candidate. Candidate focused builds and the version-specific native test above
are separate integration evidence, not a full build of upstream or the candidate.

| Whole-word `sorry` source census under `Lean4Lean/` | Our fork | Upstream |
| --- | --- | --- |
| Matching lines | 125 | 131 |
| Files containing matches | 23 | 27 |
| Occurrences | 129 | 135 |

This deliberately includes comments and `Experimental` sources. It is a source
census, **not an audit of theorem trust**: removing one admission does not make
every theorem depending on it admission-free, and adding substantial proved
code does not make the raw totals comparable as percentages. Both branches
retain foundational admissions. Our actual frontend's transitive `sorryAx`
dependency is the more important signal.

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
