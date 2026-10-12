# Progress and upstream comparison

Last reviewed: **2026-10-12 (UTC)**. This is the readable overview of the
`poc-verified-noninductive` branch; [PROOF_STATUS.md](PROOF_STATUS.md) holds the
detailed theorem contracts, dependency audits, and regression evidence.

## Bottom line

Our fork has substantial additional checker verification, primitive proofs,
inductive staging work, and regression coverage. It is **not a completed
verification of Lean's kernel**, and it is **not uniformly ahead of official
lean4lean**. Upstream has independently proved ordinary declaration checking
and added newer substitution, primitive, and universe-level results that our
branch has not integrated through Git ancestry.

The main remaining barrier is semantic: the non-inductive frontend is proved
without a direct admission, but its dependencies still include `sorryAx`.
Actual checked inductive/model registration and recursor semantics remain open.
Our executable also deliberately differs from upstream; this is not just a
proof-only patch set.

## Comparison snapshot

The measurements below compare committed source snapshots, not the moving tips
after later documentation or proof commits.

| | Our fork | Official lean4lean |
| --- | --- | --- |
| Repository | `thomasnormal/lean4lean` | `digama0/lean4lean` |
| Branch | `poc-verified-noninductive` | `master` |
| Source snapshot | `c0f993057a1a6b35f1441dc3dd15749dba5ce5e8` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` |
| Snapshot date | 2026-10-12 | 2026-10-10 |
| Lean toolchain | `v4.29.0` | `v4.33.0-rc2` |
| Commits since the common ancestor | 319 branch-only | 49 upstream-only |
| Lean modules under `Lean4Lean/Verify/` | 265 | 36 |
| Lean modules under `Lean4Lean/Theory/` | 27 | 21 |
| Lean fixtures under `tests/` | 184 | 0 in this directory |

Common ancestor: `8865b155abbf68d3a827fb3568bf6839780163c2`, dated 2026-07-06
(`feat: dynamic fuel config`). The tip-to-tip diff spans 529 files. These are
ancestry and source-size measures, **not counts of unique improvements or a
proof-completion percentage**. For example, our `15b263d` frontend-theorem
statement is patch-equivalent to an upstream commit. The fixture count also does
not imply upstream has no tests or CI elsewhere.

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
| Metatheory and reductions | Recent quotient beta/alignment work, a proved constant confluence case, and the actual closed quotient equation's guarded pattern certificate. | Full confluence, injectivity/strengthening, genuine projection semantics, and recursor soundness remain open. Upstream's newer strong simultaneous substitution proofs deserve review. |

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

## What upstream has that we should review

The 49 upstream-only commits are not merely maintenance. Particularly relevant:

- `67f63b0` (2026-10-10): compare primitive types up to metadata.
- `6ba54db` and `8223d22` (2026-08-29): strong simultaneous substitution
  (`substDF`) and closure of substitution admissions.
- `ac1498a`, `c195b64`, and related commits (2026-08-29): primitive checking
  invariants, clauses, and the inductive guard.
- `4b60e53` (2026-08-14): compute the K-target flag where the kernel does.
- The August level-normalization soundness/completeness work, lazy-delta and
  projection improvements, and stage-2 replay/toolchain updates.

These are candidates for targeted comparison and porting, not evidence that
their changes are already present here. No merge, rebase, cherry-pick, or
toolchain upgrade was performed for this status review. Review overlapping
proofs before duplicating them; a wholesale integration needs compatibility
work because our checker and toolchain have diverged.

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

At our source snapshot, the full default `lake build` passes **405 jobs**.
Seven focused fixtures also pass without warnings: `QuotientPatternEquation`,
`ConfluenceConstantReduction`, `NonInductiveDeclarationFrontend`, `Environment`,
`QuotientReductionAlignment`, `QuotientReductionSemantics`, and
`PrimitiveInductiveReceipt`. These fixtures are run separately from the default
build. This review did not build upstream with its different toolchain.

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
workstream boundaries, and record validation and dependency-audit changes.
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
