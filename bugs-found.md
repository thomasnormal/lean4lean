# Bugs found in the kernel as a result of formalization

* https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338
* https://github.com/leanprover/lean4/issues/10475
* https://github.com/leanprover/lean4/issues/10511

## Inductive constructor source-variable capture (2026-10-08)

Reproduced with the pinned Lean **4.29.0** native kernel. An inductive source
constructor containing an undeclared free variable can be accepted if its ID
matches a fresh parameter generated during nested-inductive preprocessing.
The installed constructor silently replaces that source free variable by a
bound parameter. This is an input-validation/source-capture bug; it does not
by itself demonstrate logical unsoundness or a proof of `False`.

The standalone reproducer is `tests/NativeInductiveSourceCapture.lean`, importing
only `Lean`. Run `lake env lean tests/NativeInductiveSourceCapture.lean`.
It submits the declaration through `Environment.addDeclCore 0 decl none`:

- Header: `NativeSourceCapture (A : Type) : Type`.
- Source constructor: `(A : Type) → fvar(_nested_fresh.1) → NativeSourceCapture A`.
- Installed constructor: `(A : Type) → A → NativeSourceCapture A`.

The test asserts that the original constructor has a free variable, native
declaration addition succeeds, and the stored constructor has the exact changed
bound-variable type and no free variables. Indices 0, 2, and 17 in the same native
fixture reject; index 1 accepts. No upstream report has been submitted, and
behavior on other Lean versions has not been established.

The old lean4lean frontend has the corresponding capture with ID
`_nested_fresh.2`, reflecting its different fresh-name progression. The regression
in `tests/InductiveSourceChecks.lean` still reproduces that old unguarded
preprocessing/checking pipeline. The full lean4lean frontend now uniformly checks
all original inductive header and constructor types for free variables and
expression/level metavariables **before** preprocessing. It rejects both matching
and nonmatching IDs with the original declaration name/type in the diagnostic.
This deliberate stricter acceptance policy is documented in `divergences.md`.
