# Bugs found in the kernel as a result of formalization

* https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Soundness.20bug.3A.20hasLooseBVars.20is.20not.20conservative/near/521286338
* https://github.com/leanprover/lean4/issues/10475
* https://github.com/leanprover/lean4/issues/10511

## Proof audit skipped theorem bodies on Lean 4.33 (2026-10-20)

**Regression-audit defect; no kernel acceptance or theorem contract changed.**
`ConstantInfo.value?` returns theorem proofs by default on Lean 4.29, but
requires `allowOpaque := true` on Lean 4.33. Traversals using the default
accessor therefore inspected theorem types but skipped their proof
references on the newer toolchain. `collectAxioms` still checked axiom
manifests independently; the traversal's separate claim to exclude specific
admitted theorem dependencies was not justified.

For example, after importing
`Lean4Lean.Verify.InductiveRecursiveCallTranslation`, obtain the constant
information for `UArgModelEndpoint.recursiveValueAfterInsertion` in `run_meta`
and inspect `information.value?.isSome`: it is false on Lean 4.33, while
`(information.value? (allowOpaque := true)).isSome` is true. A full traversal
of that theorem using the default accessor reported no direct admission
roots on Lean 4.33; requesting proof values reaches the same seven existing
projection admissions as Lean 4.29.

The recursive-call and preceding rule-stage fixtures now explicitly request
proof values for direct-admission checks and dependency traversal. The new
fixture also pins all seven reached admission declarations, so skipping
proof bodies fails the audit. Its exact inherited axiom manifests and
known-false strengthening/confluence exclusions pass on both toolchains.
Other older fixtures using the default accessor remain an audit-migration
item. This corrects fork-specific audit code, not the documented native API.

## Recursor rule translation staged before fresh recursor signatures (2026-10-20)

**Verification-receipt defect; no native kernel discrepancy demonstrated.**
`NativeInductive.RegistrationEvidence.recursorRuleTranslation` previously
required every recursor rule body to translate in `constructorEnv`, before
the recursor signatures were inserted. That premise is impossible for a
generated rule containing a fresh recursive recursor call.

For a fresh Nat-shaped inductive `RuleStageNat`, the actual generated
successor RHS has the form

```text
fun motive zero succ n => succ n (RuleStageNat.rec motive zero succ n)
```

including the actual dependent binder domains. The recursor name is absent
in the constructor environment. `TrExprS.const` requires a model constant
lookup, and `InductiveRuleTranslation.explicitConstPresent` propagates that
requirement through the whole RHS. The regression fixes the full generated
expression and proves it cannot translate in any model lacking that recursor.
Mutual rules also call recursors inserted later in the batch, so staging
translation immediately after the current signature is insufficient.

The repaired receipt keeps recursor **type** translation in `constructorEnv`
and checks rule-body translation in the **result environment after all
recursor signatures**. It still requires an actual `TrExprS` proof for every
rule; insertion does not derive that proof or install an iota equation.
`RegistrationEntry.RuleSemantics` and its ordered consumer use that same stage.
The new stage API proves all recursor head lookups there and their absence
before insertion, preserving the actual universe-arity requirement. Its
producer-facing head helper needs only the translated signature and insertion,
without assuming rule-body translation or complete registration evidence;
the caller's universe names are mapped explicitly.

Run `lake env lean tests/InductiveRuleTranslation.lean`. On Lean 4.29.0 and
4.33.0-rc2, the fixture checks the exact generated successor RHS and both
mutual call directions. Five complete single/mutual RHSs typecheck after
registration; three recursive RHSs fail on their missing recursor at the
constructor stage, while two base RHSs typecheck there. Formal controls also
reject translating a later mutual head after only the first insertion and
reject the wrong universe arity. The proof audit retains the existing
`TrProj` admission inherited by `TrExprS`'s constructors/recursor; it excludes
direct new admissions, new axioms, native interface axioms and the known-false
strengthening/confluence dependencies. Full rule translation and iota
soundness remain open. No executable acceptance behavior was changed.

## False quotient confluence simulation specification (2026-10-15)

**Verification-model defect, not a demonstrated native kernel soundness bug.**
The last admitted case of `VEnv.NormalEq.parRed` has a counterexample in the
actual quotient reduction instance, even with a concrete well-formed semantic
declaration history and a well-formed local context. It is not a case that can
be completed by a missing pattern-preservation lemma.

Take `P : Prop`, `r : P → P → Prop`, `f : P → Prop`,
`h : ∀ a b, r a b → f a = f b`, `a : P`, and `q : Quot r`. Write:

```text
L = Quot.lift f h q
R = Quot.lift f h (Quot.mk r a)
S = f a
```

1. `L ≡ₚ R`: the majors are proofs of the same proposition, so `NormalEq.proofIrrel`
   and application congruence relate the two eliminators.
2. `R ≫ S`: this is the actual registered, parameter-checked quotient pattern rule.
3. `L ≫* T` implies `T = L`: the neutral major and all other arguments are
   variables/sorts, with no constructor major, beta redex, or registered delta
   rule in the source.
4. `¬ L ≡ₚ S`: the distinct function heads cannot be related by normal equality.
   The only otherwise possible proof-irrelevance cases are excluded because
   the eliminator has a sort telescope type, while its result is a proposition
   (type `Prop`), not a proof of a proposition. Neither term can therefore use
   the proof-irrelevance rule to escape the head mismatch.

Thus the exact conclusion of `NormalEq.parRed` fails. The endpoints still have
the intended semantic equality, proved separately by congruence and quotient
beta; it is the reduction/conversion presentation that fails to simulate it.

Formal artifact: `Lean4Lean/Theory/Typing/QuotConfluenceObstruction.lean`.
Run `lake env lean tests/QuotConfluenceObstruction.lean`. The fixture constructs
an explicit semantic history adding the Eq axiom signature and then quotients;
its well-formedness proof depends only on `propext` and `Quot.sound`. The full
counterexample still inherits separate typing/injectivity admissions
(`propext`, `Quot.sound`, `sorryAx`), which are not claimed repaired. Its
dependency traversal rules out the contradicted confluence theorem and its
derived quotient-injectivity results, as well as `IsDefEqU.weakN_iff` (the
separate false-strengthening report in upstream issue #50). Every owned value
is checked for direct admissions/new axioms.

Minimal native control: `tests/NativeQuotientProofIrrelevance.lean`, importing
only `Lean`. It passes on both Lean **4.29.0** and **4.33.0-rc2**. Native `rfl`
accepts `q = Quot.mk r a` and the constructor beta equality; it does not close
the lifted or final equalities directly, while explicit `congrArg` and
transitivity proofs succeed. The named native controls in the full fixture
have no axiom dependencies. This records native conversion incompleteness,
not acceptance of an invalid theorem.

No executable behavior, theorem statement, admission, or acceptance guard was
changed to conceal the obstruction. In particular, excluding propositional
quotients or adding an unproved stability premise is not a repair. Existing
frontend and quotient claims that inherit the confluence admission remain
conditional on a now-known-false verification contract.

### Checked repair ingredient

`QuotPropReduction.unfold_sound` now proves the semantic unfolding
`Quot.lift f h q ≡ f (Quot.ind (fun _ => P) id q)` at any source universe
equivalent to zero, preserving the source's actual result type. The selector
constructively obtains a proof of `P` from the propositional quotient major;
this uses neither choice nor an arbitrary representative of a Type-valued
quotient. Proof irrelevance reconstructs the major as `Quot.mk` of that proof,
then the registered quotient equation applies. The compatible extension
`QuotPropReduction.Step` therefore simulates this counterexample with one
left step followed by the unchanged `NormalEq`. Weakening and typed
substitution are proved, not extra caller preservation premises.

This does not make the old `NormalEq.parRed` statement true: its relations
are untouched. Full simulation/confluence for the extension, prefix/eta
overlaps, and migration of dependent proofs remain open. The selector and
generic normal-equality join are admission-free/no-choice, while source
typing inversion and actual reduction-model construction retain the already
documented independent `sorryAx` dependencies. The fixture audits those bounds
and excludes the refuted confluence theorem and issue #50's strengthening.
Upstream draft PR #53 already contains this selector/reconstruction direction;
the local result is a focused bridge, not a new competing inductive stack.

`QuotPrefixReduction` extends this ingredient to every partial quotient-lift
prefix using typed function eta in the same compatible presentation. Its
complete transformer introduces precisely the missing binders from the
registered signature, and its proof reconstructs canonical residual typing
from the actual source derivation instead of assuming it from the caller.
All zero through six supplied-argument cases have a generic completeness
theorem and concrete semantic regressions. Weakening and typed substitution
also preserve the generated finite chains. General confluence and eta-overlap
proofs remain unproved; neither the old false contract nor native execution
is changed. This follows the existing upstream draft #53 direction, rather
than asserting a new competing repair design.

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
fixture reject; index 1 accepts. No upstream report has been submitted.

On **2026-10-12**, the same source input was tested on official lean4lean's
Lean **4.33.0-rc2** toolchain (Lean commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`). Native declaration addition now
rejects it with `Kernel.Exception.declHasFVars`, identifying the exact original
constructor name and expression. This specific reproducer is therefore **not
a current-version native bug**; the test does not establish the fixing commit
or correctness for every malformed declaration. The version-specific regression
is `tests/NativeInductiveSourceRejection433.lean`, importing only `Lean`:

```sh
elan run leanprover/lean4:v4.33.0-rc2 lean tests/NativeInductiveSourceRejection433.lean
```

The newer API takes an extra maximum-recursion-depth argument:
`Environment.addDeclCore 0 1000 decl none`. Running the unchanged 4.29.0
fixture on 4.33.0-rc2 only produces an API type error, not evidence about
acceptance or rejection. Keep the original fixture for the branch's 4.29.0 pin.

The old lean4lean frontend has the corresponding capture with ID
`_nested_fresh.2`, reflecting its different fresh-name progression. The regression
in `tests/InductiveSourceChecks.lean` still reproduces that old unguarded
preprocessing/checking pipeline. The full lean4lean frontend now uniformly checks
all original inductive header and constructor types for free variables and
expression/level metavariables **before** preprocessing. It rejects both matching
and nonmatching IDs with the original declaration name/type in the diagnostic.
This deliberate stricter acceptance policy is documented in `divergences.md`.
