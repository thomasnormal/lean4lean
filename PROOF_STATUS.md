# Non-inductive verification proof of concept

This fork is an incomplete, conditional verification checkpoint, not a proof of
all of Lean. The intended review branch is `poc-verified-noninductive`.

## What is proved

- `addDeclVerified.WF` preserves environment well-formedness and extension for
  successful checked declarations. Its entry point supports axioms, definitions,
  theorems, opaque declarations, unsafe/partial mutual definitions, and a checked
  quotient wrapper; it explicitly rejects inductives.
- `VEnvs.WF.empty`, `addDeclVerified.foldlM_WF`, and
  `addDeclVerified.fromEmpty` provide initialization and composition for finite
  declaration sequences. These are partial-correctness statements: they do not
  promise that checking any particular declaration succeeds.
- The replacement level normalizer preserves evaluation. The comparison core
  agrees with upstream `geq.go`, and the public comparison/equivalence tests are
  sound. Exact syntactic agreement of the entire normalizer with upstream is
  regression-tested, not proved.
- `NatAddSpec.eval` derives literal addition from the checked open zero/successor
  equations. The primitive-check bridge supplies those equations, and the
  declaration proof reconstructs addition reflection in the extended environment.
  The bridge uses the old environment's primitive invariant, not the invariant it
  is trying to establish. The native addition reduction is enabled again.
- `NatMulSpec.eval` derives literal multiplication from its zero/successor
  equations and typed addition reflection. Multiplication's primitive-check and
  environment-extension proofs are connected, and its native reduction is also
  enabled. `HasPrimitives` now records the function types of addition and
  multiplication as well as their literal evaluation: the type information is
  needed when checking equations that use already-declared primitives on variables.
- `NatPowSpec.eval` derives exponentiation from its checked equations and typed
  multiplication reflection. Its declaration-extension proof and native reduction
  are connected. The equation proof covers all natural exponents; the native
  reduction retains its existing `2^24` exponent limit.
- `NatPredSpec.eval` and `NatSubSpec.eval` derive predecessor and truncated
  subtraction from their checked equations. Both declaration-extension proofs
  are connected, and native subtraction is restored. The environment invariant
  records predecessor's typed evaluation and the function types needed by later
  primitives. A shared extension lemma preserves the unchanged primitives.
- `NatBeqSpec.eval` derives Boolean natural-number equality from the four checked
  zero/successor equations. The primitive-check and environment-extension proofs
  are connected, and native equality reduction is restored.
- `NatBleSpec.eval` similarly derives Boolean natural-number ordering. Its
  primitive-check and environment-extension proofs are connected, and native
  ordering reduction is restored. Equality and ordering share the verification
  of their common checking sequence; their executable checks are unchanged.
- `NatShiftLeftSpec.eval` derives left shift by induction on the shift count,
  generalizing the input value and using typed multiplication reflection for the
  doubling step. Its primitive-check and environment-extension proofs are
  connected, and native left-shift reduction is restored.
- `NatDivLoopSpec.eval` and `NatDivSpec.eval` establish division evaluation from
  explicit loop and entry equations, retaining the typed positivity and fuel
  witnesses. These are intermediate contracts, not new `HasPrimitives` fields:
  deriving them from the checked dependent conditionals remains open, and native
  division remains disabled. `Reflection.check.WF` verifies the reflection-family
  type check; an `M.WF.withLocalDecl` wrapper exposes the existing local-context
  rule for the remaining conditional checks.
- `Reflection.checkNatDITETypes.WF` verifies the four initial type checks of the
  dependent conditional validator, including both witness converters. The
  `checkNatDITE_eq` theorem proves that regrouping this prefix reconstructs the
  unchanged executable. Correctly typed witness converters alone do not establish
  correct branch selection.
- `Reflection.checkNatDITE.WF` now derives both typed computation equations from
  the full validator, including its fresh-local checks. `NatDITESpec.apply`
  instantiates the open equations with closed propositions, branches, and typed
  witnesses. `NatDITESpec.eval` also handles a Boolean argument that reduces to
  a literal, converting the dependent witness along that equality.
- `Condition.check_reflectNatNat.WF` verifies the dependent-conditional path of
  the reflected condition validator, and `Condition.natLE.check.WF` specializes
  it to natural-number ordering. The proof extracts translations of the Boolean
  function and proof term from the checked decision function by substitution,
  and records its checked equality to the declared decision function. It still
  requires a translation of the proposition function used by the initial
  infer-only check. Division checks that proposition explicitly, but currently
  does so after checking the condition; this ordering needs to be addressed in
  its bridge proof. Deriving the division entry/loop contracts remains unfinished,
  and native division is still disabled. No executable checks changed in this
  checkpoint.

Main review entry points: `Lean4Lean/Verify/Environment.lean`,
`Lean4Lean/Verify/Primitive.lean`, and `Lean4Lean/Verify/Level.lean`.

## What this does not establish

- The frontend and primitive-check bridge still inherit `sorryAx` from the
  existing verification/metatheory stack. Even the empty-environment theorem's
  axiom audit includes it. No claim of unconditional kernel soundness is made.
- `AddInduct` still has no constructors. There is no verified translation of the
  actual Lean prelude, and the restricted frontend cannot bootstrap `Nat`/`Bool`
  inductives. Arithmetic results are conditional on an appropriate starting
  environment translation; runtime tests against the imported prelude do not
  construct that translation.
- Native binary reductions other than addition, multiplication, exponentiation,
  subtraction, equality, ordering, and left shift remain disabled.
  Restoring them with their primitive-extension proofs is unfinished work, not
  an optional optimization that can be dropped from the objective.
- The unrestricted `addDecl.WF` and the existing inductive/injectivity/
  strengthening obligations remain open. The experimental subsumption algorithm
  is not the verified public level-comparison path.

This is a modified executable, not merely new proofs about an unchanged checker:
it includes the restricted frontend, additional primitive validation, safe-only
delta unfolding, the level replacement, and the reduced native-arithmetic set.
Those behavioral changes need review alongside the proofs.

## Reproduction and evidence

Using the pinned toolchain, the package was rebuilt from clean generated outputs
(dependency build caches retained):

```sh
lake clean lean4lean
lake build Lean4Lean.Theory Lean4Lean.Verify lean4lean
lake env lean tests/Environment.lean
lake env lean tests/Primitive.lean
lake env lean tests/Reflection.lean
lake env lean --run tests/Levels.lean
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Primitive
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Environment
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Level
```

The tests cover acceptance/rejection from an empty environment, rejection of
incorrect arithmetic implementations, large literal arithmetic with low fuel,
subtraction truncation at zero, equal and unequal large literals, rejection of
incorrect equality and ordering implementations, left shifts beyond machine-word
sizes, both sides of the native exponent-limit boundary, and
agreement with upstream on 3,280 small normalizations and 10,000 generated level
cases. The executable successfully replayed 550 declarations across the primitive
and environment verification modules, and 511 declarations in the level verification
module. Restoring native ordering resolved the previous deterministic timeout in
`Lean.Level.mkData_depth`.
This is module replay against imported dependencies, not a
verified replay of the entire dependency closure.

The reflection regressions accept both supported reflection encodings and reject
swapped proof converters. They also check selectors that ignore their Boolean
argument: their type-checking prefixes succeed, while their computation checks
fail. These are runtime checks against the imported prelude, not a proof of its
environment translation.
The full natural-number ordering and equality condition validators are also
tested: both are accepted, and replacing their decision function, Boolean
function, or proof with an invalid one is rejected.

`#print axioms` reports only `propext` and `Quot.sound` for
`Lean4Lean.VEnv.NatAddSpec.eval`, `.reflects`, `Lean4Lean.VEnv.NatMulSpec.eval`,
`Lean4Lean.VEnv.NatPowSpec.eval`, `Lean4Lean.VEnv.NatPredSpec.eval`, and
`Lean4Lean.VEnv.NatSubSpec.eval`, as well as `Lean4Lean.VEnv.NatBeqSpec.eval` and
`Lean4Lean.VEnv.NatBleSpec.eval` and `Lean4Lean.VEnv.NatShiftLeftSpec.eval`. The shared
`Lean4Lean.VEnv.HasPrimitives.extendPrimitive` lemma has the same axiom set.
`Lean4Lean.VEnv.NatDivLoopSpec.eval` and `Lean4Lean.VEnv.NatDivSpec.eval` use
`propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`. The new
reflection-check and local-context lemmas inherit the existing verification
stack's axioms, including `sorryAx`.
The witness-application lemmas `Reflection.ofTrueType.apply` and
`Reflection.ofFalseType.apply` use only `propext`; `Reflection.checkNatDITE_eq`
uses `propext`, `Classical.choice`, and `Quot.sound`. The new type-checking-prefix
and fresh-local equation-extraction proofs inherit `sorryAx` and the existing
implementation-interface axioms.
`Reflection.NatDITESpec.apply` and `.eval` use only `propext` and `Quot.sound`.
`Reflection.checkNatDITE.WF`, which extracts the computation equations from the
executable checks, inherits `sorryAx` and the implementation-interface axioms.
The same inherited axioms appear in `Condition.check_reflectNatNat.WF` and
`Condition.natLE.check.WF`.
The level soundness theorems
`Lean.Level.normalizeCore_eval`, `geq'_wf`, and `isEquiv'_wf` use the standard
logical axioms and the existing `Lean.Level.instLawfulBEqLevel` interface axiom,
without `sorryAx`. The frontend audit includes `sorryAx` and the existing
implementation-interface axioms, as noted above.

AI assistance: drafted and iterated with OpenAI Codex, compiled and tested
locally. Not yet human-reviewed. No PR or Zulip message has been submitted.
