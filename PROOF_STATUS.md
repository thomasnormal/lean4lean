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
- `Environment.checkPrimitiveInductive.eq_true_iff` characterizes exactly when
  the primitive-inductive validator returns `true`: a safe, monomorphic,
  parameter-free singleton declaration with precisely the `Bool` or `Nat`
  header and constructors. Successor binder names and annotations are unrestricted,
  as in the executable validator. `checkPrimitiveInductive.WF` exposes this
  classification as a partial-correctness contract. These shape proofs do not
  establish the correctness of inductive elaboration or its generated recursors.
  Their axiom audits contain no `sorryAx`, but do include the existing expression,
  level, and syntax equality interface assumptions listed below.
- `VEnv.addInductHeaders` models fresh registration of arbitrary inductive
  headers. Successful registration extends the existing constants, installs
  every header, preserves the definitional equations, and preserves `Ordered`
  when the header types are well-formed. `VInductDecl.HeadersWF` checks uniform
  universe-parameter counts and well-formed header types. Canonical `Bool`/`Nat`
  declarations satisfy this header-only specification in any starting environment.
- `PrimitiveInductiveDecl.toVDecl` and `checkPrimitiveInductive.toVDecl` connect
  the recognized primitive shapes to those canonical declarations. Their
  `TrInductDecl` translations check datatype headers in the old environment and
  constructor types in the successfully registered header environment, where
  recursive datatype references are available. These translations do not prove
  the full inductive frontend; no recursor or reduction equation is installed at
  this stage.
- `AddInductive.declareInductiveTypes.refines` now connects the executable header
  stage to `VEnv.addInductHeaders`. Given an initially `Aligned` constant map,
  translated headers, an admitting safety filter, and exactly one index-count
  entry per datatype, successful registration produces the corresponding abstract
  header environment and preserves alignment. The `ordered` corollary also
  preserves orderedness when the translated header types are well-formed.
  This proof covers arbitrary header batches, including mutually declared and
  unsafe headers, without changing the executable checker. The preceding stage's
  header-size invariant is now proved, but its semantic translation invariants
  remain open.
- `AddInductive.checkInductiveTypes.headerSizes` proves that its continuation
  receives exactly one index-count entry and one datatype constant per input
  datatype. The continuation-style theorem supports arbitrary result
  postconditions; `getHeaderSizes` specializes it to returning the statistics.
  The proof follows both nested executable loops and does not assume a verified
  starting environment or type-checker correctness. It establishes cardinality,
  not header translation, parameter typing, or full inductive soundness.
- `AddInductive.checkInductiveTypes.frameHeaderSizes` strengthens that contract:
  the continuation also sees the original environment, universe parameters,
  safety, primitive authorization, and fuel configuration. `Context.HeaderFrame`
  packages these equalities; local contexts and fresh-name generators are
  deliberately excluded because binder traversal changes them. The `frame`
  corollary discards the size information, while `getFrameHeaderSizes` returns
  statistics and the observed callback context. These proofs preserve the older
  size-only API and do not establish semantic header translation.
- `AddInductive.checkInductiveTypes.refinesHeaders` composes the actual checked
  type prefix with `declareInductiveTypes`, refining the resulting environment
  against `VEnv.addInductHeaders`. No externally constructed statistics or
  array-length premise is required: the preceding stage supplies the size and
  frame invariants. Initial alignment, header translation, and an admitting
  safety filter remain explicit assumptions. `orderedHeaders` also preserves
  orderedness when the translated header types are well-formed; their typing is
  not derived from the concrete check in this theorem. This is partial
  correctness of the checked-header prefix, not full inductive frontend
  correctness, constructor installation, positivity, or recursor soundness.
- `VEnv.addConstructorHeaders` installs constructor signatures as fresh ordinary
  typed constants. Its append, extension, installed-lookup, equation-preservation,
  and orderedness properties are proved. `AddInductive.declareConstructors.refines`
  follows both executable registration folds and preserves `Aligned`, given
  translated constructor types and an admitting safety filter. The `ordered`
  corollary additionally assumes abstract constructor-type well-formedness.
  This stage does not justify constructor arities, parent/index metadata,
  parameter-count assertions, positivity, projection/injectivity behavior,
  recursor generation, or inductive reduction equations. It does not extend the
  full `TrEnv` relation or discharge `AddInduct`.
- `AddInductive.checkInductiveTypes.frameHeaderSizesParamsFVars` additionally
  proves that every checked parameter is syntactically a free variable, while
  retaining the size and frame invariants and their existing APIs. `paramsFVars`
  supplies that invariant to arbitrary continuations, and `getParamsFVars`
  specializes it to returned statistics. No starting-environment or
  type-checker soundness premise is needed. This free-variable-only contract
  does not establish parameter typing or local-context hygiene.
- `AddInductive.checkInductiveTypes.frameHeaderSizesParamsDistinct` strengthens
  that contract with `stats.params.toList.Nodup`; `paramsNodup` and
  `getParamsNodup` specialize it to arbitrary continuations and returned
  statistics. All older size/frame/free-variable signatures remain unchanged.
  The proof tracks generated parameter names reserved by the current name
  generator, rules out its current name before each push, and preserves
  reservations across fresh parameter/index introductions and mutual types.
  No initial environment, local-context, generator-freshness, or type-checker
  soundness premise is required. This proves parameter-array distinctness,
  not freshness relative to arbitrary preexisting local declarations.
- `Verify.ConstructorArity` proves offset additivity for the actual executable
  constructor binder counter and that substituting a free variable preserves
  its raw leading-forall spine. Consuming one forall binder therefore preserves
  the total when the counter advances by one. The checked parameter invariant
  supplies the substitution premise through `checkInductiveTypes.parameterArity`.
  The specification-level substitution proof uses only `propext`; its bridge to
  `Expr.instantiate1` additionally uses the existing `Lean.Expr.instantiate1_eq`
  interface axiom, without `sorryAx`. These arity prerequisites feed the
  constructor parameter-consumption proof below; composing the full constructor
  batch remains open.
- `Verify.ConstructorParams` proves that the executable return-application check
  requires a matching argument at every parameter position. For free-variable
  parameters, arbitrary `FVarsIn` predicates on the return expression therefore
  hold on each parameter. `InductiveStats.RemainingParamsAbsent` tracks exclusion
  of unconsumed parameters; it starts from a source with no free/metavariables
  and survives consuming a distinct stored parameter. A valid terminal return
  forces all parameters to have been consumed. `checkConstructors.loop_arity`
  follows the actual fuel-recursive inner checker and derives the raw arity
  lower bound from that invariant, free-variable parameters, and an explicit
  `stats.params.toList.Nodup` premise. Field traversal needs no additional local
  freshness premise: its branch already has no parameters left to consume.
  `loop_arity_of_noFVars` specializes this to closed source types, while
  `checked_loop_arity` supplies closedness from the real no-metavariable/free-variable
  guard. The latter concerns the guard followed by the inner loop, not the
  complete nested constructor batch. `checkInductiveTypes.checkedConstructorArity`
  composes the real checked-type continuation with that guard/inner-loop bridge,
  supplying both free-variable shape and distinctness internally. It requires
  no externally constructed statistics or parameter-invariant premises and
  returns the checked statistics with their raw constructor-arity bound.
  The composition does not register datatype headers, check constructor type
  well-formedness, or traverse the full constructor batch; neither field-count
  registration composition nor full positivity/inductive soundness follows.
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
- `NatShiftRightSpec.eval` derives right shift by induction on the shift count,
  using typed division reflection for division by two. Its primitive-check and
  environment-extension proofs are connected, and native right-shift reduction
  is restored. Both shift validators are unchanged. The native dispatch proof
  uses explicit Boolean-equality simplification and splits only the current
  test, avoiding repeated simplification of the growing remaining dispatch chain.
- `NatDivLoopSpec.eval` and `NatDivSpec.eval` establish division evaluation from
  explicit loop and entry equations, retaining the typed positivity and fuel
  witnesses. The full validator and declaration-extension proofs now supply
  these intermediate contracts, and native division is restored.
  `HasPrimitives` records division's typed literal evaluation; the extension
  proof establishes it from the old environment's invariant and the checked
  equations, without assuming the new declaration's correctness.
  `Reflection.check.WF` verifies the
  reflection-family type check; an `M.WF.withLocalDecl` wrapper exposes the existing local-context
  rule for the remaining conditional checks.
- `NatModLoopSpec.eval` and `NatModSpec.eval` establish remainder evaluation
  from explicit loop and entry contracts, including zero divisors and the
  early return when the dividend is smaller. The loop retains its typed
  positivity and fuel-bound witnesses and shares division's dependent argument
  shape. The full modulo validator now supplies these contracts; its
  declaration-extension proof and native reduction are connected.
  `HasPrimitives` records modulo's literal evaluation and function type, and the
  extension proof establishes both from the checked equations. No modulo
  validation checks were changed.
- `NatGcdSpec.eval` derives literal GCD evaluation by strong induction on the
  first argument, using typed modulo evaluation to reduce the recursive input.
  The contract explicitly requires equations for the original candidate, not
  merely the equation body returned by the well-founded validator.
  `.reflects` transports evaluation from the old environment into an extension
  and connects it to the newly declared constant, without assuming the new
  environment's primitive invariant.
- `NatBitwiseSpec.eval` derives literal bitwise evaluation for an arbitrary
  Boolean binary function, by strong induction on the first natural-number
  input. Its contract contains the two zero cases and the positive step after
  evaluating the conditionals and recursive arguments. Typed addition evaluates
  the doubling and optional increment. `.reflects` likewise evaluates using the
  old environment's invariant before transporting the result into an extension.
  The executable validator does not yet supply either of these new contracts;
  native GCD, AND, OR, and XOR remain disabled. These are intermediate proofs
  toward restoring those reductions, not replacements for the missing bridge.
- `Reflection.checkITE.WF` extracts the two polymorphic branch equations from
  the complete conditional validator. `ITESpec.apply` instantiates them, and
  `.eval` evaluates the selector after its Boolean argument reduces, retaining
  the reflection witness and both branch types. The carrier's `Type` universe
  bound remains explicit; arbitrary primitive well-formedness does not imply
  that bound. The two reference branch expressions are shared with the
  executable validator via `iteBranchExpr`; no validation checks were removed.
  `Reflection.ite_witness` recovers the reflection witness's canonical type
  from a translation of the actual polymorphic selector and decision application.
  `Condition.natLE.checkITE.WF` verifies the condition validator with both
  conditional modes enabled, retaining the existing dependent-selector facts
  alongside `ITEChecked`. The dependent-only theorem's statement is unchanged.
  These are used by the full modulo bridge, not sufficient in isolation.
- `Reflection.ite_carrier` recovers the carrier's `Type` bound from the
  selector's structural translation and the actual `ite` application.
  `ITEInstance` packages the typed selector and reflection input.
  `Condition.ReflectedNatNatChecked.ite_apply` instantiates it at typed
  natural-number arguments; `.ite_branches` recovers both branch types;
  `.ite_translate` connects the declared conditional through its checked decision
  function to the selector; and `.ite_eval` returns the selected branch.
  `.natBle_ite_eval_inputs` specializes this to verified literal ordering.
  The carrier's bound is derived rather than assumed from `HasPrimitives`.
- `natMod_start`, `natMod_step`, and `natBle_dite_false_inputs` evaluate the
  modulo-specific dependent branches, retaining positivity and fuel witnesses.
  The positive entry helper shares the existing division proof through a private
  generic loop helper; the published division-entry statement is unchanged.
  `natMod_entry_start` and `natMod_entry_stop` evaluate the complete nested
  `natModEntryAt` template for a positive in-range divisor, a zero divisor, or
  an oversized divisor. These proofs start from supplied structural translations.
  These supply the branch reductions used by the complete modulo validator
  proof; they are not sufficient without extracting the actual checked equations.
- `natModEntryBody.spec` supplies the successor entry contracts from the open
  two-local equation, including zero and oversized divisors.
  `natModLoopBody.spec` supplies the recursive contract from the open five-local
  equation, preserving the dependent proof arguments. Their source substitution
  lemmas identify the templates with the executable fresh-local bodies and their
  literal instances. The recursive substitution proof is shared with division
  through a private helper; division's published statement is unchanged.
  `NatModSpec.ofEntry` combines these contracts with a separately supplied zero
  equation. `checkNatModRecursion.WF` extracts the five-local recursive equation
  using a private helper shared with division; division's published statement
  is unchanged. `checkNatModEquations.WF` extracts the entry equation in the
  surrounding two-local context and assembles the contracts in executable order.
  `checkPrimitiveDef_natMod.WF` additionally extracts the zero equation from its
  checked lambda and retains the guard, proposition check, loop-type check,
  and both conditional modes. `.extension` supplies the restored invariant
  fields, which the frontend and native-reduction proofs now use.
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
  infer-only check. `checkNatDivCondition.WF` now supplies that translation from
  the explicit proposition check: division's existing checks have been factored
  into this helper, with the proposition check performed before the condition
  validator.
- `Reflection.natDITE_witness` derives the dependent witness's required type
  from the checked selector and decision application. `NatDITEInstance`
  packages the selector, converters, equations, and typed input.
  `Condition.ReflectedNatNatChecked.apply` instantiates a checked condition at
  arbitrary typed natural-number arguments, and `.natBle_apply` connects
  literal arguments to the verified Boolean ordering primitive. These proofs
  use the existing unique-typing and weakening-inversion APIs and inherit their
  metatheory assumptions.
- `Condition.ReflectedNatNatChecked.natDITE_translate` connects the actual
  declared dependent conditional to the reflected selector application. It
  instantiates the checked decision-function equality, replaces that argument
  inside the typed conditional, and compares translations after beta-reducing
  the selector. `.natDITE_eval` then derives the selected branch equation when
  the Boolean argument reduces to a literal. Both the branch functions and the
  dependent witness retain their typing premises. These semantic bridges are
  now connected to division's full executable validator.
- `Condition.ReflectedNatNatChecked.natDITE_branches` recovers the canonical
  dependent branch types from the actual conditional translation.
  `.natBle_dite_eval` combines this with the verified Boolean ordering primitive
  and returns the selected branch together with its typed proof argument, without
  asking the caller to provide the branch types. `.natBle_dite_zero_of_gt`
  establishes the zero-valued false branch used by division's entry and stopping
  cases.
- `natDivLoopType.apply` verifies the loop's five dependent applications,
  retaining the positivity and fuel-bound witnesses. `checkNatDivLoop.WF`
  connects the executable loop-type check to that abstract type, and
  `checkNatDivPrefix.WF` verifies it together with the preceding condition checks.
  These are proofs of the existing checking fragments, now used by the complete
  division validator proof.
- `Condition.ReflectedNatNatChecked.natBle_dite_eval_inputs` accepts arbitrary
  typed source arguments translated to natural-number values, retaining a source
  expression for the selected proof witness. `.natBle_dite_body_inputs` reduces
  the selected branch lambda; `.natBle_dite_zero_inputs` handles the false branch.
  The existing literal-specific statements are unchanged.
- `tr_natDivLoopApp` recovers both proof arguments of a checked loop application
  at its canonical dependent type. `.natDiv_start` combines it with branch
  reduction to prove the positive entry equation with successor fuel, including
  the constructor-form comparison argument `Nat.succ Nat.zero`. `.natDiv_zero`
  proves the zero-divisor entry branch. The full primitive-check bridge now
  extracts the translations and equations needed by these semantic bridges
  from division's fresh-local checks.
- `natDivLoopExpr.proofIrrel` shows that changing the typed positivity or
  fuel-bound proof does not change a loop result. `.natDiv_step` reduces the
  selected recursive branch, evaluates its subtraction using the already
  verified primitive, and recovers the new fuel-bound proof at the canonical loop
  type. Proof irrelevance restores the supplied positivity witness; neither
  witness is erased from the statement. This is still a semantic bridge from a
  supplied translation of the conditional, not the full primitive-check proof.
- `checkNatDivEntry.WF` extracts the open equation and structural translation
  from the actual two-fresh-local entry-check fragment. `natDivEntryBody.at_literals`
  instantiates both together, providing the translation needed by the entry
  branch-evaluation lemmas. This is also used when assembling the complete
  division specification; the executable checks are unchanged.
- `checkNatDivEntry.spec` evaluates both branches of the actual entry-check
  fragment and supplies `NatDivEntrySpec`; `NatDivSpec.ofEntry` combines that
  contract with a loop contract without changing the existing specification.
  `Condition.ReflectedNatNatChecked.natBle_witness` constructs source witnesses
  from the checked reflection machinery, so substituting into a structural
  translation does not assume every abstract proof has a source representation.
- `natDivLoopBody.spec` derives `NatDivLoopSpec` from the open recursive equation
  and its structural translation. It substitutes reflected witnesses, evaluates
  the selected branch, and uses proof irrelevance to cover arbitrary abstract
  proof arguments. The source substitution lemmas also identify this open body
  with the executable recursive-check body and retain its literal-instance
  translation. `checkNatDivRecursion.WF` extracts the open recursive equation
  from the actual five-local checks, retaining the dependent proof arguments.
  `checkNatDivEquations.WF` combines the entry and recursive checks in their
  executable order. `checkPrimitiveDef_natDiv.WF` verifies the full validator,
  including its guard and type checks; `.extension` derives typed literal
  division for the extended environment. The declaration and native-reduction
  proofs are connected. No division validation checks were changed.

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
  The abstract header-registration, executable-prefix refinement, and primitive
  translation bridges do not discharge this obligation. Constructor/recursor
  generation, inductive reduction equations, and the semantic statistics/header
  translation invariants of the preceding stage remain unverified; the paired
  header-array lengths are now proved.
- Native `Nat.gcd`, `Nat.land`, `Nat.lor`, and `Nat.xor` reductions
  remain disabled.
  Restoring them with their primitive-extension proofs is unfinished work, not
  an optional optimization that can be dropped from the objective.
- The unrestricted `addDecl.WF` and the existing inductive/injectivity/
  strengthening obligations remain open. The experimental subsumption algorithm
  is not the verified public level-comparison path.
- Full syntactic agreement with the upstream level normalizer remains
  regression-tested, not proved. Upstream `Lean.Level.normalize` and several of
  its helpers are partial definitions whose implementations are opaque to Lean's
  logic. No additional interface assumption has been introduced to assert that
  agreement. The total fork normalizer's evaluation-preservation proof and the
  comparison core's agreement theorem are independent of such an assumption.

This is a modified executable, not merely new proofs about an unchanged checker:
it includes the restricted frontend, additional primitive validation, safe-only
delta unfolding, the level replacement, and the reduced native-arithmetic set.
Those behavioral changes need review alongside the proofs.

## Well-founded primitive validation gap

`tests/WellFoundedGap.lean` characterizes a missing obligation before restoring
native GCD and bitwise reduction. It defines otherwise ordinary Euclidean GCD
and bitwise functions with termination measures `m + measureOffset` and
`n + measureOffset`, where `measureOffset` is an opaque natural-number constant
defined to be zero. Both definitions type-check, and both pass this fork's
primitive validators when supplied as the corresponding primitive's value.
Nevertheless, comparison of their applications on literals with the expected
result returns `false`, both in Lean4Lean and in Lean's own comparison at full
transparency. The examples include GCD at `(0, 5)` and `(6, 9)`, and bitwise
AND/OR/XOR at those inputs. Comparisons terminate normally rather than exhausting
fuel.

The test also shows that the equation body returned by `unfoldNatWellFounded`
does reduce GCD at `(0, 5)` to `5`. The missing connection is between that body
and the original well-founded fixpoint. `WellFounded.Nat.fix` obtains its fuel
from `Nat.eager (measure input + 1)`; an opaque measure need not evaluate on
literal inputs. The library's `WellFounded.Nat.fix_eq` is a propositional
equation, not automatically an abstract definitional-equality derivation.

The example functions are propositionally equal to the reference functions for
all inputs: `WellFoundedGap.measuredGcd_eq` and `.measuredBitwise_eq` are proved,
and their axiom audits contain only `propext` and `Quot.sound`. Thus these are
not demonstrated wrong arithmetic results or a Lean kernel soundness exploit.
The executable comparisons also do not constitute a formal non-derivability
proof about the abstract typing judgment. They do show why extracting the checked
equation body alone is insufficient evidence for the needed primitive-extension
contract.

One possible repair is to check that the measure applied to the initial state
is definitionally the designated natural-number argument (the first GCD
argument, or the first natural-number bitwise argument). Its computation on
literals would then follow from already verified facts. That restriction and
the subsequent fixpoint simulation still need a proof; neither is implemented
here. A more permissive alternative would require a checked literal-computation
contract for the measure. Native GCD and bitwise reductions remain disabled.

The diagnostic now extracts the initial measure using the validator's existing
unfolding prefix and tests the proposed equality guard without changing the
validator. Both reference definitions pass: GCD's measure equals its first
argument, and bitwise's measure equals its first natural-number argument. The
opaque-offset candidates fail that guard. For GCD, a generic `offsetGcd k`
fixture additionally distinguishes a transparent zero offset (which passes)
from a transparent one offset (which fails). Both transparent-offset fixtures
pass the current primitive validator and compare definitionally equal to the
expected results at `(0, 5)` and `(6, 9)`. `offsetGcd_eq` proves propositional
equality with the reference GCD for all offsets and inputs, using only `propext`
and `Quot.sound`.

Consequently, requiring exactly the canonical measure would accept the pinned
reference definitions and rule out the demonstrated opaque-measure gap, but
would also reject the computable `m + 1` variant. It is a conservative restriction
on accepted implementations, not a claim that every rejected implementation is
incorrect. A more permissive repair should certify computation of the measure
rather than merely testing its equality with the input. Selecting and authorizing
that acceptance-policy change is still pending; no new guard is enabled.

This diagnostic concerns the fork after its earlier lambda-wrapper correction
in `unfoldNatWellFounded`, not a demonstration that unmodified upstream `master`
accepts these examples. The test intentionally asserts the current acceptance
behavior and must be updated when the validator is hardened.
It was compiled and axiom-audited separately after a successful cached build of
both proof libraries and the executable. It changes no kernel implementation
or verification-library proof.

## Reproduction and evidence

Using the pinned toolchain, the package was rebuilt from clean generated outputs
(dependency build caches retained):

```sh
lake clean lean4lean
lake build Lean4Lean.Theory Lean4Lean.Verify lean4lean
lake env lean tests/Environment.lean
lake env lean tests/PrimitiveInductive.lean
lake env lean tests/InductiveHeaders.lean
lake env lean tests/InductiveStats.lean
lake env lean tests/ConstructorHeaders.lean
lake env lean tests/ConstructorArity.lean
lake env lean tests/ConstructorParams.lean
lake env lean tests/Primitive.lean
lake env lean tests/Reflection.lean
lake env lean tests/Division.lean
lake env lean tests/Modulo.lean
lake env lean tests/WellFoundedGap.lean
lake env lean tests/GcdAndBitwise.lean
lake env lean --run tests/Levels.lean
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Primitive
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Environment
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Level
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.PrimitiveInductive
lake env .lake/build/bin/lean4lean Lean4Lean.Theory.InductiveHeaders
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.Inductive
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveHeaders
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveStats
lake env .lake/build/bin/lean4lean Lean4Lean.Theory.ConstructorHeaders
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorHeaders
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorArity
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorParams
```

The tests cover acceptance/rejection from an empty environment, rejection of
incorrect arithmetic implementations, large literal arithmetic with low fuel,
subtraction truncation at zero, equal and unequal large literals, rejection of
incorrect equality and ordering implementations, left shifts beyond machine-word
sizes, right shifts at and beyond the input's bit length (including a shift count
beyond machine-word sizes), both sides of the native exponent-limit boundary, and
agreement with upstream on 3,280 small normalizations and 10,000 generated level
cases. The executable successfully replayed 902 declarations across the primitive
and environment verification modules, and 511 declarations in the level verification
module. Restoring native ordering resolved the previous deterministic timeout in
`Lean.Level.mkData_depth`.
This is module replay against imported dependencies, not a
verified replay of the entire dependency closure.

`tests/PrimitiveInductive.lean` runs 39 primitive-inductive checks against each
of an empty and an imported environment. It covers both accepted shapes,
all four successor binder annotations and three binder names, declined headers
and nonprimitive declarations, and rejected malformed constructor lists/types.
It also audits both new validator theorems, allowing only the existing
axioms `propext`, `Classical.choice`, `Quot.sound`, `Lean.Expr.eqv_eq`,
`Lean.Level.instLawfulBEqLevel`, and `Lean.Syntax.structEq_eq`; any additional
axiom, including `sorryAx`, fails the regression. These interface assumptions
are already present in `Verify.Axioms`; no new assumption is introduced here.
Focused executable replay of `Lean4Lean.Verify.PrimitiveInductive` checks 43
declarations successfully; as above, imported dependencies are assumed correct.

`tests/InductiveHeaders.lean` checks successful registration, registered type
lookups, duplicate/collision rejection, empty batches, polymorphic headers, and
orderedness, with eighteen proof regressions and fourteen axiom audits. It
confirms that the header stage does not install constructors.
Runtime checks exercise the executable `declareInductiveTypes` for `Bool` and
`Nat`, including duplicate-name and primitive-authorization rejection, and for
two ordinary mutually declared headers in safe and unsafe modes. The same cases
also exercise the checked type-and-registration composition. Additional checked
cases verify automatically computed index counts, shared parameters, dependent
indices, and universe parameters in safe and unsafe modes. Rejection cases cover
missing/mismatched parameters, mismatched result universes, undeclared universes,
invalid types, and exhausted inductive fuel. These checks total thirty-six
executable outcomes and include within-batch duplicates and existing-header
collisions. A deliberately short
`nindices` array demonstrates why the refinement's exact-length precondition
matters: the unchecked prefix's `zipWith` truncates the batch. This test
deliberately bypasses the preceding stage's statistics-length assertions; it is
a precondition-boundary regression, not a kernel discrepancy. Seven abstract
header-theorem audits exclude `sorryAx` and implementation-interface
axioms; seven translation/refinement audits track their inherited assumptions.
The abstract extension, lookup, equation-preservation, and orderedness proofs
use only `propext` and `Quot.sound`; the header-well-formedness proofs use only
`propext`. `PrimitiveInductiveDecl.toVDecl` additionally inherits
`Classical.choice` and `sorryAx` through the existing structural-translation
API (`TrExprS` includes the admitted `TrProj` specification).
`checkPrimitiveInductive.toVDecl` also inherits the three equality interface
assumptions of the validator classification. No new axiom or admitted proof
is added, and these bridges do not claim unconditional inductive soundness.
Focused executable replay checks 21 declarations in `Theory.InductiveHeaders`
and nine in `Verify.Inductive`, assuming their imported dependencies are correct.

The header-extraction lemma inherits the structural-translation API's
`sorryAx` and standard logical axioms. The executable `refines` and `ordered`
proofs additionally inherit the existing persistent-map interface assumptions
`Lean.PersistentHashMap.findAux_isSome`,
`Lean.PersistentHashMap.WF.find?_eq`, and
`Lean.PersistentHashMap.WF.toList'_insert`. The audits allow only these known
dependencies. No new axiom, admitted proof body, or full-environment translation
constructor is introduced by the registration refinement.
The two checked-prefix composition theorems inherit exactly the same known
dependencies as the standalone executable header refinement; their audits do
not introduce additional assumptions. No claim is made that concrete header
checking establishes the supplied structural translations or abstract typing.
Focused executable replay checks 18 declarations in `Verify.InductiveHeaders`,
assuming its imported dependencies are correct.

`tests/InductiveStats.lean` contains sixteen proof regressions and ten axiom audits
for the paired header-array lengths, fixed callback-context fields, and parameter
distinctness. Twenty-one executable acceptance cases cover
empty, singleton, and mutual batches; safe and unsafe contexts; parameters;
dependent indices; distinct index counts; three dependent parameters with mixed
binder annotations; and universe parameters. Six rejection
cases cover missing or mismatched parameters, mismatched result universes,
undeclared universes, invalid types, and exhausted inductive fuel. The size/frame
theorems use only `propext`, `Quot.sound`, and `Classical.choice`; their audits
exclude `sorryAx` and all implementation-interface axioms.
The proof tracks parameter and universe counts internally to justify the terminal
assertions for nonempty batches. Its empty-batch case also accounts for the
kernel-level default value of a failed parameter-count assertion; the size
invariant does not claim that malformed empty input succeeds at runtime or that
every assertion is unreachable. No executable behavior changes.
All acceptance cases observe the callback context: they check preserved fixed
fields, existing `Nat` header metadata, absence of newly registered datatype
headers, and the expected changes to local-context size and fresh-name state.
Seeded cases additionally exercise a nonempty starting local context, a distinct
name-generator prefix and nonzero starting index, enabled primitive authorization,
universe parameters,
and nondefault values for every fuel field. The environment frame theorem proves
full environment equality; the runtime lookup checks are regressions, not its
proof.
Every accepted statistics fixture additionally checks parameter uniqueness and
the exact introduction names/order, including reuse across mutual declarations.
Focused executable replay checks 65 declarations in `Verify.InductiveStats`,
assuming its imported dependencies are correct.

`tests/ConstructorHeaders.lean` contains fourteen proof regressions and eight
axiom audits. The five abstract constructor-header theorem audits exclude
`sorryAx` and interface axioms, using only `propext` and `Quot.sound`.
`TrConstructor.mono` inherits the structural-translation API's `sorryAx` and
standard logical axioms; executable registration additionally inherits the same
three persistent-map interface assumptions as datatype-header refinement. No
new axiom, admitted proof body, or full-environment translation constructor is
introduced. The existing single-constant equation-preservation lemma is now
public so both abstract staging modules can reuse it.
Eighteen executable outcomes include checked staging of `Bool`/`Nat`, mutual
ordinary datatypes, empty batches, and a polymorphic parameterized `Box` in safe
and unsafe modes. They check constructor types, parents, per-parent indices,
parameter/field counts, universe parameters, safety, existing-name rejection,
and absence of recursors. Further cases reject wrong return datatypes,
within-parent and cross-parent duplicates, and safe nonpositive occurrences;
the corresponding unsafe declaration is accepted as intended. These preceding
constructor-checking and numeric-metadata checks are runtime evidence, not their
semantic verification. The refinement concerns constant-map type entries only;
it does not prove the field-count assertion unreachable for malformed inputs.
Focused executable replay checks fourteen declarations in `Theory.ConstructorHeaders`
and twenty-four in `Verify.ConstructorHeaders`, assuming their imported dependencies
are correct.

`tests/ConstructorArity.lean` contains four proof regressions and twelve axiom
audits, all excluding `sorryAx`. The checked-parameter invariants use only the
standard logical axioms. The specification-level arity substitution proof uses
only `propext`; executable instantiation additionally relies on the existing
`Lean.Expr.instantiate1_eq` interface axiom. There are no new axioms or admitted
proofs. The 192 expression/offset/depth fixtures cover every expression form,
bound-variable substitution boundaries, dependent telescopes, and accumulated
binder counts. Two further boundary checks demonstrate why the theorem needs
free-variable substitutions and why raw metadata counting does not strip
annotations or reduce let expressions. The existing statistics fixtures now
check the free-variable invariant, including repeated parameter pushes in
dependent and universe-polymorphic mutual declarations. Focused replay checks
22 declarations in `Verify.ConstructorArity`, assuming imports are correct.

`tests/ConstructorParams.lean` contains seven proof regressions and thirteen axiom
audits, all excluding `sorryAx`. The core constructor-loop arity proof uses
standard logical axioms and the existing `Lean.Expr.eqv_eq` and
`Lean.Expr.instantiate1_eq` interface axioms. The guarded bridge additionally
uses the existing expression free/metavariable-flag interfaces and
`Lean.Level.hasMVar_eq`. No new axiom, admitted proof, executable checker path,
or cache is introduced. Eleven return-application fixtures check missing,
misordered, repeated, and bound-variable parameters, including index arguments.
Twenty-four inner-loop outcomes exercise zero/one/two parameters, dependent
fields, safe/unsafe checking, missing parameters, and fuel exhaustion.
Two further duplicate-parameter arity checks and one source-free-variable guard
check show why distinctness and source closedness are required: bypassing those
premises can make the inner loop accept a signature with too few raw binders.
These are deliberate helper-boundary fixtures, not evidence of full-declaration
acceptance; they never invoke constructor registration on malformed metadata.
Sixteen further checked-type/guard/inner-loop outcomes cover zero/one/two
generated parameters, dependent fields, safe/unsafe contexts, missing/swapped
parameters, open source expressions, and fuel exhaustion. The checked-parameter
arity theorem adds no interface assumptions beyond the existing guarded-loop
bridge and excludes `sorryAx`.
Focused executable replay checks 54 declarations in `Verify.ConstructorParams`,
assuming its imported dependencies are correct.

The reflection regressions accept both supported reflection encodings and reject
swapped proof converters. They also check selectors that ignore their Boolean
argument: their type-checking prefixes succeed, while their computation checks
fail. These are runtime checks against the imported prelude, not a proof of its
environment translation.
The polymorphic-conditional regressions likewise accept both reference encodings,
check that Boolean-ignoring selectors pass their type checks, and reject those
selectors at the computation checks. The condition regressions retain the
dependent-only path and additionally exercise both conditional modes together.
The full natural-number ordering and equality condition validators are also
tested: both are accepted, and replacing their decision function, Boolean
function, or proof with an invalid one is rejected.
The division regression accepts the reference implementation and rejects
constant-zero and first-argument implementations. It also checks native literal
division with low fuel, covering zero divisors, exact division, smaller dividends,
and inputs and quotients beyond machine-word sizes. Moving the proposition check
ahead of the condition validator was checked at an earlier checkpoint.
The modulo regression accepts the reference validator and rejects constant-zero
and first-argument implementations. It checks restored native modulo with low
fuel, covering zero divisors, exact division, smaller dividends, and dividends
and divisors beyond machine-word sizes. It additionally evaluates the nested entry
template on nine small input pairs, covering zero divisors, recursive calls,
equal dividends/divisors, and oversized divisors. The same inputs check that
substitution into the open entry body produces the tested template. Four
additional source-only checks exercise substitution into the recursive body;
their placeholder proof terms are not asserted to be well-typed.
The GCD/bitwise regression checks both reference validators, rejects three
incorrect implementations for each, evaluates eight GCD input pairs, and
evaluates forty bitwise cases using AND, OR, XOR, and constant-false/constant-true
Boolean functions. The bitwise inputs include values beyond machine-word sizes.
These tests exercise unfolding, not the still-disabled native reductions.

`#print axioms` reports only `propext` and `Quot.sound` for
`Lean4Lean.VEnv.NatAddSpec.eval`, `.reflects`, `Lean4Lean.VEnv.NatMulSpec.eval`,
`Lean4Lean.VEnv.NatPowSpec.eval`, `Lean4Lean.VEnv.NatPredSpec.eval`, and
`Lean4Lean.VEnv.NatSubSpec.eval`, as well as `Lean4Lean.VEnv.NatBeqSpec.eval` and
`Lean4Lean.VEnv.NatBleSpec.eval`, `Lean4Lean.VEnv.NatShiftLeftSpec.eval`, and
`Lean4Lean.VEnv.NatShiftRightSpec.eval`. The shared
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
`Reflection.NatDITEInstance.eval` uses only `propext` and `Quot.sound`.
`Reflection.natDITE_witness` and `Condition.ReflectedNatNatChecked.apply`
inherit `sorryAx`; `.natBle_apply` also inherits the existing persistent-map
and array interface axioms. `checkNatDivCondition.WF` inherits the verification
stack's axioms.
`Condition.ReflectedNatNatChecked.natDITE_translate` and `.natDITE_eval`
depend on `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`;
no new axioms or admitted proofs were added for the conditional bridge.
`natDivLoopType.apply` uses only `propext`, and
`Reflection.NatDITEInstance.branchProof_type` uses only `propext` and `Quot.sound`.
The branch-type recovery proof inherits `sorryAx` and standard logical axioms;
the literal-selection and zero-branch proofs additionally inherit the existing
persistent-map/array interface axioms. `checkNatDivLoop.WF` and
`checkNatDivPrefix.WF` inherit the checker stack's axioms, including `sorryAx`.
The generalized source-input selection and branch reduction lemmas, and the
division entry lemmas `.natDiv_start` and `.natDiv_zero`, inherit `sorryAx`
and the existing map/array interface axioms. `tr_natDivLoopApp` uses the standard
logical axioms and inherited `sorryAx`; it does not introduce a new assumption.
`natDivLoopExpr.proofIrrel` uses only `propext` and `Quot.sound`, and
`natDivEntryBody.instantiate_literals` uses only `propext`. The source
instantiation bridge `natDivEntryBody.at_literals` inherits `sorryAx` from the
existing structural-translation API. `.natDiv_step` additionally uses the existing
map/array interface axioms, and `checkNatDivEntry.WF` inherits the checker stack's
axioms. No new axioms or admitted proofs were introduced at this checkpoint.
`NatDivSpec.ofEntry` and `natDivLoopBody.instantiate_fvars` use only `propext`;
`natDivLoopBody.instantiate_literals` uses the standard logical axioms without
`sorryAx`. The recursive translation instantiation inherits `sorryAx` from the
existing structural API. The reflected-witness, entry-contract, and loop-contract
bridges inherit `sorryAx` and the existing map/array interface axioms;
`checkNatDivEntry.spec` also inherits the checker-interface axioms. No new
assumptions were added for these contracts.
`checkNatDivRecursion.WF`, `checkNatDivEquations.WF`,
`checkPrimitiveDef_natDiv.WF`, and `.extension` inherit `sorryAx` and the existing
checker-interface axioms. The new division reflection and type fields are
established by the extension proof; no new axiom or admitted proof was added.
`checkPrimitiveDef_natShiftRight.WF` and `.extension` likewise inherit the
verification stack's `sorryAx` and implementation-interface axioms. Right-shift
reflection is established from the checked equations and the old environment's
division reflection; no new axiom or admitted proof was added.
`NatModLoopSpec.eval` and `NatModSpec.eval` use `propext`, `Classical.choice`,
and `Quot.sound`, without `sorryAx`. `Reflection.iteBranch.eval`,
`Reflection.ITESpec.apply`, and `.eval` use only `propext` and `Quot.sound`;
`Reflection.checkITE_eq` additionally uses `Classical.choice`.
`Reflection.checkITE.WF` and `Condition.natLE.checkITE.WF` inherit the checker
stack's `sorryAx` and implementation-interface axioms. `Reflection.ite_witness`
inherits `sorryAx` and the standard logical axioms, without additional
implementation-interface axioms. No new axioms or admitted proofs were added.
`Reflection.ITEInstance.eval` uses only `propext` and `Quot.sound`.
`Reflection.ite_carrier` and the polymorphic instantiation, branch-type recovery,
translation, and evaluation bridges inherit `sorryAx` and the standard logical
axioms. The literal-ordering specialization, closed-false-branch reduction,
and modulo entry/recursion bridges additionally inherit the existing
persistent-map/array interface axioms. No new assumptions were added for them.
`NatModSpec.ofEntry`, both modulo free-variable substitution lemmas, and
`natModEntryBody.instantiate_literals` use only `propext`;
`natModLoopBody.instantiate_literals` additionally uses `Classical.choice` and
`Quot.sound`, without `sorryAx`. Both `.at_literals` bridges inherit `sorryAx`
from the structural-translation API; both `.spec` bridges additionally inherit
the existing map/array interface axioms. No new axiom or admitted proof was added.
`checkNatModRecursion.WF`, `checkNatModEquations.WF`,
`checkPrimitiveDef_natMod.WF`, and `.extension` inherit the verification stack's
`sorryAx` and implementation-interface axioms. The modulo invariant is supplied
by the extension proof, not assumed for the new declaration. The unchanged
division-recursion statement now uses the same private extraction helper.
`NatGcdSpec.mono` uses only `propext`. `NatGcdSpec.eval`, `.reflects`,
`NatBitwiseSpec.eval`, and `.reflects` use only `propext` and `Quot.sound`, without
`sorryAx`. Their computation equations remain explicit premises; they are not
added as assumptions to the environment invariant.
The level soundness theorems
`Lean.Level.normalizeCore_eval`, `geq'_wf`, and `isEquiv'_wf` use the standard
logical axioms and the existing `Lean.Level.instLawfulBEqLevel` interface axiom,
without `sorryAx`. The frontend audit includes `sorryAx` and the existing
implementation-interface axioms, as noted above.

AI assistance: drafted and iterated with OpenAI Codex, compiled and tested
locally. Not yet human-reviewed. No PR or Zulip message has been submitted.
