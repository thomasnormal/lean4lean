# Non-inductive verification proof of concept

This fork is an incomplete, conditional verification checkpoint, not a proof of
all of Lean. The intended review branch is `poc-verified-noninductive`.

**2026-10-15 trust correction:** the remaining `NormalEq.parRed` contract is
false for the actual quotient reduction instance, as demonstrated by
`QuotConfluenceObstruction.counterexample`. Its transitive users therefore
depend on a known-false admitted specification, not only an open proof task.
The counterexample is independent of that theorem and all its confluence/
quotient-injectivity consequences, but still inherits the separately identified
typing/injectivity admissions. No unconditional kernel soundness follows from
the results below. See `bugs-found.md` for the full obstruction and native
Lean 4.29.0 / 4.33.0-rc2 controls.

## What is proved

- `QuotPrefixReduction` removes the preceding repair ingredient's
  saturation-only limitation. The same compatible presentation includes typed
  function eta, and `unfoldPrefix` parses the actual application spine,
  computes the residual type from `quotLiftConst`, and introduces precisely
  the missing binders before applying the existing Prop-source unfolding.
  `unfoldPrefix_complete` proves success for arbitrary lists of zero through
  six supplied arguments at any zero-equivalent source universe, not just
  fixture terms. `prefix_reduces` combines that completeness with actual source
  typing to give a real finite reduction and semantic equality at the original
  type. No canonical-type witness or preservation condition is demanded from
  the caller; the canonical residual typing is derived internally using the
  existing independent typing/injectivity baseline.
  Eta steps and all finite chains preserve weakening, typed substitution,
  and definitional context conversion;
  compatible application/lambda chains allow the generated reductions beneath
  binders and additional applications. The fixture checks all seven prefixes
  in a concrete Eq-plus-Quot model and excludes the refuted confluence theorem,
  derived quotient injectivity, and false strengthening from reachable proofs.
  Completeness, fresh-variable application typing, and concrete source typings
  are admission-free/no-choice; general reduction soundness and actual-model
  construction retain the separate `sorryAx` baseline. Native prefix and full
  function equalities use only `Quot.sound`; native selector and saturated
  unfolding equalities use no axioms. These are semantic controls, not native
  reduction-completeness claims. General simulation/Church–Rosser, eta critical
  pairs, and downstream migration remain open. The eta/prefix direction is
  already present in upstream draft PR #53.
- `QuotPropReduction` supplies a concrete repair ingredient without changing
  the existing false `NormalEq.parRed` contract. `zeroLike_iff` constructively
  characterizes all universes equivalent to zero, including noncanonical
  `max`/`imax` syntax. The total `unfold` transformer rewrites a saturated
  Prop-source `Quot.lift f h q` to `f (Quot.ind (fun _ => P) id q)`;
  `unfold_sound` preserves its original result type with only the source
  typing, actual quotient registration, context WF, and environment WF.
  `Step` adds this rule to actual parallel reduction with compatible
  application/lambda/forall closure; finite `Steps` include all existing
  parallel-reduction chains. The new step is stable under arbitrary weakening
  and typed single-variable substitution, and both step relations preserve
  semantic equality and the original type. The fixture demonstrates that the
  prior concrete obstruction joins after one new step, while the original
  obstruction remains checked and unchanged.
  `selector_hasType`, `zeroLike_iff`, and generic `Params`-level selector/join
  proofs use only `propext` and `Quot.sound`, without choice or admissions.
  Concrete-model instantiation and general source-typing inversion additionally
  inherit `sorryAx`; dependency traversal forbids the refuted confluence
  theorem, its derived quotient injectivity, and `IsDefEqU.weakN_iff`.
  This is not a confluence proof, downstream migration, native-checker fix, or
  checked inductive registration. The same selector idea is already present
  in upstream draft PR #53. Native-only controls pass on Lean 4.29.0 and
  4.33.0-rc2; they use explicit congruence for the unfolding equality.
- `QuotConfluenceObstruction.counterexample` constructs a well-formed local
  context, a `NormalEq` pair, and a concrete quotient pattern reduction for
  which no left reduction followed by `NormalEq` can simulate the right step.
  The source universe is zero, the target is `Prop`, and the neutral major and
  `Quot.mk` major are proofs of the same proposition. `.neutralReduction`
  proves that every finite left reduction stays unchanged;
  `.not_normalEq_reduced` excludes the required normal equality using the
  independent typing/injectivity baseline. `.semanticEquality` separately
  derives the endpoint conversion by actual congruence and registered quotient
  beta, without the refuted theorem. The fixture constructs an explicit
  Eq-axiom-plus-quotient semantic declaration history, rather than assuming an
  arbitrary environment or a fabricated `Params` instance. Its environment
  well-formedness proof uses only `propext` and `Quot.sound`; the full
  counterexample's exact dependency set is `propext`, `Quot.sound`, `sorryAx`.
  All 32 owned public/private/generated values are checked for direct
  admissions/new axioms and for forbidden dependence on `NormalEq.parRed`,
  `.parRedS`, `IsDefEq.church_rosser`, `IsDefEqU.quot_inj`, or
  `IsDefEqU.weakN_iff` (the separate upstream issue #50).
  `tests/NativeQuotientProofIrrelevance.lean` imports only `Lean` and reproduces
  the native proof-irrelevance/beta behavior on both toolchains; its named
  equivalents in the semantic fixture have no axioms at all. This identifies
  a false verification contract; it is not a repair of confluence or evidence
  that the native kernel accepts an invalid proof.
- `getElimLevel` is a total executable definition with an equation theorem.
  `Inductive.ElimName` implements the same first-unused `u`, `u_1`, `u_2`, …
  search using verified string append. A decimal-length bound on the finite
  input names proves termination; it is a proof-only decreasing measure, not
  runtime fuel, a fallback result, or an extra acceptance restriction.
  `freshElimName.loop.spec` proves freshness and that every preceding candidate
  is occupied, for arbitrary starting indices and arbitrary lists, including
  duplicates. `freshElimName.first` also accounts for the initial bare `u`.
  `getElimLevel.eq_map` preserves the actual `isLargeEliminator` result and
  every classifier failure. `getElimLevel.fresh` and `.recLevelParams` derive
  freshness, distinct generated recursor universe parameters, and the actual
  selected level's semantic translation without caller-supplied freshness or
  translation receipts. The new proof/definition values depend only on
  `propext`, `Classical.choice`, and `Quot.sound`, with no inherited admission
  or new interface axiom. The original `Name.appendIndexAfter` uses opaque
  `String.Internal.append`, so equality to that old helper is runtime-tested,
  not asserted as a proved native-interface equation. The verified candidate
  definition explicitly constructs the same decimal `u_` spelling.
  `tests/InductiveEliminationLevel.lean` audits all 44 owned declarations and
  exercises 2378 collision/order/duplicate/noise controls, 2145 comparisons to
  the former native renderer, 100 actual empty/unit/data/proof/indexed
  declaration runs and their generated recursors, 120 classifier/selection
  controls, and classifier fuel-failure propagation. This closes the selector's
  partial-definition gap, not semantic large elimination, `AddInduct`, checked
  recursor registration, positivity, or the frontend's inherited admissions.
- `IsDefEqStrong.substEq'` and `.subst` prove simultaneous substitution by a
  pointwise definitionally equal pair of substitutions, with the left/right/cross
  bundle covering every actual strong typing constructor. `IsDefEq.substDF`
  transfers the result to the weak judgment; ordinary equality, typing, untyped
  equality, and type judgments have diagonal substitution corollaries.
  `Ctx.SubstEq` certifies each source binder's domain and corresponding target
  values, supports identity, lookup, weakening, and lifting under equal domains,
  and allows arbitrary substitutions outside the empty source context.
  This is a targeted port of official upstream's `6ba54db`/`8223d22` proof API,
  adapted to this branch without migrating its toolchain or executable.
  `tests/StrongSubstitution.lean` audits the owned helper/context/semantic proofs
  with no inherited admissions or new interface axioms; their dependency union
  is `[propext, Quot.sound]`. It covers arbitrary related substitutions, actual
  variable substitution with syntactically distinct equal values, binder lifting,
  identity, and beta. This removes a missing semantic API, not the frontend's
  existing inherited `sorryAx`, the remaining confluence admission, or any of
  the inductive/recursor registration obligations.
- `Pattern.Equation` represents guarded registered pattern reductions under
  lambda binders. `Pattern.Equation.of_root` preserves the old root-pattern
  certificate, while `Pattern.Equation.parRed` derives the corresponding actual
  parallel reduction without using admitted confluence. `Params.extra_pat`
  now accepts these certificates and the real `IsDefEq.church_rosser` extra-rule
  case consumes them. `quotDefEq.not_matches` proves that the former root-only
  premise excluded the actual six-lambda quotient equation at every universe
  instance. `Theory.Typing.QuotPattern` supplies its simple quotient-lift pattern,
  parameter-equality guards, result expression, and an admission-free certificate
  deriving those guards from the equation's bound variables. The fixture audits
  the structural proofs, legacy compatibility, and reduction-bridge dependencies.
  This repairs the closed-equation representation; subsequent work also proves
  checked quotient rule soundness and constructs the concrete definition/quotient
  `Params` model described below. Quotient-type injectivity and semantic
  arbitrary-parameter alignment are now proved using that model and the existing
  confluence theorem. The native quotient callback/dispatcher contracts are also
  proved below; the inherited confluence and typing admissions remain open.
- `Theory.Typing.RewriteRules` derives the complete classification and constant
  lookup of registered equations, uniqueness of definition origins by name, and
  exclusion of definitions at all four registered quotient primitive names from
  the WF declaration history. `RewriteRule` contains exactly registered closed
  definition rules and the checked quotient rule; its soundness and equation
  coverage are proved, including the actual closed quotient equation.
  `Theory.Typing.ConcreteReduction` proves all overlap/major-premise obligations
  and supplies `VEnv.WF.reductionParams` at every universe count. It constructs
  the actual model instead of requiring a caller's `Params` premise.
  `Params.pat_wf` now receives local-context WF explicitly, matching the proved
  typing APIs; `ParRed.defeq` forwards its existing certificate at both uses.
  The public parallel-reduction and confluence theorem statements do not change.
  `ConcreteReduction` checks metadata, primitive-name masking negatives, equation
  coverage, actual parallel reduction/subject conversion, and instantiation of
  the unchanged confluence consumer. Its exhaustive proof/dependency audit
  excludes circular reliance on the rule-soundness projection or confluence
  consumers. Metadata, equation coverage and non-overlap use only `propext` and
  `Quot.sound`; the whole model additionally inherits the existing `sorryAx`
  dependency through rule soundness, but no choice or new interface axiom.
  The generic `NormalEq.parRed` application/extra contract is now refuted; model
  construction does not remove it or prove full native recursor semantics.
- `NormalEq.parRed_constDF` proves the constant case of parallel reduction
  modulo universe conversion, including registered extra-reduction rules and
  their nontrivial equality checks. `EqUpToLevels.instL_of_levels` and
  `Pattern.RHS.eqUpToLevels_const` derive structural universe transport without
  inherited metatheory admissions; `NormalEq.of_eqUpToLevels` and
  `Pattern.Check.OK.const_levels` supply the semantic transports. The actual
  `NormalEq.parRed` proof now uses the proved constant case instead of its
  former admission. `ConfluenceConstantReduction` checks both constant and
  extra branches, transported equality guards, proof dependencies, and the
  absence of circular dependence on the still-admitted application/extra case.
  Semantic transports retain the existing typing/model dependencies. This
  removes one admission, not the remaining confluence, injectivity, quotient
  callback, or inductive registration obligations.
- `TypeChecker.Inner.whnfCore'.headWF` and `whnf'.headWF` prove a native
  head/cache invariant through the actual normalizer workers: successful
  outputs have neither a metadata nor a let-expression as the outermost node,
  and both WHNF caches retain that property. The proof includes the actual
  beta worker, local-let lookup, projection helper, all native natural-number
  reducers, delta-unfold cache updates, full-WHNF fuel loop and final cache
  insertion. Native reductions are proved to return no successful reduction
  rather than assuming an arbitrary native result has a clean head.
  `HeadCacheWF.empty` supplies the cold initial cache invariant, and clean
  core/full insertions preserve it. The worker theorems still require the
  normalization callbacks' native `Methods.HeadWF` contract; the generic
  worker interfaces also take an explicit recursor-helper cache frame, now
  discharged by the actual helper proofs below. The actual arbitrary-fuel
  callback contract is now proved by the four-method induction below.
  This necessary syntactic property does not establish semantic WHNF
  completeness, exclude local-let free-variable heads, or discharge accepted
  recursor parameter/index traversal and terminal-sort obligations. The
  existing conversion-only `Methods.WF` is not silently strengthened.
  `tests/WHNFHeadShape.lean` audits every owned declaration without inherited
  checker/metatheory admissions; cache-insertion proofs retain exactly the
  existing native representation assumptions `Lean.Expr.eqv_eq`,
  `Lean.Level.instLawfulBEqLevel` and `Lean.Syntax.structEq_eq`, in addition to
  the three logical foundations. The fixture exercises actual cold/warm workers,
  both safeties/eager modes and all cheap flags. Poisoned-cache negative
  controls demonstrate why the initial cache invariant is necessary; these
  deliberately invalid states are not kernel discrepancies or positive
  checker receipts.
- `TypeChecker.Inner.reduceRecursor.headWF` proves the actual quotient and
  inductive reduction helpers preserve both clean WHNF caches under the four
  native callback contracts. The proof covers actual `isDefEq` equivalence
  updates, both quotient eliminators, K adaptation (including its pure
  metavariable-index scan), structure/Prop guards, major normalization,
  literal constructor adaptation, rule lookup and assembly, and cheap-recursion
  normalization selection. No semantic header/model alignment or separate
  recursor-result cache/head premise is supplied by callers. Consequently
  `whnfCore'.headWFOfMethods` and `whnf'.headWFOfMethods` remove the separate
  helper-frame premise from the actual-worker head/cache results.
  `Methods.withFuel.zero_headWF` proves the actual throwing zero-fuel base
  contract; `whnfCore_succ_headWF` and `whnf_succ_headWF` supply the two real
  normalizer successor steps from the prior-fuel four-method contract.
  The comparison worker frame and full `Methods.withFuel.HeadWF` induction
  are supplied below. This closes native reduction-helper
  cache framing, not semantic normalization completeness or frontend closure.
  `tests/RecursorHeadFrame.lean` audits every owned declaration against the
  unchanged logical/native representation foundations and uses actual typed
  Nat/K/structure/Prop/string/quotient terms with real methods, both safeties,
  eager modes, cheap flags, cold/warm caches and full-reduction endpoints.
- `TypeChecker.Inner.inferType'.headWF` proves both clean WHNF caches survive
  the actual inference worker, including inference-cache hits and insertions,
  literal/constant/universe checks, recursive metadata and projections,
  lambda/forall/let telescopes and fresh local scopes, infer-only application
  loops, checked applications and the eager-reduction reader override.
  Its bound-variable fallback is framed at the actual native pure default,
  without adding a bound-variable representation axiom to the audit allowlist.
  Projection framing reuses the proved equality with the actual projection
  program, including parameter/field loops and dependent/Prop guards, rather
  than supplying projection eligibility or a shadow checker receipt.
  `Methods.withFuel.inferType_succ_headWF` is the third real successor step
  under the prior-fuel four-method contract. The comparison successor step and
  full arbitrary-fuel induction are now supplied below; the
  inference theorem asserts cache preservation, not semantic type correctness
  or inductive frontend closure. `tests/InferenceHeadFrame.lean` exhaustively
  audits the module's declarations against the unchanged foundation allowlist
  and exercises actual cold/warm inference/checking with expected types,
  local/let scopes, dependent/Prop projections, malformed/error guards and
  poisoned-cache precondition controls.
- `TypeChecker.Inner.isDefEqCore'.headWF` proves the actual comparison worker
  preserves both clean WHNF caches. It covers binder/argument comparison,
  the actual equivalence probe and failure-cache updates, lambda/structure
  eta, proof irrelevance, unit-like and string guards, offsets, projection
  unfolding, every lazy-delta plan and its bounded rounds, both native/Nat
  reduction tails, cheap/full normalization and all comparison fallbacks.
  Existing exact implementing-program equalities expose these paths; no
  metadata alignment, semantic eligibility or separate helper-frame receipt
  is required. `Methods.withFuel.isDefEqCore_succ_headWF` supplies the fourth
  successor step, and `Methods.withFuel.headWF` proves the complete native
  four-method cache/head contract for every fuel, with no callback premise.
  `RecM.run_headWF` lifts this to the actual configured public normalization,
  inference/checking and comparison entries. Successful normalizations have
  no metadata/let outer node and every successful entry preserves initially
  clean WHNF caches. This is partial correctness: zero/exhausted budgets may
  throw and warm-state entry framing still requires initial cache cleanliness.
  `M.HeadWF.fromEmpty` and `M.HeadWF.run` discharge initialization for the
  actual cold `M.run` API, giving its successful normalizations clean heads
  without a caller-supplied cache or callback contract. Semantic WHNF
  completeness, inference/comparison soundness and inductive frontend closure
  are not established by this syntactic/cache invariant. The audit retains
  exactly the existing six logical/native representation foundations, with
  no inherited checker/metatheory admissions. `tests/ComparisonHeadFrame.lean`
  audits every owned declaration and exercises actual typed bidirectional
  comparisons, all configured entries, cold/warm states, real proof/eta/unit
  helpers, resource failures and poisoned-cache preconditions.
- `NativeHeadScoped` strengthens the native head condition by excluding a
  free-variable head that names a local let. `HeadScopeCacheWF` imposes it on
  both WHNF caches, while `HeadCacheNamesWF` reserves cached values' free
  variables against the actual fresh-name generator. `NativeLocalNamesWF`
  and native local-context well-formedness discharge allocation freshness.
  `withLocalDecl.headScopeWF` and `withLetDecl.headScopeWF` prove the actual
  allocation, extended-reader entry, generator advancement and restored-reader
  exit frames. Fresh local entry does not need cached-name reservation; fresh
  let entry does. Both exit frames allow arbitrary new cache entries satisfying
  the extended-context invariant. Pure actions, exceptions, composition and
  actual `withFreshId` have the corresponding native cache-scope frames.
  Native core/full cache insertion preserves both scoped-head and reserved-name
  invariants when the inserted value satisfies them. Scope lookup/allocation
  proofs retain the three pre-existing container interfaces
  `Lean.PersistentHashMap.WF.find?_eq`,
  `Lean.PersistentHashMap.WF.toList'_insert` and
  `Lean.PersistentArray.toList'_push`; cache insertion/empty proofs retain the
  existing expression/level/syntax representation assumptions. No owned
  axiom or inherited checker/metatheory admission occurs in the exhaustive audit.
  These are independently audited prerequisites, not an arbitrary-fuel proof
  that normalization/inference/comparison preserve the stronger invariant.
  They do not establish semantic WHNF completeness or terminal-sort acceptance;
  the stronger worker/fuel induction and semantic head obligations remain open.
  `tests/HeadScope.lean` exercises actual cold/warm normalization across fresh
  local/let scopes and invalid reservation/shadowing preconditions; those
  invalid states are not kernel discrepancies.
- `TypeChecker.Inner.whnfCore'.scopeWF` and `whnf'.scopeWF` carry the stronger
  scoped-head cache invariant through the actual core/full normalizer workers
  together with the existing semantic state, conversion and free-variable
  contracts. Successful heads are neither metadata nor let expressions nor
  free variables naming local lets. The proofs cover native metadata stripping,
  local-let lookup, cached results, multi-lambda beta consumption, rebuilt
  application spines, projection/string expansion, natural-number reducers,
  native-reduction rejection, delta unfolding, fuel loops and core/full cache
  insertion. Existing `VState.WF` supplies both cache-value and local-name
  reservation; these are not fresh independent caller assumptions. Native
  delta helpers preserve the actual scoped caches and name generator.
  `Methods.ScopeWF` retains the original semantic contract and adds scoped
  cache preservation at its typed four-method boundaries. Its actual zero-fuel
  instance is proved; the stronger arbitrary-fuel induction is now supplied by
  `ScopedMethods` below. The inference dispatcher and comparison worker frames
  consume those derived scoped callbacks. The recursor cache frame is proved
  below, and neither normalizer worker requires an independent recursor-frame
  premise.
  These model-aware proofs inherit the pre-existing checker/metatheory and
  representation dependencies of `whnf'.WF`; the separate native scope module
  remains audited without checker/metatheory admissions. No new admission or
  axiom is added. Neither the scoped-head invariant nor conversion preservation
  establishes semantic WHNF completeness or terminal-sort acceptance.
- `TrEnv'.recursorLookupRejected`, `TrEnv.recursorLookupRejected`, and
  `TrEnv.recursorNotInModel` extend the existing inductive-header exclusion to
  recursor records by sharing a single inductive-family lookup invariant. The
  invariant covers ordinary declarations, quotient registration, ignored unsafe
  records, and the constructor-free `AddInduct` case. It does not prohibit native
  recursor records: a fixture constructs a satisfiable ignored unsafe recursor.
  `inductiveReduceRec.eq_none` derives the actual inductive reducer's `none`
  result for any translated expression and arbitrary monadic callbacks, before
  any major normalization, K/structure conversion, or rule expansion can run.
  `quotReduceRec.scopeFrame` extracts the consumed major argument's translation
  from the application stack and scopes the actual quotient normalization
  callback. `Inner.reduceRecursor.scopeFrame` combines that frame with inductive
  rejection for both quotient-initialization states and all cheap flags.
  Consequently `whnfCore'.scopeWF` and `whnf'.scopeWF` no longer require a separate
  recursor cache-frame hypothesis. Their semantic reduction dependencies remain
  explicit; `reduceRecursor.WF` now has the proof described below. No new
  admission or stronger caller premise is added. Checked inductive registration
  will require replacing this fragment-specific rejection with actual recursor
  semantics. Arbitrary-fuel scoped comparison/method closure is proved below;
  the frontend theorem remains open. The scoped WHNF fixture audits 166 owned
  declarations
  without direct admissions or axioms and runs 896 actual core and 896 actual
  full cold/warm scoped-cache controls, including quotient lift/induction, plus
  32 string projection controls. Its quotient lift control independently
  distinguishes the encoded numeral retained by core reduction from the native
  literal produced by full normalization.
- `quotReduceRec.fvarsBelow` proves the structural free-variable preservation
  of both quotient lift and quotient induction reductions. It follows the
  actual constructor-normalization callback, rejects malformed constructor
  heads, and preserves the optional trailing application range. This is a
  separate partial-correctness component, now combined with the semantic
  `TrExpr` result in `quotReduceRec.WF` and the original dispatcher contract.
- `VContext.quotientDefEq` turns the registered quotient beta equation into
  a verified semantic `IsDefEqU` relation whenever the native environment has
  completed quotient initialization. The theorem is the base equality for
  the still-open instantiated quotient reduction proof; it does not by itself
  prove the callback's translated result.
- `Theory.Typing.QuotReduction` proves `VEnv.quotLift_beta` at arbitrary
  well-formed universe instances and local contexts by instantiating the
  registered equation through its six binders. `VEnv.quotMk_hasType` derives
  constructor typing from the registered constant; `VEnv.quotInd_beta` derives
  proposition-valued induction reduction by typing both sides and applying
  proof irrelevance. The constructor and induction proofs do not depend on
  metatheory admissions or choice; lift retains the existing unique-typing
  dependencies. `QuotientReductionSemantics` checks initialized verified
  contexts, typed trailing application transport, exhaustive module-owned
  proof/dependency audits, and actual cold/warm quotient helper and dispatch
  controls. `Theory.Typing.QuotReductionAlignment` proves `VEnv.quotMk_congr`
  for convertible constructor universes, parameters and payloads, and extends
  both semantic beta rules to a convertible major argument. Induction transports
  its result to the original dependent motive rather than leaving the canonical
  motive as a caller restriction. `QuotientReductionAlignment` checks these
  contracts in arbitrary initialized verified contexts and exhaustively audits
  owned declarations against the existing unique-typing dependencies.
  `VEnv.quotMk_inv` now recovers the singleton universe instance, domain type,
  relation type, payload type, and conversion of an arbitrary result type from
  constructor application typing alone. `VContext.quotMkArguments` carries this
  inversion through the actual native constructor translation while preserving
  translations of all three original arguments. `VContext.quotMkPayload` turns
  the reducer's actual `isAppOfArity` guard into a typed translation of its
  extracted `appArg!` payload, including after the verified WHNF callback.
  These inversion proofs inherit
  the existing unique-typing admissions; they do not change the admission-free
  dependency bounds of `quotMk_hasType` or `quotInd_beta`.
  `QuotientConstructorInversion` checks arbitrary result types and local contexts,
  rejects incorrect universe arities, checks a constructor typing/inversion
  round trip, and audits all four new proofs against the existing unique-typing
  and initialized-context dependency baselines.
  `VEnv.quotLift_inv` and `VEnv.quotInd_inv` likewise derive universe arity,
  well-formedness and all argument typings from an arbitrary typed eliminator
  application, not from caller-supplied argument typing premises. This includes
  the exact respect-proof or dependent-minor type, the major's quotient type,
  and conversion of the arbitrary result type to the lift target or the motive
  applied to the original induction major. `VContext.quotLiftArguments` and
  `VContext.quotIndArguments` preserve translations of all original native
  arguments with these derived typings. `QuotientEliminatorInversion` checks
  both semantic contracts, incorrect semantic/native universe arities,
  beta-typing/inversion round trips, and composition of the recovered major
  translation with verified WHNF and constructor payload extraction. It audits
  all four new proofs against the existing unique-typing and initialized-context
  dependency baselines. The semantic proofs inherit `sorryAx` through unique
  typing; the native bridges additionally inherit choice and the existing
  persistent-map/array interface axioms. No direct admission or new axiom is
  introduced, and `quotMk_hasType`/`quotInd_beta` retain their admission-free bounds.
  `Theory.Typing.QuotPatternSoundness` now proves `quotLiftPattern.sound`:
  the actual pattern match, source application typing, and the pattern's actual
  domain/relation checks imply semantic reduction at the original supplied
  result type. `VEnv.quotLift_beta_of_checkedParameters` derives all argument
  typings, both universe arities and their required equivalence, and payload
  transport before applying the semantic beta rule. It does not assume universe
  equivalence or any argument typing. `VEnv.WF.quotientObjects` recovers primitive
  quotient signatures from registration of the actual quotient equation by
  induction on the well-formed declaration history; its dependencies are only
  `propext` and `Quot.sound`. The semantic rule proofs retain the existing
  unique-typing/sort-injectivity `sorryAx` dependency but do not assume a `Params`
  instance or confluence. `QuotientPatternSoundness` checks arbitrary convertible
  parameters and result types, both actual checks (with mismatch rejection),
  concrete pattern construction, use in initialized verified contexts, all owned
  proof dependencies, and absence of circular dependence on `Params.pat_wf` or
  the confluence consumers. This proves the quotient rule's semantic-soundness
  obligation used by the concrete rewrite model above, not full confluence. The native
  reducer does not perform these semantic checks; deriving them automatically
  from major typing and discharging the remaining confluence obligations are
  still necessary. No runtime restriction is added to evade those obligations.
  `Theory.Typing.QuotInjectivity` now derives universe-list equivalence and
  domain/relation definitional equality from arbitrary quotient-type equality.
  The concrete model preserves the registered `Quot` head through parallel
  reduction and its reflexive/transitive closure. Normal equality inversion
  excludes every proof-irrelevance branch by proving that a telescope ending
  in a sort cannot itself be a proposition; applications are not assumed to be
  generally injective. Actual quotient-equation registration protects the head
  from user definitions; a matching constant signature alone is not assumed
  to identify a primitive. `VEnv.quot_inv` also recovers the primitive universe
  arity and argument typings from an arbitrary typed quotient application.
  `Theory.Typing.QuotReductionAutomatic` proves both `quotLift_beta_of_typed`
  and `quotInd_beta_of_typed` at the original arbitrary result type without
  caller-supplied parameter checks, universe equalities or argument typings.
  Their `of_normalizedMajor` variants accept a major convertible to an arbitrary
  constructor spine, including differently expressed constructor parameters.
  `QuotientInjectivity` checks all these contracts, multistep spine preservation,
  incorrect universe arities, unequal-universe impossibility, and beta-converted
  domains. Its exhaustive audit rejects direct admissions and new axioms,
  preserves the admission-free bounds of `quotMk_hasType`/`quotInd_beta`, and
  explicitly traverses the inherited confluence and sort-injectivity dependencies.
  Structural and normal-equality inversion use only `propext`, `Quot.sound`,
  and inherited `sorryAx`; full injectivity and automatic beta additionally
  inherit `Classical.choice` from the existing confluence theorem. No admission
  is removed by that application of confluence, and its remaining
  `NormalEq.parRed` application/extra admission is not hidden or reproved here.
  `VContext.quotLiftReduction` and `quotIndReduction` now transport the actual
  normalized constructor payload back to the original native eliminator's
  semantic translation. They use the WHNF callback's real `TrExpr` result,
  preserve translations of the original function/minor and extracted payload,
  and derive parameter alignment rather than imposing checks absent from the
  executable. The actual application stack supplies saturated source typing;
  the reapplication proof handles arbitrary trailing arguments and both the
  empty/nonempty suffix branches of `mkAppRange`.
  `quotReduceRec.trExpr` verifies the actual worker against arbitrary valid
  methods, including every name, saturation and constructor-shape guard.
  `quotReduceRec.WF` combines that semantic result with the existing
  free-variable invariant. The original, unrestricted `reduceRecursor.WF`
  contract is now proved by composing initialized quotient reduction with the
  constructor-free inductive rejection branch, for both initialization states
  and every cheap-recursion/projection flag. Its former direct admission is
  removed without changing a theorem premise or executable behavior.
  `NativeQuotientReduction` checks callback composition, the worker and original
  dispatcher contracts, arbitrary explicit fuel and `RecM.run`; it audits all
  new public/private/generated proof values against independent typing,
  confluence, registration and native-interface baselines. A dependency traversal
  excludes circular use of the normalizer implementations or `Methods.withFuel.WF`
  in their own recursor proof. The result still inherits `sorryAx`, choice and
  existing expression-range/persistent-map/array interface axioms. It does not
  prove genuine inductive recursor semantics or close the remaining confluence
  and foundational typing admissions, and the constructor-free `TrEnv` boundary
  is unchanged.
  The existing beta/alignment theorem contracts stay unchanged. The native
  fixture includes actual proposition-induction reduction with an explicit
  motive, not a claim that native reduction erases the induction application.
- `Environment.checkPrimitiveInductive.toVDecl_WF` packages the checked
  primitive-inductive success result with its existing Bool/Nat declaration,
  header-well-formedness, and `TrInductDecl` translation receipt. This is a
  checked-inductive frontend boundary only; it does not admit general
  `addInductive` registration or alter the unsupported inductive branch of
  `addDeclVerified`.
- `addDecl.WF_noninductive` proves the actual checked `addDecl` frontend for
  every non-inductive declaration, including its original unchecked quotient
  registration worker, at arbitrary configured fuel. Its list-fold and
  empty-environment wrappers preserve the same fragment and extension relation.
  `checkEqType.no_success` derives quotient-bootstrap rejection from the current
  `TrEnv` inductive lookup exclusion; `Environment.addQuot.WF` retains the actual
  initialized quotient worker's identity result. No quotient exclusion, extra
  registration premise, or alternate frontend is imposed on callers.
  `NonInductiveDeclarationFrontend` audits these proofs against the existing
  inherited checker/model dependencies. This does not eliminate those inherited
  admissions or prove quotient bootstrap acceptance, terminal-sort completeness,
  or genuine inductive registration; the global `addDecl.WF` admission remains.
- `TypeChecker.Inner.reduceProj.none_of_translation` proves that the actual
  projection reduction helper cannot return a field in the current `TrEnv`
  fragment. Both normalization choices and string-constructor expansion retain
  a translated result; a successful constructor lookup would contradict the
  existing constructor exclusion. This replaces the `reduceProj.WF` admission
  without changing its statement or adding callback/state premises. The
  `ProjectionReductionSemantics` fixture audits both proofs against the existing
  semantic/native baseline, checks generic, arbitrary-depth real-method and
  cold-run contracts, and runs 1,536 actual cold/warm rejection controls and 128
  native constructor-field controls. Native constructor/string positives remain
  outside this fragment; invalid-cache and zero-depth controls preserve the
  original state/callback boundary. Successful checked inductive registration
  will require genuine constructor projection semantics; `TrProj` itself
  remains admitted.
- `TypeChecker.Inner.ensureSortCore.scopeWF` and
  `ensureForallCore.scopeWF` carry the scoped-head/cache invariant through the
  actual sort and forall checks, using the completed scoped WHNF contract and
  preserving the existing translated-expression and free-variable-below
  results. `Inner.inferFVar.scopeWF`, `checkLevel.scopeWF`, `envGet.scopeWF`,
  and `inferConstant.scopeWF` frame the real reader/lifted free-variable,
  universe-check, environment-lookup, and constant-inference actions with the
  existing typing/lookup theorems and unchanged caches. The focused
  `ScopedInferType` fixture checks all six contracts and audits ten owned
  declarations for theorem-backed proofs without adding an axiom. These are
  primitive inference frames. The recursive lambda and forall frames below
  consume them; the later frames also cover let telescopes, applications,
  comparison, and projection rejection in the current verified environment
  fragment. The inference dispatcher and arbitrary-fuel method scope preservation
  are now proved below.
- `Inner.isProp.scopeWF` composes the scoped inference and WHNF frames for the
  actual proposition test. On a successful proposition result it transports
  the inferred expression back to the caller's semantic translation and
  derives `HasType semantic (.sort .zero)`; the false branch closes with the
  existing trivial failure postcondition. This is a reusable native projection
  prerequisite, not a projection soundness theorem.
- `Inner.nativeProjectionFailure.scopeWF` and
  `Inner.nativeProjectionParameter.scopeWF` frame the actual projection
  failure and one parameter-step worker. The parameter frame consumes a
  translated current constructor type, preserves scoped caches through WHNF,
  and returns the yielded instantiated body without claiming its semantic
  constructor-header typing. `Inner.nativeProjectionField.scopeWF` additionally
  handles dependent body instantiation and the propositional-domain guard by
  extracting the translated forall domain and consuming `isProp.scopeWF`.
  `Inner.nativeProjectionFinal.scopeWF` handles the terminal forall-domain
  check with the same translated-domain guard. The field loop still needs
  translated types at intermediate states.
  `Inner.nativeProjectionParameters.scopeWF` now proves a translation-carrying
  parameter loop from an initial `TrExpr`, `TypedParameterArguments`, and an
  aligned native argument prefix. Its typed single-step proof transports the
  normalized forall's domain and body equalities through argument instantiation;
  the offset loop derives each intermediate translation by induction. The old
  universal per-step translation premise was vacuous (it included metavariables)
  and is removed. Concrete zero/one/two-dependent-parameter and nonzero-offset
  fixtures instantiate the replacement contract, permit unused metavariables
  outside the consumed prefix, and reject metavariable translations. The fixture
  audits both scoped inference/WHNF modules (329 owned declarations) against the
  existing semantic/native axiom baselines with no owned axioms. This does not
  close semantic constructor-header transport or the field loop. Projection
  rejection in the currently supported environment fragment is proved below.
- `VState.WF.next` advances all model cache/type invariants through the actual
  fresh-name generator transition, while `HeadScopeCacheWF.next` preserves
  scoped cache heads under the unchanged caches. `RecM.ScopeWF.withFreshId`
  then frames the real `mkFreshId`/state transition, carrying cache scope,
  model WF, generator monotonicity, and the callback's postcondition. The
  fixture now audits fourteen theorem-backed declarations without owned
  axioms. The local/let reader frames and recursive lambda inference below
  consume this fresh-state transition; the remaining recursive inference
  workers are still open.
- `VState.WF.mkLocalDecl` constructs the actual extended model state for a
  fresh local binder, including translated-context, equivalence-manager,
  cache-value and generator reservations. `RecM.ScopeWF.withLocalDecl` frames
  the real reader transition under that model, extends both scoped caches,
  invokes the callback at the fresh free variable, weakens the callback's
  final model state back to the outer context, and removes the local binder
  from both cache scopes on exit. The local-reader frame remains conditional
  on the existing translated domain/type and extended-context model; the
  corresponding let frame and recursive lambda contract are recorded below.
- `VState.WF.mkLetDecl` and `RecM.ScopeWF.withLetDecl` provide the matching
  let-binder frame, including translated value/typehood, cached-name
  reservation for the let value, extended reader/cache scope, model-state
  weakening, and cache restoration on exit. The fixture now covers both local
  and let reader frames; the recursive lambda and infer-only let contracts
  below consume the local/let frames. Checking-mode recursive let inference
  consumes the scoped comparison worker below.
- `Inner.inferType.scopeWF` exposes the original typed callback contract for
  both infer-only and checking modes, while `Inner.checkType.scopeWF` supplies
  the false-`inferOnly` specialization. These frames preserve the scoped
  caches exactly through the callback boundary and retain the original
  translation premise; they do not assert the recursive worker's semantic
  soundness or close `Methods.ScopeWF.inferType` beyond that field.
- `Inner.inferLambda.loop.scopeWF` proves scoped cache preservation and the
  existing translated typing/free-variable result for the actual recursive
  lambda telescope. It constructs the extended model at the real fresh ID,
  consumes `RecM.ScopeWF.withLocalDecl`, checks domains through the scoped
  inference/sort callbacks, and handles the body's cheap beta reduction and
  final local-context forall construction. `Inner.inferLambda.scopeWF`
  supplies the empty-telescope entry point; the fixture checks generic mode
  and two-binder checking/infer-only contracts, and exhaustively audits owned
  declarations against the existing semantic lambda/WHNF dependency baselines
  and native scope foundations. The proof inherits the existing
  semantic/metatheory admissions and requires `Methods.ScopeWF` callbacks;
  the remaining recursive inference frames and arbitrary-fuel method closure
  are proved below. Semantic WHNF completeness and the frontend theorem remain
  open.
- `Inner.inferForall.loop.scopeWF` and `Inner.inferForall.scopeWF` prove the
  corresponding scoped forall telescope. They preserve universe-list and
  sort-list witnesses, consume the local-declaration frame for each domain,
  carry the translated forall body through fresh context extension, and build
  the terminal sort typing result. The fixture covers generic mode and two-
  binder checking/infer-only contracts, while its dependency audit includes
  the existing semantic forall baseline. Recursive let/application/comparison
  frames, current-fragment projection rejection, and arbitrary-fuel methods are
  proved below; terminal frontend closure remains open.
- `Inner.inferLet.loop.scopeWF_inferOnly` and
  `Inner.inferLet.scopeWF_inferOnly` prove the actual recursive let telescope
  in infer-only mode. They consume `withLetDecl`, preserve the let-value
  translation and body free-variable frame, carry the real cached-name/fresh
  state transition, and construct the terminal forall typing result. The
  fixture checks generic and one-let contracts. The checking-mode branch is
  covered by the checking-mode contract below.
- `Inner.inferLet.loop.scopeWF` and `Inner.inferLet.scopeWF` prove the actual
  checking-mode recursive let telescope. They frame domain sorting, value
  checking, successful `isDefEq` comparison, mismatch failure, and the real
  `withLetDecl` transition before reusing the terminal forall construction.
  The comparison may advance the equivalence manager before let allocation, so
  the proof re-enters through the reached state and its fresh-name invariant.
  The fixture checks generic and one-let checking contracts. This closes the
  recursive let worker only under the existing scoped callback contracts; it
  does not itself close the remaining inference/method frames proved below,
  semantic WHNF completeness, terminal-sort acceptance, or the frontend theorem.
- `Inner.inferApp.loop.scopeWF` and `Inner.inferApp.scopeWF` prove the actual
  application-spine inference worker. They preserve the `AppStack` typing
  relation across saturated and partially saturated forall steps, consume the
  scoped forall-normalization callback, and transport the final head typing
  relation back to the original application. The fixture covers the generic
  application contract and explicitly records the pre-existing
  `Lean.Expr.instantiateRevRange_eq` representation axiom used by the source
  application reconstruction. Projection rejection in the current fragment is
  proved below; successful inductive projection semantics remain open.
- `RecM.forInList_scopeWF` and `RecM.forInRange_scopeWF` provide the reusable
  scoped cache/state frame for list and legacy-range loops, including yielded
  intermediate states. They are intended for the native projection parameter
  and field traversals, but do not themselves supply the missing semantic
  projection contract.
- `TrEnv'.inductiveLookupRejected` proves that native inductive headers in the
  current environment relation must be ignored by the selected safety mode;
  `TrEnv.inductiveNotInModel` excludes those header names from its semantic model.
  The proof covers all ordinary declaration insertions, quotient registration,
  and ignored unsafe constants, and eliminates the constructor-free `AddInduct`
  case. It does not claim that native environments contain no inductive headers:
  the fixture constructs a valid ignored unsafe header with an empty model.
  `Inner.inferProj.rejects` transports the normalized source-type translation to
  its application head and rules out the required inductive lookup before any
  parameter/field traversal. Thus `inferProj.WF` is now proved, without its former
  admission or any new premise. `RecM.ScopeWF.of_rejects` and
  `Inner.inferProj.scopeWF` close its scoped failure frame using the actual
  semantic callback contract, not the weaker native `HeadWF` theorem.
- The corrected `inferProj.WF` contract consumes the full `TrTyping` certificate
  for the structure and supplied native type, including semantic type alignment
  and native free-variable dependency preservation. It existentially returns
  the projected semantic value rather than reusing the structure value. The
  dispatcher supplies its complete inferred certificate and consumes both
  returned witnesses. The old premises left the supplied type unrelated to the
  structure's type and free-variable dependencies, and its postcondition assigned
  the field's type to the structure itself. The dedicated
  projection-contract fixture exercises ordinary, dependent, and Prop fields
  with distinct source/result types, plus a trusted-worker type mismatch that
  the full checker and native kernel reject. A definitionally equal local type
  alias demonstrates why semantic alignment alone cannot establish native
  dependency preservation; an axiom-free theorem rejects introducing a local
  variable from a closed source. Compile-time controls reject both
  the old semantic-value postcondition and unaligned typing premises. Its proof
  closes projection inference only in the currently supported `TrEnv` fragment;
  the positive native projection controls use a host environment outside that
  relation. Implementing actual checked inductive registration will invalidate
  the rejection argument and require genuine constructor-header transport and
  projection semantics. The `TrProj` specification (`Verify/Typing/Expr.lean:67`)
  and its semantic transports remain admitted; no successful inductive projection
  expansion or full frontend theorem is claimed; scoped method closure is proved
  below.
- `Inner.addEquiv.scopeWF`, `Inner.isDefEqCore.scopeWF`, and
  `Inner.isDefEq.scopeWF` preserve the scoped WHNF caches through equivalence-
  manager updates and transport successful comparison results to the semantic
  `IsDefEqU` relation. The comparison contracts reuse the existing semantic
  equivalence-manager proof and require the typed `Methods.ScopeWF` callback;
  they do not yet close arbitrary-fuel `Methods.ScopeWF`.
- `Inner.isDefEqLambda.scopeWF` and `Inner.isDefEqForall.scopeWF` prove the actual
  recursive structural-comparison telescopes, with the same aligned substitution,
  closed-value, model-context, and translated-expression premises as their
  original semantic contracts. Equal native domains reuse structural uniqueness;
  other domains consume the real scoped comparison callback and reject mismatches.
  Dependent bodies allocate the actual reached state's fresh identifier, derive
  its model-context instance, and consume `RecM.ScopeWF.withLocalDecl` to restore
  the caller's scoped caches. The unused-binder branch carries the native default
  substitution without allocating a name; a shared theorem derives its body
  translation by fresh-context transport and weakening inversion. Successful
  recursive comparisons transport back to semantic lambda/forall conversion.
  Empty-substitution entry wrappers require only the original two translations.
  `RecM.ScopeWF.toLBoolM` frames the actual Boolean-to-three-valued conversion.
  `Inner.quickIsDefEq.scopeWF` proves the real equivalence-manager lookup/update,
  cache-preserving short circuit, lambda/forall dispatch, sort equivalence,
  metadata recursion, literal comparison, untranslated metavariable exclusion,
  and undefined fallback. The equivalence-manager update leaves scoped WHNF
  caches unchanged. The dedicated fixture exhaustively audits 111 owned
  declarations for direct admissions/axioms against the existing semantic
  lambda/forall/quick-comparison/normalization and native baselines. It also checks generic
  telescope, empty-substitution, quick-comparison, and three-valued contracts,
  rejecting loose substitution values and metavariable translations. Its 480
  cold/warm bidirectional lambda/forall controls retain exact fresh-name counts
  and scoped caches; 512 quick controls retain true/false/undefined results in
  both hash modes. Domain aliases/mismatches, dependent/unused/nested binders,
  body mismatches, sorts/literals/metadata, poisoned caches, and zero-fuel
  boundaries are covered. Their `Methods.ScopeWF` callbacks are discharged for
  actual arbitrary-fuel methods by `ScopedMethods` below. Full frontend closure
  remains open.
- `TrEnv'.constructorLookupRejected`, `TrEnv.constructorLookupRejected`, and
  `TrEnv.constructorNotInModel` expose the constructor case of the existing
  inductive-family exclusion, including satisfiable ignored unsafe records.
  `VContext.constAppHeadInModel` shares the structural application-head transport.
  `Inner.tryEtaStructCore.false_of_translation` shows that structure eta cannot
  successfully return true for a translated constructor-side expression in the
  current environment relation. `Inner.isDefEqUnitLike.false_of_translation`
  transports the inferred and normalized first operand type to its application
  head and excludes the required inductive lookup. Both original semantic `WF`
  contracts are now proved, removing their two admissions without stronger caller
  premises. The shared environment-lookup fact moves from `InferType` to `Reduce`
  so both inference and comparison use the same primitive contract.
  `tryEtaStructCore.scopeFalse`, `tryEtaStructCore.scopeWF`,
  `tryEtaStruct.scopeWF`, `isDefEqUnitLike.scopeFalse`, and
  `isDefEqUnitLike.scopeWF` frame the actual early-exit workers and preserve scoped
  caches through the unit-like inference/normalization callbacks. The boundary
  fixture exhaustively audits 334 owned environment/comparison declarations with
  no direct admissions or axioms, and runs 64 actual cold/warm negative guards
  alongside 64 positive host structure-eta/unit-like controls outside the current
  `TrEnv` fragment. It checks unread metavariables, symmetric eta, zero-fuel pure
  exits, and the poisoned-cache premise. The complete scoped-comparison audit now
  includes the existing normalization baseline for the new normalized-type worker;
  its inherited lookup assumptions are not new axioms. This does not prove
  successful inductive structure eta or unit-like semantics: actual checked
  inductive registration will invalidate the rejection argument and require the
  genuine constructor/field transport. Semantic WHNF completeness
  and the full frontend theorem remain open.
- `Inner.inferType.scopeWF_of_translation` aligns the scoped inference result
  with the caller's existing semantic expression through translation uniqueness,
  retaining the complete typing/cache contract. `Inner.isDefEqArgs.scopeWF`
  follows the actual reverse argument traversal under the original explicit
  head-equality premise. `Inner.isDefEqApp.scopeWF` frames the head comparison,
  arity guard, and forward argument loop with a translated application-stack
  invariant. `Inner.tryEtaExpansionCore.scopeWF` transports the inferred,
  normalized dependent function type and the synthesized lambda, then closes the
  semantic eta conversion. `Inner.tryEtaExpansion.scopeWF` handles both
  orientations and the actual short circuit. `Inner.isDefEqProofIrrel.scopeWF`
  combines proposition inference with the compared operand types, preserving
  true/false/undefined results and both scoped WHNF caches. The auxiliary fixture
  audits all 274 declarations in scoped inference/comparison against the
  original semantic worker/native baselines without direct admissions or axioms.
  Its 512 actual cold/warm argument/application/function-eta controls and 96
  three-valued proof controls cover both safeties/eager modes, fuels 32/128,
  dependent functions, head aliases/mismatches, arity/argument mismatches,
  symmetric eta, normalized proposition aliases, zero-fuel guard/callback
  boundaries, and poisoned caches. Raw
  argument controls intentionally return true for unequal heads to keep that
  theorem premise explicit; they are not checker discrepancies. These are
  worker contracts under `Methods.ScopeWF`; the arbitrary-fuel method instance
  and actual comparison dispatcher are proved in `ScopedMethods` below.
  Semantic WHNF completeness and unrestricted frontend closure remain open.
- `Verify.TypeChecker.ScopedDelta` closes the remaining lazy-delta and string
  worker frames under the existing scoped callbacks. `M.ScopeWF.lift` frames an
  actual nonrecursive monadic action; `Inner.cacheFailure.scopeWF` updates the
  failure set without changing either scoped WHNF cache. The projection-app
  guard and Nat reducer retain their original optional-result semantic contracts.
  `Inner.lazyDeltaReductionStep.scopeWF` covers unknown/continuing/Boolean
  results, reduction-hint ordering, projection fallback, regular same-head
  argument comparison, and failed-comparison caching before unfolding.
  `Inner.isDefEqOffset.scopeWF` transports zero/successor comparisons.
  `Inner.lazyDeltaReduction.loop.scopeWF` inducts on the actual lazy-delta budget
  and transports normalized semantic operands across every continuing round;
  its successful results exclude continuation. The configured reader wrapper
  uses that theorem at its actual budget. Native reduction retains its existing
  rejection contract, not a new success assumption. Both string-expansion
  orientations preserve three-valued semantics and scoped caches. The fixture
  audits all 48 owned declarations against original semantic worker/native
  baselines without direct admissions or axioms. Its 224 typed cold/warm steps,
  576 typed terminal loop/configured reductions, 144 string/offset controls,
  16 false-string controls, and 48 projection-app guards pass. Controls cover
  both safeties/eager modes, ordinary callback fuels 32/128, explicit lazy-delta
  budgets 2/8, regular failure caching with equal/distinct unfolded bodies,
  reduction hints, open projections, raw and ordinary `OfNat` numerals, and
  symmetric string expansion. Ordinary numerals and successor applications
  explicitly retain their intermediate continuing status before later phases;
  they are not assumed to normalize in one step. Unequal strings compare false
  at callback depth 1024 and exhaust depth 32, matching the existing bounded
  recursion policy. Zero loop/callback budgets, one-round exhaustion, and the
  poisoned-cache premise are negative controls. This proves worker frames, not
  semantic WHNF completeness, successful inductive reduction, or unrestricted
  frontend closure. The actual `isDefEqCore'` dispatcher and arbitrary-fuel
  scoped method closure are proved in the following module.
- `TrEnv'.quotientObjects` and `TrEnv.quotientObjects` recover the five
  semantic quotient objects from the existing `TrEnv'` quotient transition,
  including the quotient equation, without adding a new environment premise.
  The induction transports the object witnesses through ordinary constants,
  definitions, theorems, opaques, and ignored unsafe records using the existing
  environment extension order; the constructor-free inductive branch is
  impossible. This exposes the registered quotient reduction rule as a reusable
  prerequisite for semantic WHNF completeness and terminal-sort work. The
  focused `QuotientEnvironmentObjects` fixture checks both wrappers and rejects
  direct axioms/admissions. It does not prove the remaining inductive reducer or
  unrestricted frontend theorem.
- `Verify.TypeChecker.ScopedMethods` proves the actual comparison dispatcher,
  closes scoped callbacks for arbitrary `Methods.withFuel`, and frames configured
  public entries and cold initialization. Its private dispatcher frame follows
  the actual quick/Boolean shortcut, cheap normalization/recomparison,
  proof-irrelevance, lazy-delta terminal cases, constant/free-variable/projection
  fast paths, full-normalization retry, and application/eta/string/unit fallback.
  `Inner.isDefEqCore'.scopeWF` combines that cache frame with the existing proved
  semantic dispatcher contract, preserving its original translated operands.
  `Methods.withFuel.scopeWF` structurally inducts on the actual callback depth;
  the successor record applies all four completed workers to the preceding real
  method record, with the existing `Methods.withFuel.WF` semantic base. No caller
  scoped-method instance or strengthened cache/name premise is required.
  `RecM.ScopeWF.run` consumes the actual reader-selected recursion depth.
  The public `whnfCore`, `whnf`, `inferType`, `checkType`, and `isDefEq` scoped
  contracts are now proved, and `M.ScopeWF.run` derives the actual cold initialized
  result contract from `VEnvs.WF` and the proved empty scoped caches. Generic
  arbitrary-depth, actual field/dispatcher/public, and cold normalized-head
  contracts compile. The fixture audits all 27 owned declarations against the
  original semantic arbitrary-fuel/native baseline without direct admissions or
  axioms. Its 1728 typed cold/warm bidirectional dispatcher/method/public
  comparisons, 1408 inference/checking/core/full entries, 232 cold initialized
  comparisons, 56 cold initialized full heads, and 48 polymorphic cold/warm
  comparisons pass in both safeties/eager modes at depths 32/128 and all cheap
  flags, including the open-term Boolean shortcut policy and equivalent constant
  universe levels. Zero-depth method fields, configured
  public entries, and cold normalization reject; a real depth-one pure comparison
  succeeds; poisoned caches retain the initial scoped-cache premise. These are
  derived actual method instances, not fabricated callbacks or finite-budget
  evidence substituted for the induction. They inherit the original semantic
  checker/metatheory and native representation dependencies, including existing
  admissions. Scoped-head/conversion preservation still does not establish
  semantic WHNF completeness, terminal-sort acceptance, successful inductive
  reduction, or the unrestricted non-inductive frontend theorem.
- `Inner.inferType'.scopeWF` proves the actual recursive inference dispatcher in
  checking and infer-only modes under the existing scoped method callbacks.
  Its premises mirror `inferType'.WF`: free-variable membership and, only in
  infer-only mode, an existing semantic translation. The proof covers loose-bound-
  variable rejection, selected inference-cache hits and typed insertion, literals,
  metadata recursion, current-fragment projection rejection, free variables,
  metavariable rejection, sorts, constants, lambda/forall/application/let workers,
  checked applications, ordinary/eager comparison, and mismatch errors. Inference
  cache insertion preserves both scoped WHNF caches unchanged. The scoped fixture
  checks eight generic/mode/metadata/application/let contracts and audits all 329
  owned scoped inference/WHNF declarations for direct proof admissions and axioms
  against the original semantic lambda/forall/dispatcher/WHNF and native baselines.
  The native inference-head fixture also passes its cold/warm cache controls in
  both inference modes. Together with `ScopedMethods` this closes the scoped
  inference dispatcher and actual arbitrary-fuel method instances, not successful
  inductive projection semantics, semantic WHNF completeness, or the full
  non-inductive frontend.
- `addDeclVerified.WF` preserves environment well-formedness and extension for
  successful checked declarations. Its entry point supports axioms, definitions,
  theorems, opaque declarations, unsafe/partial mutual definitions, and a checked
  quotient wrapper; it explicitly rejects inductives.
- `VEnvs.WF.empty`, `addDeclVerified.foldlM_WF`, and
  `addDeclVerified.fromEmpty` provide initialization and composition for finite
  declaration sequences. These are partial-correctness statements: they do not
  promise that checking any particular declaration succeeds.
- `CheckerEnv` factors out the lookup/delta portion of native checker environment
  correspondence: semantic `VEnv.WF`, native/semantic lookup alignment, and the
  translation of every admitted safe definition value to its semantic constant.
  The value contract preserves delta unfolding; well-formedness and alignment
  alone are not sufficient. `TrEnv.checkerEnv` derives this relation from the
  existing declaration-history invariant, while `CheckerEnv.addConst` preserves
  it across fresh translated, well-typed native constants with no unfoldable
  value. This relation is not yet sufficient to replace `VContext.trenv`:
  constructor/recursor/projection metadata contracts and primitive invariants
  remain separate obligations.
- `AddInductive.declareInductiveTypes.refinesChecker` and
  `AddInductive.checkInductiveTypes.refinesHeadersChecker` preserve `CheckerEnv`
  through the actual header-registration fold, including previously registered
  safe definition values. Header translations and semantic header typing remain
  explicit inputs. This is typed-axiom staging,
  not a native declaration-history extension: `AddInduct`, positivity, generated
  recursors/reduction equations, and full inductive frontend soundness remain
  open. The verified checker and non-inductive frontend retain the stronger
  `TrEnv` invariant; the existing metadata-dependent checker admissions are not
  silently generalized to the weaker relation. No executable checker behavior
  changes.
- `NativeValueFrame` independently proves native constant-map well-formedness,
  retention of every old lookup, and that any final value-bearing record belongs to
  the initial map. Its fresh no-value insertion and generic stateful fold proofs
  apply to both native registration traversals. `declareInductiveTypes.preservesValues`,
  `declareConstructors.preservesValues`, and
  `checkInductiveTypes.preservesHeaderConstructorValues` cover the actual checked
  header/constructor prefix without semantic typing or translation premises.
  `declareConstructors.refinesChecker` combines this native frame with semantic
  constructor WF/registration refinement. The stronger
  `checkInductiveTypes.refinesPrimitiveHeaderConstructorChecker` derives canonical
  `Bool`/`Nat` header/constructor registration, translation, semantic WF, and final
  lookup/delta correspondence from initial `CheckerEnv` and primitive-validator
  success, with no caller-supplied semantic models or registration-success
  premises. These results still install typed ordinary constants; they do not
  justify native constructor/projection metadata, generated recursors/reduction
  equations, primitive invariants, or replacement of `VContext.trenv`.
- `Verify.InductiveValueFrame` extends that native frame through the full
  `AddInductive.run`, including fresh recursor registration, for arbitrary
  context safety. `declareRecursors.preservesValues` strengthens the existing
  suffix map/lookup theorem without changing its interface. Fresh restoration
  traces preserve values when every allowed record has `value? = none`;
  `RestoredInductiveRecord.value?_eq_none` supplies that condition for restored
  headers, constructors, and recursors. Consequently
  `Environment.addInductive.safePreservesValues` and
  `addDecl.safeInductivePreservesValues` cover the actual safe public frontend,
  direct and genuinely nested restoration branches, and both dispatch check
  flags. Their only input invariant is initial native map validity. This is
  exact old-record retention and exclusion of new delta-value records, not
  constructor/recursor typing, inductive reduction soundness, or a replacement
  for semantic `VInductDecl.WF`, `VEnv.addInduct`, `AddInduct`, or `VContext.trenv`.
  All six new theorems are audited without `sorryAx`; only the existing three
  persistent-map interfaces and standard logical axioms occur. Unsafe public
  nested restoration is deliberately outside this theorem.
- `Verify.InductiveHeaderTyping` derives semantic type well-formedness of the
  first source header from successful `checkInductiveTypes`, without a supplied
  semantic header model or type-WF premise. It uses actual source guarding,
  checked source translation, and accepted WHNF: a normalized Pi is a type by
  strict translation, while a non-Pi must pass the actual terminal sort check.
  `firstHeaderWF` closes the semantic local context and constructs its reset
  checker-state invariant automatically. `singleHeaderChecker` consequently
  derives typed header registration, semantic environment WF, alignment, and
  old-value translation for an arbitrary singleton header and parameter count.
  `run.firstHeaderWF` exposes the source-header result on every successful
  nonempty complete runner. The input remains the existing strong `VContext`
  with `TrEnv`; it is not replaced by the weaker native frame or `CheckerEnv`.
  These proofs inherit the existing checker/metatheory's `sorryAx` and interfaces,
  but introduce no new admission or axiom. By themselves, they do not verify
  later mutual header models, constructor positivity/typing, recursor typing/equations,
  preprocessing transport of original header semantics, or `VInductDecl.WF`.
- `Verify.InductiveMutualHeaderTyping` extends derived semantic header WF to
  every header in the actual mutual checking traversal, not only the first.
  `HeaderParameterModels` tracks real parameter lookup support. Accepted
  parameter equality is interpreted through the existing checker, and
  `translatedReusedHeaderParameter` types the reused argument and substitutes it
  into the candidate body before interpreting its accepted WHNF. General
  `CheckedHeaderTrace.checkerModels` handles fresh parameters, reused parameters,
  and accumulated indices, preserving a typed local-context history. Each
  guarded closed source header is strengthened back to the initial empty
  semantic context, so `checkInductiveTypes.headersWF` derives all source models
  and type-WF proofs without asking the caller to supply them.
  `headersChecker` derives whole-array typed header registration, semantic WF,
  alignment, and old-value translation; `run.headersWF` projects every source
  header from the successful complete runner, including empty arrays without a
  default-element claim. The existing strong initial `VContext`/`TrEnv` remains
  required. Initial canonical annotation constants/definitions and disjoint
  reader/reset-checker generator prefixes are explicit; the root reservation
  and reset-state invariants are derived from the empty model. These are typed
  ordinary-constant header results, not semantic inductive declarations,
  constructor/recursor typing, positivity, or reduction equations. The inherited
  checker/metatheory admissions remain explicit; no new axiom or admission is
  introduced, and the initial annotation contracts are not silently assumed.
- `Verify.InductiveHeaderAxiomView` constructs a strong declaration-history model
  for a separate axiom shadow of the actual native header stage. It does not
  reinterpret the native inductive rows as verified inductive declarations or
  change `TrEnv`, `VContext`, or any checker admission. Fresh accepted header
  registration is replayed through existing `TrEnv'.axiom` constructors and
  semantic `addInductHeaders`; every old record is retained exactly. The shadow
  replaces only the new inductive-header tags with axiom tags, retaining names,
  universe parameters, source types, safety, and exact optional values at every
  lookup. Replay uses the existing registration and semantic monotonicity
  contracts, rather than invoking the admitted checker algorithms. The
  all-header checking and arbitrary-continuation
  stage theorems derive the header models/WF instead of requiring caller models;
  `run.headerAxiomViewStage` projects the shadow stage from complete successful
  safe/unsafe runs. The latter explicitly excludes `.partial` checker safety,
  whose admission order does not admit the runner's unsafe header rows.
  `VContext.inHeaderAxiomView` derives a genuine strong context for the shadow,
  preserving the original local model and every other native context field,
  given the semantic extension, strong shadow history, and exact primitive
  frame. Header registration derives that primitive frame when primitive
  declarations are disabled. `VState.WF.headerAxiomReset` carries the existing
  generator reservations into a fresh validated shadow state; it does not reuse
  old caches. There is still no proof transporting actual
  constructor checking into this shadow: projections and other metadata-sensitive
  operations distinguish the two environments even when all type/value lookup
  signatures agree. In particular, the projection regression demonstrates this
  after constructor registration. The initial strong checker, canonical
  annotation, and generator-prefix premises remain explicit; the three checked
  stage projections inherit the existing checker/metatheory admissions, while
  replay and context-model extension retain the existing semantic metatheory
  admissions. No
  constructor-WF, positivity, recursor equation, or full-inductive theorem is
  claimed by the shadow construction.
- `Verify.InductiveHeaderContinuation` derives the typed continuation reader
  from the actual mutual header traversal. `TypedHeaderReader` separates the
  first shared parameter model from all accumulated index locals, records the
  exact native parameter array, and supplies native reader alignment, a validated
  fresh checker state, full parameter/ambient prefix histories, and parameter
  lookup support. The traversal constructs the first model by checked binder
  opening and preserves it through later reused-parameter equality checks and
  index allocations. `checkInductiveTypes.withTypedContinuation` exposes this
  model at the real continuation together with whole-array source-header models
  and semantic WF, native header sizes/counts, and unchanged environment,
  universe, safety, primitive-authorization, and fuel fields. It supports empty
  arrays without selecting a default source header.
  The continuation also retains conversion-aware compatible parameter inputs for
  every parent at this exact final mixed context, deriving each from its actual
  checked header trace and weakening earlier inputs through later index locals.
  Nonempty batches retain the exact original universe-level array.
  `withHeaderAxiomContinuation` performs actual header registration, derives its
  separate strong axiom shadow, and extends this exact local model to the shadow
  with fresh-state WF and primitive/value frames. The stage also derives and
  carries initial/actual native map WF and separate actual-header/shadow-axiom
  fresh registration traces from successful header registration, rather than
  inferring these from signature agreement with the shadow. No caller-provided
  parameter model, header model, or header type-WF evidence is required.
  `constructorAxiomContinuation` packages this proved shadow model with successful
  actual constructor checking and the accepted native constructor traces at the
  same staging checkpoint. The complete runner projects this package for
  ordinary safe/unsafe runs, excluding `.partial` checker safety and primitive
  declarations explicitly. The shadow model now supplies the existing constructor
  domain-receipt theorem's parameter/ambient premises. Actual constructor
  acceptance is transported below under a native metadata frame, now derived
  from those registration traces and explicit initial native parent closure.
  These results
  retain the strong initial `VContext`/`TrEnv`, canonical annotation contracts,
  disjoint generator prefixes, and inherited checker/metatheory admissions;
  they are not semantic constructor WF, positivity, or inductive soundness.
- `Verify.InductiveConstructorFreshness` derives absence of every source
  constructor name at the actual header checkpoint and global constructor-name
  distinctness, including across mutual parents, from successful eventual
  constructor registration. The raw registration theorem requires native map WF
  but no constructor typing or arity model. Exact old-record preservation
  transports absence backwards, and header/axiom signature agreement transports
  it into the separate shadow. The native-only complete-run receipt includes
  installed header metadata, accepted actual constructor checking, and the
  registration value frame; the ordinary safe/unsafe shadow receipt pairs both
  absence facts with the already derived typed continuation without additional
  caller models. Constructor checking alone does not imply freshness: valid
  constructor types can still collide with existing names, their own or another
  mutual header, or a constructor registered earlier in the batch.
  The native projection barrier rules out successful projection inference when
  the normalized parent header's constructors are missing. The raw structure-eta
  barrier excludes a missing constructor head; the raw unit-like barrier excludes
  the constructor lookup of an otherwise qualifying nonrecursive singleton
  parent with no indices. All three support arbitrary native methods and checker
  state, conditional only on their explicit native lookup/normalization evidence.
  These results do not establish unrestricted checker transport.
  Header-only `isStructureLike` can
  already be true, whereas it is false in the axiom shadow; the unit-like helper
  can fail on a missing actual constructor while returning false in the shadow.
  Raw freshness and metadata-barrier contracts exclude `sorryAx`; typed shadow
  receipts retain the inherited checker/metatheory admissions. Constructor WF,
  positivity, recursor equations, and full inductive soundness remain open.
- `Verify.InductiveHeaderCheckerTransport` starts native checker transport with
  an exact lookup bridge, not unrestricted signature extensionality.
  `HeaderAxiomLookupAgreement` classifies each lookup as an identical native
  record in both environments, or a source-batch inductive header and its exact
  axiom view. Successful header registration derives this source-indexed
  classification while retaining the old strong-header theorem as a projection.
  `HeaderAxiomContinuation` also derives exact source constructor lists for the
  installed headers. Combined with eventual registration freshness,
  `missingChangedHeader` supplies the missing-constructor premise for every
  changed native header. Continuation construction requires no additional caller
  header/parameter model, lookup classification, or constructor-list premise.
  Constructor/recursor lookup casts and constructor-application observations
  agree exactly. Delta selection and both core/application definition unfolding
  agree exactly, including optional results and the entire native checker state.
  Constant inference preserves every accepted result; the executable constant
  branch and public `checkType`/`inferType` entry points preserve accepted bare
  constants and their complete state at every recursion fuel, with either cache
  bank and arbitrary initial native caches. Missing-name diagnostics may retain
  different environment payloads, so successful constant transport is not stated
  as equality of all exceptions. These raw transport contracts exclude
  `sorryAx` and do not establish semantic cache WF. Arbitrary-expression and
  metadata-sensitive recursive transport is composed below under explicit native
  environmental eligibility. Accepted constructor-check transport is composed
  below under that native frame; staged eligibility is derived below from
  initial native parent closure. Automatic shadow domain receipts are composed
  below; constructor WF remains open. The strong
  initial `VContext`/`TrEnv` is unchanged; no substitute `CheckerEnv` assumption or
  broader checker admission is introduced.
- `Verify.TypeChecker.Transport` supplies directional accepted-result
  composition rather than equality of failing computations. `Except.SuccessTransport`
  allows different error types, and its bind rule requires continuation transport
  only for an accepted actual prefix. `TypeChecker.M.SuccessTransport` preserves
  the entire returned native state; its continuation receives the exact accepted
  result/state equation. The application-spine relation lemma covers the actual
  `Expr.withApp` implementation, not an alternative expression traversal.
  `Verify.InductiveHeaderNormalizationTransport` applies this calculus to native
  sort/forall guards, proposition testing, equality-manager updates, and projection
  reduction. Direct sort/forall guards require no normalization premise. Otherwise
  their reached WHNF callback must transport. Proposition testing requires inference
  transport and WHNF transport only on the accepted inferred type/state. Equality
  testing preserves both true/false results and the complete native equivalence
  manager update after an accepted comparison callback.
  `reduceProj.headerAxiomTransport` combines the exact header lookup bridge with
  transport of the selected full/core normalization callback. String expansion
  requires its second callback only when the accepted first result is a string
  literal, at that returned state. Constructor records agree exactly; a changed
  inductive header and its axiom shadow are both non-constructors, so no structure
  metadata equality or old-parent eligibility premise is needed by this helper.
  Missing-name failures may still carry different native environments. All owned
  declarations exclude `sorryAx`; these are real native compositional lemmas with
  explicit reached-callback obligations, not an unrestricted theorem about
  `Methods.withFuel`. The recursive module below composes these helper receipts;
  strong continuation below supplies default semantic-state WF and derives
  automatic domain receipts under explicit initial native parent closure.
  Constructor WF and full inductive soundness remain open.
  The constructor module below composes accepted strong-shadow
  constructor checking under the native frame. No executable checker
  behavior or initial strong `VContext`/`TrEnv` invariant changes.
- `Verify.InductiveHeaderRecursorTransport` transports the actual native K and
  structure-major adaptation helpers without assuming structure metadata agrees
  for a changed header. A parent whose shadow lookup still has an inductive tag
  must have an identical actual lookup. `stableOriginalInductiveParent` derives
  this equality from the existing shadow value-frame receipt and an original
  inductive lookup; the parent name need not be separately excluded from the
  abstract changed-name predicate. Stable parent lookups preserve the native
  structure-like test, first-constructor selection, nullary constructor creation,
  and structure expansion. Constructor casts agree even at other names that
  change from inductive headers to axioms. Pure expansion equality does not assert
  constructor metadata WF or exclude the existing unreachable fallback.
  `toCtorWhenStruct.headerAxiomTransport` handles both initial early exits,
  normalized-type parent mismatch, proposition rejection, and structure expansion,
  preserving complete accepted states across distinct methods/readers. Its type
  and sort prefix obligations are guarded by the actual reached initial tests;
  the sort obligation also receives the exact accepted type/state and matching
  parent test. `toCtorWhenK.headerAxiomTransport` requires the native K flag and
  covers nonconstant and wrong-parent types, the complete metavariable-index scan,
  missing constructor selection, and true/false constructor comparisons. Its
  comparison receipt is indexed by the accepted type/state and selected native
  constructor. The generic transport module now relates `Expr.withApp` to its
  actual head and proves the native pure `forIn'` scan independent of readers and
  checker state, including early exits. These raw contracts exclude `sorryAx`;
  only original-parent lookup conversion uses the existing persistent-map lookup
  interface. They do not derive old recursor parent/constructor closure merely
  from lookup classification, or unconditionally transport `inductiveReduceRec`, recursive
  `Methods.withFuel` transport, semantic state WF, accepted constructor-check
  transport, constructor WF, or full inductive soundness. Strong initial
  `VContext`/`TrEnv` and executable behavior remain unchanged.
- `Verify.InductiveHeaderReductionTransport` composes the native K and structure
  helpers through the entire successful `inductiveReduceRec` program. Raw
  `NativeRecursorEntryReceipt` and `NativeRecursorMajorReceipt` record the actual
  constant head, recursor lookup, in-bounds major selection, and accepted optional
  K-adaptation result/state. Parent metadata stability is required only at a
  reached recursor entry; normalization, literal-string expansion, and structure
  type/sort prefixes are indexed by the exact accepted earlier results/states.
  K inference and comparison obligations also receive the reached entry and K
  flag. The proof covers native natural/string literal handling, structure
  expansion, missing rules, field and universe-arity guards, level substitution,
  parameter/motive/minor application, trailing major fields, and overapplication.
  It preserves the entire accepted state across distinct methods and readers,
  not merely the final expression or selected caches.
  `quotReduceRec.transport` separately preserves the actual quotient helper from
  its reached lift/ind major-normalization callbacks. The outer
  `TypeChecker.Inner.reduceRecursor.headerAxiomTransport` preserves quotient-first
  dispatch and both cheap flags, requiring equality of the quotient gate and
  native inductive transport only after an accepted quotient miss (or bypass).
  Successful native header registration and the axiom view both preserve
  `quotInit`, so that gate equality follows from their shared original environment;
  lookup classification alone is not used to infer it. All module-owned raw
  declarations exclude admissions and persistent-map axioms. Callback transport
  and old-parent closure remain explicit obligations, not consequences of name
  freshness. These proofs alone do not derive semantic cache/state WF, automatic old
  recursor parent/constructor closure, general mutually recursive method
  transport, accepted constructor-check transport, constructor WF, or full
  inductive soundness. Strong initial `VContext`/`TrEnv` remains unchanged.
- `Verify.InductiveHeaderWHNFCoreTransport` transports the complete actual
  `TypeChecker.Inner.whnfCore'` program from reached callback receipts and equal
  local contexts, across distinct methods/readers and identical initial states.
  `NativeCoreHeadReceipt` records the actual application/cache miss and accepted
  head normalization result/state. `NativeCoreCallbacks` limits local-let, zeta,
  beta, rebuilt-head, recursor and projection obligations to the native reached
  branches and exact earlier accepted states/results. Recursor/projection fields
  accept the native helper contracts established by the previous transport
  modules; environment lookup agreement is not silently treated as universal
  callback refinement. Native head comparison remains its actual Boolean test,
  not an unjustified propositional equality of expressions.
  `whnfCoreBetaInput` factors the exact native lambda-peeling input, including
  reversed arguments, partial saturation and overapplication; `loop_eq` proves
  this factorization against the existing native loop. It does not replace that
  loop or use a different beta traversal. Outer metadata removal and the native
  reader/cache prefixes are likewise proved equal to the actual program.
  The proof preserves all result-state fields and the asymmetric native cache
  policy: easy cases and non-let free variables bypass cache reads; other reached
  cache hits return even under cheap flags. Beta, rebuilt-head, zeta and projection
  paths save only with both flags off; local-let free variables and unchanged-head
  recursor paths do not add the outer cache entry. Native `isLetFVar` includes
  nondependent local lets, so its value receipt uses `LocalDecl.value? true`.
  All owned declarations exclude admissions and persistent-map axioms. This is
  directional accepted-computation transport, not semantic cache/state WF, a
  proof that malformed metadata cannot reach panic fallbacks, or general
  `whnf'`/`inferType'`/mutually recursive `Methods.withFuel` transport. The modules
  below compose translated input eligibility, staged native closure, accepted
  constructor checking and automatic domain receipts under explicit initial
  native parent closure. Constructor WF, semantic inductive registration and
  full inductive soundness remain open. Strong initial
  `VContext`/`TrEnv` and executable checker behavior remain unchanged.
- `Verify.InductiveHeaderWHNFTransport` transports the complete actual
  `TypeChecker.Inner.whnf'` program across header shadows, distinct methods and
  distinct readers with equal local contexts. `NativeWhnfEntryReceipt` requires
  native cache eligibility and a cold full-normalization cache entry.
  `NativeWhnfReachable` records the actual selected normal/eager budget and only
  the accepted core/native/natural/unfolding prefixes that reach a subsequent
  iteration. `NativeWhnfCallbacks` requires core receipts only at positive-fuel
  reached inputs and natural-reduction transport only after accepted core
  normalization and a native miss. No universal untyped callback refinement is
  assumed. `NativeNatOperands` and the native arithmetic-helper/dispatch proofs
  derive that natural transport from reached operands: the second callback is
  needed only after accepted first normalization and successful literal
  extraction, including the native `Nat.zero` extension and exponent cap.
  General unfolding equality follows from header delta lookup agreement, even
  with different methods, safety, universe readers and fuel configurations.
  Native reduction is independent of its environment argument; unsupported
  native requests continue to reject.
  `whnf'.loop_headerAxiomTransport` permits a shadow remaining budget at least
  the actual remaining budget, rather than requiring identical budgets. The
  full entry theorem requires this inequality only for a cold eligible entry;
  easy inputs and native cache hits bypass callbacks and fuel. Metadata peeling
  and the cache prefix are proved equal to the existing program. Successful loop
  results retain every state field, followed by the native unconditional final
  cache insertion; the loop does not reread the outer full-normalization cache.
  This is directional accepted-computation transport, not semantic cache/state
  WF or a proof that all callbacks satisfy the receipts. Recursive method
  receipts are closed below under `NativeRecursiveHeaderFrame`; translated-input
  eligibility and automatic staged domain receipts are composed below under
  initial native parent closure. Constructor WF, semantic inductive registration
  and full inductive soundness remain open. Strong initial `VContext`/`TrEnv`
  and checker behavior are unchanged.
- `Verify.InductiveHeaderWHNFMethodTransport` derives the normalization half of
  the recursive-method successor step from the four smaller-depth method
  receipts, uniformly over complete reached states. `NativeMethodTransport`
  contains only raw method transports: no recursor, projection, natural
  reduction, core or full-normalization helper obligations remain in this step.
  The recursor proofs now support an arbitrary literal normalization callback,
  with the previous full-WHNF theorems retained as specializations. This covers
  the actual cheap-rec policy throughout K adaptation, major/string
  normalization and structure type/sort normalization, without replacing the
  method record or changing panic fallbacks. Projection and natural callbacks
  are likewise derived from the four method receipts; complete native core and
  full-normalization callbacks follow, including all cheap-rec/cheap-proj
  combinations and larger shadow normalization budgets.
  `Methods.withFuel.zeroTransport` proves the simultaneous vacuous base case;
  `normalizationStep` derives both normalization fields at successor depth, and
  `normalizationDepthOne` discharges its smaller-depth premise. This module
  supplies only the normalization half; `InductiveHeaderRecursiveTransport`
  supplies the inference/comparison fields and scoped/eager reader preservation
  that close simultaneous all-depth induction.
  `NativeRecursorParentFrame.ofNativeOrigins` derives the uniform parent frame
  from initial native recursor-parent closure, actual native recursor-origin
  receipts and retained native shadow inductive lookups. Initial native closure
  is not inferred from a semantic context or imported-prelude execution. The
  native metadata module derives staging origins and retention from actual fresh
  registration traces, explicitly retaining existing persistent-map lookup and
  insertion interfaces; these dependencies are not imported into the clean raw
  audit boundary.
  The frame cannot cover registered new-parent recursors across their axiom
  shadows. Constructor freshness remains required for inference/unit metadata
  in the eventual before-constructor bridge. Strong initial `VContext`/`TrEnv`,
  semantic state/cache WF and all inductive soundness boundaries are unchanged;
  no checker algorithm, axiom or admission is added.
- `Verify.InductiveHeaderRecursiveTransport` closes simultaneous depth induction
  for all four actual `Methods.withFuel` fields across a native header axiom
  shadow. The theorem has no method or helper callback obligations: every
  inference, normalization, quick/binder/application comparison, eta, structure,
  string, unit, proof-irrelevance, arithmetic and lazy-delta receipt is derived
  from the smaller-depth induction hypothesis. `NativeHeaderReaderFrame` keeps
  every reader field except the environment exact, including fuel configurations.
  Its transport is preserved by actual lambda/forall/let telescope openings,
  binder-comparison openings and the eager `inferComparisonContext` adjustment.
  The scoped hypothesis is uniform over complete states and all such readers;
  no particular expression, method depth or reached-state subset is assumed.
  The zero-depth deep-recursion case is vacuous, and the complete simultaneous
  successor step composes the actual native programs, not replacement checkers.
  Public `inferType`, `checkType`, `whnf`, `whnfCore`, `isDefEq`, `ensureSort` and
  `ensureType` entry theorems use the actual reader-selected recursion depth and
  preserve every accepted result and complete final state.
  `NativeRecursiveHeaderFrame` retains genuine environmental eligibility:
  header lookup agreement, stable entered recursor/constructor parents, native
  projection/unit eligibility and quotient-initialization alignment.
  `beforeConstructors` derives constructor-parent stability and all projection
  frames from actual constructor freshness, exact native entered-header
  constructor names and native constructor-parent membership; native old
  recursor shadow-parent lookups remain explicit. Registered new-parent
  constructors/recursors across axiom shadows do not satisfy this frame.
  This is directional accepted-computation transport, not equality of errors or
  a semantic state/cache WF theorem. The native metadata module derives staged
  native closure and lookup eligibility from explicit initial native closure and
  the actual accepted registration traces. Initial native parent closure remains
  an eligibility input, not an asserted consequence of the strong semantic
  history alone. This result does not substitute a weaker
  `CheckerEnv` for initial `VContext`/`TrEnv`, derive translated constructor inputs
  or strong shadow cache/state WF, or yet compose accepted constructor checking
  with semantic constructor WF. Positivity, recursor equations, semantic
  inductive registration and full inductive/frontend soundness remain open.
  Every owned declaration excludes admissions and implementation-interface
  axioms; executable checker behavior and existing admission boundaries are
  unchanged.
- `Verify.InductiveConstructorTransport` applies the callback-free recursive
  checker transport to the actual `AddInductive.checkConstructors` program.
  `M.SuccessTransport.typeChecker` respects the actual lift: each checker call
  starts with its fresh default state, copies the full local context, universe
  parameters, safety and fuel, and discards the returned native state. Positivity
  and constructor-spine transport follow their actual decreasing fuel, shared
  parameter lookup/comparison, domain sort and universe checks, safe-only
  positivity calls and annotation-peeled local openings with the exact scoped
  name-generator advancement. The list-loop theorem preserves duplicate-name
  state and both early completion/yield cases. A definitional factorization
  captures the initial environment read rather than falsely transporting that
  environment as an equal result. The mvar/fvar source guard preserves accepted
  outcomes even though rejected diagnostics can contain different environments.
  `checkConstructors.headerAxiomTransport` has no helper/method callback premises
  and transports the entire actual constructor batch under
  `NativeRecursiveHeaderFrame`. All owned raw declarations exclude admissions
  and implementation-interface axioms.
  `Verify.InductiveConstructorContinuation` separately composes this transport
  with the existing strong staged axiom shadow.
  `HeaderAxiomContinuation.acceptedConstructors` derives accepted shadow checking
  and constructor traces from actual acceptance. Its remaining inputs are genuine
  native metadata eligibility: actual constructor freshness and parent closure,
  old recursor shadow-parent lookups and quotient alignment; entered header
  lookup agreement and exact constructor lists come from the stage. The strong
  composition theorem inherits `sorryAx` through its existing `VContext` and
  `HeaderAxiomContinuation` input types, not through the raw transport proof; its
  exhaustive audit permits only the dependencies already present in that strong
  input. The native metadata module derives the staged metadata premises from
  actual registration and explicit initial native parent closure. This is not a semantic
  constructor WF, positivity/recursor equation, registration or full frontend
  soundness theorem; translated-input eligibility and strong shadow reader/state
  WF are composed in the semantic receipts module below. No weaker `CheckerEnv`,
  checker algorithm change, new admission or implementation-interface axiom is
  introduced.
  `tests/InductiveConstructorTransport.lean` exhaustively audits all twenty-four
  owned raw declarations against only `propext`, `Classical.choice` and
  `Quot.sound`, and the one strong continuation theorem against its exact
  existing strong-stage dependency baseline. Its 432 native/shadow outcomes
  cover empty and constructor-free batches, nullary and genuinely mutual types,
  shared/dependent/universe parameters, indexed and higher-order recursion,
  peeled annotations, a thirty-two-field spine, both safety/primitive settings,
  complete fuel configurations and exhaustion. Rejection controls exercise
  parameter mismatch, nonpositivity, universe overflow, wrong returns, duplicate
  names and source metavariables/free variables. Expected nonempty successes also
  pass the native kernel. These executable metadata-stage checks are not proofs
  of the remaining staged native eligibility or semantic constructor WF.
- `Verify.InductiveHeaderNativeMetadata` closes the actual staged native metadata
  frame under initial native constructor-parent membership and recursor-parent
  closure. `strongHeaderAxiomRegistrationView` derives actual inductive-header
  and shadow header-axiom fresh registration traces from the real accepted
  `checkName`/insertion program, preserving the previous lookup/view contracts
  as projections. The strong staged continuation carries these exact traces and
  initial native map WF. Trace lookup origin excludes newly introduced
  constructors/recursors, and native lookup retention preserves all old parents
  and constructor-name membership. Both traces preserve quotient initialization
  directly. `HeaderAxiomContinuation.nativeFrame` derives the recursive frame;
  no caller supplies staged constructor closure, recursor shadow-parent lookups,
  quotient alignment or a method/helper transport callback. The checked prefix
  and complete `AddInductive.run.nativeConstructorAxiomContinuation` derive
  constructor freshness from actual later registration and package the derived
  native frame, accepted actual/shadow constructor checking and shadow traces
  with the unchanged strong initial `VContext`/`TrEnv` contracts.
  Native trace lookup/retention explicitly retains the existing interfaces
  `Lean.PersistentHashMap.findAux_isSome`, `Lean.PersistentHashMap.WF.find?_eq`
  and `Lean.PersistentHashMap.WF.toList'_insert`, inherited from
  `FreshRegistrationTrace.lookup`/`preserves`. Generic native lemmas permit only
  these interfaces and the three standard logical axioms;
  strong stage theorems additionally inherit their input-type admissions, and
  prefix/run composition retains existing source-pipeline dependencies.
  Initial native parent closure is still an explicit native eligibility input;
  it is not inferred from a weaker `CheckerEnv`, signature/value agreement or
  runtime prelude scans. Translated constructor-input eligibility and semantic
  shadow domain receipts are composed below; constructor WF,
  positivity/recursor equations, semantic registration and full
  frontend/prelude soundness remain open.
  The native metadata fixture exhaustively audits all ten owned declarations
  against their exact native-interface, strong-input or existing source-pipeline
  baselines. Twenty-eight metadata-stage/constructor/full-run combinations cover
  empty/constructor-free, recursive/higher-order, parameterized, indexed and
  genuinely mutual batches, both safety/primitive settings, nonzero nested
  metadata and initialized/uninitialized quotient environments. It checks native
  constructor/recursor origins, all old inductive parent fields, constructor-name
  membership and both accepted constructor checkers; expected nonempty types also
  pass the native kernel. Runtime prelude closure checks are controls, not proofs
  that the strong semantic history implies the initial native closure premises.
- `Verify.InductiveConstructorSemanticReceipts` derives translated constructor
  inputs and semantic parameter-domain receipts automatically from the accepted
  constructor batch in the strong header-axiom continuation.
  `TypedHeaderReader.constructorTranslation` obtains free-variable eligibility
  from the actual source guard and translation from actual lifted `checkType`,
  then strengthens it through the stored parameter/ambient insertion history to
  the original base context. No caller supplies translated constructor inputs,
  parameter-domain equality, semantic local openings or default-state WF.
  `TypedHeaderReader.constructorDomains` supplies the existing domain-receipt
  theorem's aligned reader, default-state, history, ambient-drop and statistics
  premises from the strong reader model. `shadowUniverses` derives the exact
  initial universe list from both aligned readers.
  `ConstructorSemanticReceipts` contains a complete translated `VInductDecl`,
  actual header registration into the same semantic shadow, semantic header WF
  and every constructor's accepted shadow trace, checked parameter-domain
  receipts, complete target-context agreement and exact parameter-target length.
  Completing the constructor lists preserves every semantic header signature;
  `addInductHeaders.sameConstructorLists` transports registration without
  pretending the constructor lists themselves are unchanged.
  `shadowConstructorSemantics` constructs these receipts from accepted shadow
  checking. `constructorSemantics` derives them from actual checking and initial
  native parent closure; the checked prefix and complete
  `AddInductive.run.semanticConstructorAxiomContinuation` supply actual
  constructor freshness from later accepted registration. Strong initial
  `VContext`/`TrEnv`, ordinary primitive/safety restrictions and exact fuel,
  scope and generator contracts remain unchanged.
  Source translation alone does not establish that translated constructor types
  are `IsType`. The executable `checkType` is checked inference, not sort-valued
  type formation: `Nat.zero` passes that source call but is rejected as a
  constructor type by the complete constructor checker. The complete receipts
  do imply constructor WF through the checker-model
  module below recovers constructor WF for binder sources and complete
  parameterized batches; binder-free sources use the return-typing theorem below
  with automatically derived contextual header kinds. The combined
  `constructorTypesWF` theorem supplies full batch constructor type WF.
  Positivity/recursor equations, semantic inductive registration and full
  inductive/frontend/prelude soundness remain open.
  The fixture exhaustively audits all 33 owned declarations, including generated
  receipt declarations. List membership/signature lemmas use only logical
  axioms; strong receipt types inherit existing `sorryAx`; translation, domain
  and prefix/run proofs retain the existing checker/metatheory baseline of 31
  dependencies. No new axiom or admitted proof is added. Thirty-two native
  controls cover empty/constructor-free, recursive/higher-order, parameterized,
  universe-polymorphic, indexed and genuinely mutual batches, plus
  annotation-peeled dependent field openings, under both
  safety/primitive settings, with unsupported-source rejection and the checked
  term/type-formation boundary. Runtime controls do not fabricate a semantic
  context or prove the imported prelude's strong invariant.
- `Verify.InductiveConstructorCheckerModels` models the entire real accepted
  constructor spine in strong typed readers, including reused parameters and
  fresh fields, rather than stopping semantic reasoning at the parameter prefix.
  `translatedHeaderOpening` and `translatedReusedHeaderParameterOpening` factor
  the existing header helpers before their subsequent WHNF call. Both provide
  strict translated and sort-valued typed opened bodies; the old normalized
  helper signatures remain unchanged compositions. Constructor checking does
  not normalize opened bodies, so no fictitious accepted WHNF premise is added.
  Fresh fields use the exact annotation-peeled native domain, declaration name,
  binder, free-variable identifier and generator advance. Domain conversion
  transports body typing into the peeled context, and the actual lifted
  `ensureType` receipt recovers the checked sort and its precise semantic level.
  `CheckedHeaderContinuation` now retains native reader reservation and the
  default-checker/reader generator-prefix separation already derived inside the
  actual header program; callers supply neither as staged obligations.
  `AcceptedConstructorTrace.checkerModels` supplies an aligned final strong
  checker with default-state WF, unchanged semantic environment/universes, a
  typed local-declaration history and exact field count, including arbitrary
  starting constructor indices. Reused parameters do not add native locals;
  fields do, with their actual fresh identifiers. Source typehood is preserved
  through every real opening to the final translated return expression.
  `TypedConstructorReceipts` combines complete input/domain receipts with these
  reader models and automatic constant WF for every accepted constructor.
  The strong shadow, actual-stage,
  checked-prefix and complete `AddInductive.run.typedConstructorAxiomContinuation`
  bridges derive them from real acceptance and later registration freshness.
  Canonical annotation signatures and definitions are inherited from the root
  through the actual semantic header extension, not assumed for the shadow.
  `TrConstructor.forallWF` proves semantic constructor type WF for every source
  beginning with a forall. `CheckedConstructorDomainReceipts.requiresBinder`
  derives that source shape from positive complete parameter-target growth.
  Consequently `ConstructorSemanticReceipts.parameterizedTypesWF` automatically
  proves WF for every translated constructor in the complete declaration when
  `stats.params.size > 0`, with no caller-supplied constructor translations or
  per-constructor binder/typehood premises.
  Binder-free constructors of zero-parameter families now obtain typehood from
  automatic contextual batch kinds and saturated return-application typing,
  as proved below. Semantic positivity,
  recursor equations, complete inductive registration and full frontend/prelude
  soundness remain open; this is not a full inductive soundness theorem.
  The conditional `AcceptedConstructorTrace.zeroParameterKind` reconstructs
  sort arity from a sort-arity anchor, and `TrConstructor.sortArityWF` converts
  a closed zero-arity receipt into `VConstant.WF`. These cannot supply ordinary
  constructor-return anchors: an inductive type such as `Nat` has a sort as its
  type, but is not itself definitionally a sort. The return-typing module below
  instead derives `IsType` from the sort arity of the header's type. No caller
  may replace strict translation with unchecked inference or a weakened checker
  context.
  Strong initial `VContext`/`TrEnv`, exact ordinary safety/primitive restrictions,
  genuine initial native parent closure and all executable checker behavior
  remain unchanged. The expanded semantic receipt fixture exercises the new
  opening, final-context/field-count/typehood, parameterized WF, actual-stage and
  full-run contracts through 27 formal examples. It audits all 47 owned
  reader-model declarations, both factored shared helpers and the 33 input-receipt
  declarations, and passes 36 native source/constructor/full-run controls.
  Canonical annotation extension lemmas have no axiom dependencies. Binder and
  parameterized constructor-WF extraction retain the existing semantic input
  baseline of four dependencies, including `sorryAx` through the existing
  `TrConstructor`/strong receipt interfaces; they are not admission-free semantic
  soundness proofs. Fresh and reused opening helpers inherit 11 and 28 existing
  dependencies respectively; whole trace models retain 28, and source-guard,
  batch, strong-stage and prefix/run composition retain the existing 31.
  Each audit compares against the genuine earlier semantic/checker/source
  interfaces, including the real no-metavariable/free-variable guard, rather
  than using the admission-free raw native transport baseline. No new axiom or
  admitted proof is added.
- `Verify.InductiveReturnTyping` derives semantic typehood of saturated
  inductive return applications from exact semantic header-kind receipts.
  `SortArity.apply` consumes one binder of the function's type using unique
  typing, forall injectivity, context conversion and typed substitution.
  `typedIsType` converts a zero-arity receipt for the resulting type into
  `IsType` of the applied expression; it does not assert that the expression
  itself is a sort. `instL` specializes header kinds at the actual translated
  universes, and `weak0` inserts closed header kinds into arbitrary contexts.
  `TrExprS.constantKind` obtains the constant's actual type from its registered
  semantic lookup, strictly translated universe list and generic header kind.
  `saturatedIsType` follows every strictly translated application, retaining
  the actual function and argument typing rather than using unchecked inference.
  `isValidIndAppIdx.headerMatches` extracts the real head-equality and exact
  parameter-plus-index argument count. `isValidIndAppIdx.isType` composes those
  guards with the application theorem, including the native expression-equality
  translation interface rather than pretending Boolean equality is syntactic
  equality.
  `AcceptedConstructorTrace.isType` now proves constructor-source typehood:
  binder sources use their strict translation's existing sort-valued premises,
  while binder-free sources use the accepted terminal guard and header kind.
  `TrConstructor.typehoodWF` and `ConstructorSemanticReceipts.typesWF` close
  constructor WF from these receipts. `typesWFOfHeaders` obtains every semantic
  lookup automatically from the actual registered declaration and needs only
  matching native header heads and semantic header sort arities, not translated
  constructor inputs or constructor/return typehood assumptions.
  `CheckedHeaderContinuation.heads` retains the exact accepted native constant
  for every parent, including parameterized batches. `contextualKinds` derives
  exact zero-parameter sort arity for every translated header, not just the first,
  and transports earlier receipts through all later accepted index contexts.
  `contextualHeaderKind` packages a matching semantic member, native head and
  parameter-plus-index arity in the final typed reader context. The semantic
  constructor receipt retains the complete/incomplete header signature relation;
  `ConstructorSemanticReceipts.contextualHeaderKinds` transports those automatic
  receipts to every corresponding complete declaration member in the registered
  semantic environment without changing constructor lists or assuming equality
  of entire headers. These are contextual kinds, not empty-context kinds.
  `TrExprS.contextualConstantKind` specializes both the generic header kind and
  its well-formed auxiliary context at the actual strictly translated universe
  list. `SortArity.applyClosed` consumes the closed strict application spine
  in that context using ordinary typing weakening. `closedTypedIsType`
  strengthens only the resulting sort-valued typing back to the empty context;
  existential header-kind witnesses need not be strengthened. The saturated
  application, accepted return and constructor-trace contextual variants
  preserve strict function/argument typing throughout. Finally
  `ConstructorSemanticReceipts.constructorTypesWF` automatically proves
  constant WF for every constructor in the complete declaration, for all
  parameter counts and empty/nonempty batches, without caller-supplied header
  kinds, constructor translations or return/constructor typehood. It combines
  the existing positive-parameter result with the exact automatic zero-parameter
  receipts and the accepted trace. No reduction-pattern `VEnv.Params` premise
  or empty-context header-kind assumption is introduced. `TypedConstructorReceipts`
  retains this automatic WF proof, so its existing shadow, actual-stage, checked
  prefix and complete-run bridges now supply it without extra caller premises.
  Complete run fixtures also compose the theorem with the existing derived
  semantic receipts. The return fixture checks 18 formal contracts and audits
  24 sort-arity and ten return-typing declarations plus six constructor-WF
  compositions. Automatic batch WF inherits nine existing dependencies,
  including native local-context array/hash interfaces through `VContext.Δwf`;
  its audit uses that genuine earlier context-WF baseline as well as the
  contextual header receipts, not just the smaller `TrConstructor` input type.
  The semantic fixture additionally checks polymorphic nullary constructors in
  a mixed 1/0/2-index batch and verifies sort-valued inferred types for every
  accepted constructor while retaining the `Nat.zero` non-type control. Semantic
  positivity, recursor equations and complete inductive soundness remain open.
  No strong checker or native parent-closure contract is weakened, and no
  executable checker behavior changes. The return fixture passes twenty-four
  staging combinations in both actual and shadow environments. Nullary,
  indexed, dependent-index, parameterized, parameter-plus-index and polymorphic
  returns pass checked inference/type formation but reject sort-expression
  formation; under/oversaturation rejects, while ill-typed structurally valid
  indices fail checked inference. `ensureType` uses inference-only mode, so its
  acceptance alone does not supply strict argument-typing eligibility.
  Existing metatheory admissions remain inherited: the new theory lemmas use
  only `propext`, `Quot.sound` and existing `sorryAx`; return saturation also
  inherits `Classical.choice`, `Lean.Expr.eqv_eq` and
  `Lean.Level.instLawfulBEqLevel` through existing translation interfaces.
  No new axiom or admitted proof is added.
- `Verify.InductiveConstructorRegistration` connects those automatic constructor
  WF receipts to fresh semantic constant registration and exact native constructor
  metadata. `VInductDecl.constructorHeaders` flattens the complete declaration;
  `TrInductDecl.constructorModels` and `constructorNames` retain each source
  constructor's translation and exact name correspondence. Strong parameter-prefix
  models imply that every native parameter is an FVar and the parameter list is
  duplicate-free. `ConstructorSemanticReceipts.constantsFresh` transports missing
  actual/shadow native constructors through the existing strong shadow `TrEnv`,
  rather than assuming a weaker environment interface.
  `VEnv.addConstructorHeaders.exists` constructs a successful semantic extension
  from fresh, globally distinct names. `registeredConstants` derives those facts
  from accepted native registration, combines automatic constructor type WF with
  the existing semantic registration WF theorem, and derives exact native metadata
  using checked arities and the model's parameter facts. No caller-supplied
  constructor typehood, semantic freshness, name distinctness or arity premise is
  added. `ConstructorConstantRegistration` retains the exact semantic registration,
  semantic WF/ordering and monotone extension, unchanged definitional equations,
  native map WF, exact old-value preservation, and native constructor metadata at
  the original universe list. `constructorConstant` pairs each accepted source's
  exact `.ctorInfo` lookup with the matching semantic constant lookup and its
  `TrConstant` proof in the extended semantic environment.
  The checked-prefix `constructorConstantContinuation` and complete
  `AddInductive.run.constructorConstantContinuation` supply these receipts without
  extra semantic-WF assumptions, preserving the original strong initial context,
  canonical-annotation, primitive/safety and native parent-closure restrictions.
  The complete-run theorem records the reached constructor-registration stage;
  it does not assert that the final recursor-extended environment satisfies a full
  `TrEnv`, nor invent inductive histories while the existing `AddInduct` relation
  remains uninhabited. Semantic positivity, recursor types/equations and complete
  inductive/frontend/prelude soundness remain open. No executable checker changes,
  new axioms or admitted proofs are introduced.
  `tests/InductiveConstructorRegistration.lean` checks 21 generic registration,
  parameter/model/name contracts, all receipt fields, paired native/semantic
  lookup and both acceptance bridges; nine concrete `Bool`/`Nat` semantic controls
  retain exact lookup, unchanged equations and rejection of repeated registration.
  Forty native staging controls inspect every constructor metadata field, exact old definitions,
  old constructors and inductive headers, distinct FVar parameters, actual/shadow
  freshness and full runs. They cover empty/constructor-free, recursive/higher-order,
  dependent-field, dependent/multiple-parameter, parameter-plus-index, polymorphic
  parameter and mutual mixed 1/0/2-index batches in both safeties and primitive
  modes. Existing-name, own/other-header and cross-parent duplicate collisions
  pass checking but reject registration; within-parent duplicates reject checking
  as well. Runtime controls do not fabricate semantic contexts. Exhaustive owned
  declaration audits compare against genuine earlier context, constructor-WF,
  metadata, freshness, arity and acceptance interfaces, not the new receipts
  themselves: all 18 theory and 39 registration-module owned declarations are
  audited. The new existence proof uses only `propext` and `Quot.sound`;
  structural list/model/name lemmas inherit the existing four translation-type
  dependencies, including `sorryAx`. Registration inherits 15 earlier dependencies
  and the checked-prefix/full-run bridges retain the earlier 31-dependency
  checker/metatheory baseline.
- `Verify.InductiveRecursorSignatureInputs` derives the semantic constant inputs
  needed by recursor parent/constructor applications from accepted constructor
  registration, without caller-supplied source typehood or constant-head typing.
  `RecursorConstantInput` records strict source translation and sort-valued
  typehood, strict constant translation and typing at that same semantic source.
  `headerInput` and `constructorInput` supply it for every registered parent and
  constructor, at any exactly translated native universe list of the original
  arity and in any well-formed reached mixed context. This includes added
  elimination universes, reordered or concrete instantiations, original
  parameters, dependent locals and lets; no universe-Nodup, zero-parameter or
  empty-reached-context restriction is added. The proof specializes the closed
  source translation and registered constant type at the actual translated
  levels, weakens both into the same mixed context, and aligns the strict
  source's recovered semantic type by the existing definitional-equality
  interface. It does not confuse checked inference with type formation or
  assume the instantiated semantic signature is syntactically unchanged.
  `alignedType` supplies constant typing at an existing exact source translation;
  `applyParameters` composes genuine per-domain typed argument receipts rather
  than assuming parameter names alone imply universe/domain compatibility.
  The field-trace initial-source lemma and `registeredConstructorApplication`
  directly derive the earlier constructor-field application's head-translation
  and head-typing premises from registration and its reached typed endpoint.
  `RecursorSignatureInputs` collects these universal parent/constructor inputs
  for the full batch. Checked-prefix and complete-run acceptance bridges derive
  it with the original strong context, canonical-annotation, primitive/safety and
  native parent-closure contracts unchanged. The semantic environment remains
  the reached signature-registration stage, not a claimed final actual `TrEnv`.
  Signature eligibility is now automatic for all parameter counts. The following
  parameter-prefix module supplies compatible arguments and nonzero-parameter
  field endpoints at the original source universes; universal parameterized
  parent/index eligibility, universe-reindexed parameter applications, reached normalization
  and annotation support, motive/IH/minor domain formation, recursor equations
  and final inductive registration remain separate obligations. In particular,
  the existing field-only endpoint representation is not silently treated as a
  nonzero-parameter recursor proof. No executable checker change, new axiom or
  admitted proof is introduced.
  `tests/InductiveRecursorSignatureInputs.lean` checks 15 formal contracts,
  including all input proof fields, parameter application, endpoint composition,
  universal batch eligibility and both acceptance bridges. Its native controls
  check 472 exact inferred parent/constructor types and sort-valued source/residual
  typehood in both constructor-registered and complete-run environments, both
  safeties, and original/dependent-local/let contexts. Empty/constructor-free,
  recursive/higher-order, multiple/dependent-parameter, polymorphic-parameter,
  mutual mixed 1/0/2-index and two-universe batches cover original, elimination,
  concrete and reversed universe lists. Wrong universe arity, unbound universes
  and incompatible original-parameter instantiations are rejected. Runtime
  controls do not fabricate semantic contexts. Exhaustive owned-declaration
  audits use genuine earlier instantiation, constant-WF, mixed-context weakening,
  uniqueness, parameter application, field application and acceptance interfaces,
  not the new input type itself; all 34 owned declarations are audited. Universal
  batch inputs inherit 12 earlier dependencies, and both acceptance bridges
  retain the earlier 31-dependency checker/metatheory baseline. All existing
  metatheory admissions remain
  inherited, with no additional caller typehood or head-typing premise.
- `Verify.InductiveRecursorParameterPrefixes` closes the accepted constructor
  parameter-consuming prefix before translating its actual recursor field suffix.
  The strengthened `translatedReusedHeaderParameterArgument` exposes genuine
  parameter-domain typing from the accepted stored-type and definitional-equality
  calls; the earlier opening theorem retains its API as a projection.
  `AcceptedConstructorTrace.parameterPrefix` derives `TypedParameterArguments`
  together with a strict residual source translation and an exact native prefix.
  Its completed index is `max initialIndex stats.params.size`; an unchecked early
  stop cannot supply this accepted receipt. `ConstructorSemanticReceipts` derives
  these prefixes for every accepted constructor without caller-supplied argument
  typing. Native suffix extraction preserves the actual field trace and its
  annotation support without allocating locals or changing readers.
  `ConstructorConstantRegistration.parameterizedFields` transports the automatic
  receipts through the semantic registration extension and a genuine reached
  mixed-context insertion, then translates the actual field suffix after all
  parameters. `ParameterizedCtorFieldModelEndpoint` retains the complete typed
  parameter application, residual translation, final model well-formedness and
  native agreement, terminal translation and field abstraction extension.
  Its application theorem types `mkAppN (mkAppN head stats.params) fields`;
  `constantInputApplication` derives the head premises from the registered
  constant input. This is a separate parameter-plus-field endpoint, not a change
  to the earlier field-only application's meaning. All accepted parameter counts
  are supported at the original source universes. Reindexing compatible parameter
  applications into fresh elimination universes, automatic parent-header
  parameter receipts, reached annotation support, complete motive/IH/minor formation, recursor
  equations and final actual inductive histories remain open. The strong initial
  checker interface and actual/shadow boundary are unchanged; no final actual
  `TrEnv`, executable checker change, new axiom or admitted proof is introduced.
  `tests/InductiveRecursorParameterPrefixes.lean` checks 16 prefix, suffix,
  environment transport, registration and endpoint contracts, exhaustively audits
  all 50 owned declarations against genuine earlier foundations, and separately
  audits the strengthened shared argument helper. Its 152 native controls compare
  the full traversal with the exact remaining-fuel suffix in constructor-registered and
  reached actual motive readers, checking terminal, field/recursive-field arrays,
  name generator, every local declaration, residual typehood and complete
  constructor application typing. Empty/constructor-free, zero/one/two-parameter,
  dependent/polymorphic, parameter-plus-index and mutual batches run under both
  safeties and primitive modes. Unchecked incomplete prefixes retain no accepted
  constructor eligibility; runtime controls do not fabricate semantic contexts.
- `Verify.InductiveRecursorIndexParameters` handles the actual parameter-consuming
  recursor index prefix, including each native parameter-opening WHNF call, then
  composes the existing typed index-only suffix. `RecursorIndexParameterPrefix`
  retains the exact intermediate normalized expressions and unchanged reader;
  completion reaches `max initialIndex stats.params.size`. A completed native
  trace supplies its prefix. `completeParameters` also derives completion from
  the real raw leading-binder bound and free-variable parameter receipts, using
  the existing native WHNF/instantiation arity bounds rather than assuming an
  unchecked early stop consumed all parameters. Annotation and index-normalization
  receipts are restricted to the actual remaining suffix without reallocating
  any index or changing the source reader.
  `IndexParameterNormalizationSupport` supplies the missing parameter-opening
  normalization semantics: the older index-normalization receipt deliberately
  skips those heads and is not silently treated as sufficient. An aligned strong
  checker with its actual initial-state WF derives the new support from accepted
  WHNF calls; sort telescopes have a separate structural derivation. The generic
  proof is not restricted to identity WHNF, sort telescopes, zero parameters or
  empty contexts. `normalizedTranslation` consumes genuine
  `TypedParameterArguments`, uses earlier forall injectivity to align parameter
  domains through definitional equality, and retains residual strict translation
  and its equality to the original typed application result. It does not assume
  the intermediate semantic type stays syntactically unchanged.
  `ParameterizedRecursorIndexModelEndpoint` retains the normalized parameter
  prefix, original typed argument application, actual translated index suffix,
  final model WF/native agreement and index abstraction extension. Application
  types the exact `mkAppN (mkAppN head stats.params) indices`. A translated native
  sort terminal yields saturated parent `IsType`; registered constant inputs
  remove caller head-translation/typing assumptions. Exact terminal universe
  mapping and the existing annotation-universe support compose a genuine
  `RecursorMajorOpening`; its existing mixed-context/index abstraction machinery
  now also forms the actual motive domain through the parameterized endpoint.
  No zero-parameter restriction is retained on these new major/motive adapters.
  The strong-checker CPS theorem covers the actual `loopArgs1` continuation and
  derives parameter completion from source arity rather than a caller-supplied
  final-index bound. This is a separate parameter-plus-index endpoint, preserving
  the earlier index-only application's meaning.
  Compatible parent-header argument receipts are derived per accepted checking
  trace by the following module, with original-universe batch aggregation derived
  below, including compatible fresh-elimination-universe transport. Reached annotation/
  index-normalization support and native
  sort-terminal eligibility for every accepted batch remain to be derived.
  The new adapters do not fabricate a strong checker for the final actual
  inductive environment, weaken the initial `VContext` interface, claim a final
  actual `TrEnv`, or complete recursor equations/inductive histories.
  `tests/InductiveRecursorIndexParameters.lean` checks 22 native/semantic prefix,
  strong checker/CPS, endpoint application/typehood, index abstraction and
  major/motive formation contracts, and exhaustively audits all 57 owned
  declarations against genuine earlier WHNF, forall injectivity, typed
  application, mixed context, annotation and motive foundations. Its 88 native
  controls cover empty and constructor-free batches, zero/one/two/dependent/
  polymorphic parameters, indexed and mutual families, and let/beta/metadata
  wrappers after the final explicit parameter. Both safeties/primitive modes and
  initial/reached actual motive readers compare exact remaining fuel, index
  arrays, name generators, every local declaration, residual typehood and
  saturated parent application typing, including 56 nonidentity parameter-opening
  WHNF reductions. All 72 wrong-domain parameter arrays remain entirely free
  variables and complete unchecked native traversal, but reject typed application
  eligibility. Unchecked early stops retain no complete-prefix/header eligibility.
  Wrappers hiding a declared raw parameter binder remain excluded by the previously
  verified public preprocessing guard, not mistaken for a new full-frontend
  discrepancy. Runtime controls do not fabricate semantic contexts; no executable
  checker change, new axiom or admitted proof is introduced.
- `Verify.InductiveHeaderParameterApplications` derives compatible parent-parameter
  application inputs from actual accepted header checking, including both freshly
  allocated first-header parameters and stored/reused parameters of later headers.
  `TypedParameterApplications` adds genuine input-type definitional-equality
  conversions to the earlier syntactic `TypedParameterArguments` representation;
  the old representation embeds without changing its meaning. Application,
  concatenation, environment extension and genuine mixed-context insertion retain
  the actual argument expressions and semantic values. Conversion does not assume
  a normalized function type is syntactically unchanged or justify arguments
  merely from their free-variable names.
  `CheckedHeaderTrace.parameterApplications` extracts arguments for every remaining
  declared parameter, together with an actual reached strong checker, aligned
  native reader, initial-state WF and chronological local-context extension. Fresh
  parameter typing comes from the checked annotation-domain opening and its real
  new local model; reused parameter typing comes from accepted stored-type and
  definitional-equality calls. Actual parameter-opening WHNF equalities connect
  successive function types. Index branches allocate their existing typed locals
  but do not consume them as parameters. Parameter-array append preservation and
  unchanged arrays after completion retain exact native order and count.
  `parameterApplicationsFromSource` derives the original strict header translation
  from the actual source guard/check, restores the original signature through its
  initial WHNF equality, and returns a `HeaderParameterApplicationReceipt` with
  no caller-supplied parameter-domain typing or source typehood. The CPS theorem
  follows the actual header binder loop and terminal `ensureSort` before handing
  this automatic receipt to its continuation. It supports every parameter count,
  both first and reused headers, dependent domains, original source wrappers and
  nonempty reached contexts under the unchanged strong checker interface.
  `HeaderParameterApplicationInput` transports through semantic environment
  extensions and reached mixed-context insertions. The registered signature
  adapter `RecursorConstantInput.applyHeaderParameters` aligns its original source
  type and applies the actual native parameter array without caller head typing.
  `withStats` transports the input across metadata updates with the unchanged
  parameter array. The following batch module retains these inputs through the
  complete header/constructor-registration continuation, with compatible fresh-universe
  transport derived below. Composition with normalized recursor parent traces remains.
  No universal fresh-universe normalized-index eligibility, final actual `TrEnv`,
  recursor equations or completed inductive frontend theorem is claimed.
  `tests/InductiveHeaderParameterApplications.lean` checks 23 conversion-aware
  application, prefix, strong checker, original-source, continuation, input
  transport and registered-head contracts. It exhaustively audits all 85 owned
  declarations against genuine earlier application/weakening, checked header
  models/openings, accepted source/WHNF and native guard foundations. Generic
  application inherits seven earlier dependencies, accepted trace derivation
  inherits 28, and original-source/CPS bridges retain the earlier 31-dependency
  checker/guard baseline, including existing metatheory admissions. Its 264 native
  controls compare exact inferred partial parent application types with normalized
  residual signatures and strictly check residual sort-valued typehood. Header-
  registration/full-run environments, original/local/let contexts and both
  safeties/primitive modes cover empty/constructor-free, zero/one/two/dependent/
  polymorphic parameters, indexed/mutual families, convertible parameter domains
  and post-parameter let/beta/metadata wrappers. There are 168 nonidentity
  parameter-opening WHNF results and 216 rejected wrong-domain all-free-variable
  arrays; incompatible reused-header domains reject in both kernels. Runtime
  controls do not fabricate semantic contexts. No executable checker change,
  new axiom or admitted proof is introduced.
- `Verify.InductiveHeaderApplicationBatch` closes original-universe compatible
  parent-parameter aggregation through accepted complete header and constructor
  registration. The existing `CheckedHeaderContinuation` now retains strict
  original-source, genuinely typed parameter inputs for every parent in its
  actual final mixed model, including fresh first-header parameters, reused later
  parameters, dependent domains and accumulated indices. Its traversal selects
  the checker delivered by the application receipt; native context alignment
  identifies allocated identifiers without assuming two semantic checkers equal.
  First-header parameter/ambient separation and all earlier strong reader/state,
  chronological history, source-WF, count, kind and shadow interfaces remain.
  `ConstructorConstantRegistration.parentParameterInput` monotonically extends
  these automatic inputs to the registered semantic environment, and
  `parentParameterModelWF` derives their model WF there.
  `parentParameterApplications` constructs genuine registered parent heads and
  proves every actual `mkAppN stats.indConsts[parent]! stats.params` translated
  and typed at its conversion-aware residual. No caller-provided argument/domain
  typing, source typehood, original-level mapping or head typing is required.
  Canonical native universe substitution can normalize level syntax, so the head
  adapter does not assert that original-level substitution is syntactically the
  identity. It instead proves original nominal-level translation/instantiation
  invariance and rebuilds the original source translation under semantic level
  instantiation, including the genuine existing projection-instantiation boundary.
  The accepted helper-program and complete-run bridges automatically package this
  entire `HeaderParameterApplicationBatch` alongside actual registration receipts
  under their unchanged strong entry checker, ordinary-safety and native-parent
  closure premises. Empty batches are vacuous; exact canonical levels are retained
  only when a parent exists, including the earlier empty-batch default path.
  Compatible fresh-elimination-universe transport is derived by the following module.
  Normalized recursor parameter/index composition, terminal sort eligibility and full
  recursor/frontend closure remain. No final actual `TrEnv` is fabricated or weaker
  checker substituted.
  `tests/InductiveHeaderApplicationBatch.lean` checks 11 formal contracts and audits
  all 119 continuation and 12 new batch-module declarations against genuine earlier
  foundations. Registered batch application inherits seven dependencies; accepted
  traversal and complete-program bridges retain the earlier 31-dependency baseline,
  including existing metatheory admissions. Its 240 native controls cover exact
  constructor-registered/full-run parent application types, strict residual typehood,
  original/local/let contexts, both safeties/primitive modes, differing accumulated
  mutual index counts, dependent/polymorphic parameters and convertible wrapped
  domains. It exercises 144 nonidentity parameter-opening normalizations, a genuinely
  nonidentity original-universe self substitution, and 192 rejected incompatible
  all-free-variable arrays; incompatible later-header domains reject in both kernels.
  Runtime controls do not fabricate semantic contexts. No executable checker change,
  new axiom or admitted proof is introduced.
- `Verify.InductiveHeaderParameterUniverses` transports compatible checked parent
  parameter inputs and applications into the actual `getRecLevelParams` universe
  context, including prepended fresh elimination parameters and the unchanged
  nonparameter-elimination branch. `UniverseNameExtension` records genuine nominal
  name inclusion, and derives the semantic level mapping and its WF from native
  parameter lookup. Strict and conversion-aware source translations reindex semantic
  universes without changing the native source, native constant levels or parameter
  arrays; no syntactic universe-substitution identity is asserted. The generic
  transport also supports reordered and extended name lists without adding a
  universe-distinctness premise.
  `MLCtx.reindexLevels` preserves exact native local declarations, names, dependent
  domains and let values while instantiating their semantic counterparts. It derives
  target model WF; `TypedParameterApplications`, header inputs and entire registered
  batches transport with genuine typing and all input conversions preserved.
  Existing strong `VContext`s reindex at the same native/semantic environment,
  retaining their real `TrEnv`, safety, primitive contracts and fuel. Reader alignment
  and reset-state WF follow automatically; warm caches are not transported or assumed.
  Registered whole-batch application/model-WF adapters specialize to every selected
  elimination level, and `run.headerParameterUniverseContinuation` derives these
  receipts for every parent and every recursor universe context from accepted ordinary
  complete runs under the unchanged strong entry checker/native-parent premises.
  It does not replace original parameter universes with the elimination universe,
  certify the selected name's freshness or elimination-sort eligibility, fabricate
  a strong checker or `TrEnv` for the final actual inductive environment, or discharge
  the remaining normalized-index support and recursor/frontend closure obligations.
  `tests/InductiveHeaderParameterUniverses.lean` checks 23 nominal-level, strict/
  conversion-aware translation, native mixed-context, model-WF, strong checker/reset,
  registered batch and complete-run contracts. Its exhaustive audit checks all 53
  owned declarations against genuine earlier level-instantiation, model, reset,
  application and accepted-run foundations, rejecting owned axioms. Generic semantic
  transport inherits four dependencies, strong reset ten, and accepted complete runs
  retain the earlier 31-dependency baseline, including existing metatheory admissions.
  Its 480 native controls compare exact partial-parent inferred types and strictly
  check residual typehood under original, fresh-prefix, appended and reordered
  universe contexts, constructor-registered/full-run environments, original/local/
  let contexts, both safeties/primitive modes, dependent parameters and differing
  accumulated mutual indices. They reject 288 incompatible elimination-universe
  substitutions and 480 contexts omitting original nominal universes. Runtime controls
  do not fabricate semantic contexts. No executable checker change, new axiom or
  admitted proof is introduced.
- `Verify.InductiveHeaderIndexApplications` composes conversion-aware checked
  header applications with the actual normalized recursor parameter/index trace.
  `TypedParameterApplications.emptyResultEquality` and `consView` invert arbitrary
  input-conversion chains, including zero arguments, without replacing genuine
  domain typing by a free-variable or syntactic-argument assumption.
  `RecursorIndexParameterPrefix.normalizedApplications` retains source-to-forall
  conversion and transports the residual through every accepted parameter-opening
  WHNF. `HeaderRecursorIndexModelEndpoint` fixes both source and result semantics,
  so an already-typed partial parent feeds the translated index suffix directly.
  The earlier syntactic endpoint embeds unchanged into this new endpoint.
  Context, partial/head/constant application and sort-terminal typehood adapters
  preserve the actual final native reader, translated mixed context and index array.
  Strong-checker entry adapters derive original-header source alignment and all
  parameter normalization support from accepted native WHNF. Whole-batch and actual
  `mkRecInfos.loopArgs1` CPS adapters select the checked input and typed partial
  parent automatically, then pass the complete parent parameter-plus-index
  application to the continuation without caller-supplied head/domain typing.
  They still require genuine checker/alignment/reset WF, reached annotation and
  index-normalization support, reservation, initial normalization and parameter
  completion/source arity; typehood additionally needs a sort terminal. They do not
  fabricate a checker for the final actual environment or prove unconditional
  normalized accepted-batch, recursor or inductive frontend closure.
  `tests/InductiveHeaderIndexApplications.lean` checks 15 formal contracts, including
  two explicit double-conversion controls. Its exhaustive audit checks all 15 owned
  declarations against genuine earlier foundations, rejecting owned axioms. Generic
  normalization inherits eight dependencies and checker/batch/CPS bridges 28,
  including existing metatheory admissions. Its 1248 native controls compare exact
  remaining-fuel suffixes, index arrays, name generators, every local declaration,
  residual and saturated parent typing/typehood, with 768 parameter-opening WHNF
  changes, 288 original-header changes and 864 rejected wrong-domain free-variable
  arrays. They cover zero/one/two/dependent parameters, differing mutual index
  counts, original/fresh/reordered universes, registered/full-run environments,
  original/local/let contexts, both safeties/primitive modes and post-parameter
  let/beta/metadata wrappers. Runtime controls do not fabricate semantic contexts.
  No executable checker change, new axiom or admitted proof is introduced.
- `Verify.InductiveIndexCheckerClosure` closes reached annotation peeling and
  index-opening WHNF directly in genuine strong checker models. The unrestricted
  forall-opening bridge uses the earlier conversion-aware domain/body peeling
  theorem, deriving the actual stored domain, dependent opened body, native binder
  position and scope frame without a literal-uniform annotation universe premise.
  `RecursorIndexTrace.checkedIndexModels` extends the real entry checker through
  every actual peeled index declaration and derives each accepted normalization
  from that reached checker. It retains the real `TrEnv`, environment/universe
  equalities, reader alignment, cold reset-state WF, exact mixed-model extension,
  selected index array and the existing translated trace. It neither fabricates
  universal legacy support predicates nor asserts their literal uniformity, which
  can genuinely fail for accepted nested annotations with equivalent universes.
  `HeaderRecursorIndexCheckerEndpoint` adds the final genuine checker to the earlier
  conversion-aware result-indexed model endpoint. `headerCheckedModels`,
  `checkedHeaderBatch` and the actual `mkRecInfos.loopArgs1.checkedHeaderBatchTrace`
  compose original-header WHNF, checked parameter consumption and index traversal
  without caller-supplied annotation/index-normalization support or head/domain
  typing. Partial-parent application and sort-terminal typehood adapters expose
  the resulting strict translations and typing in that actual final checker.
  The entry checker, alignment/reset WF, context reservation, disjoint native versus
  reset checker name prefixes, canonical annotation signatures/definitions, initial
  normalization and parameter completion/source arity remain genuine premises.
  Terminal-sort eligibility and subsequent motive/recursor/frontend closure remain
  unproved: source typehood plus stopped traversal does not imply a sort terminal.
  This does not manufacture a checker for the final actual inductive environment;
  the entry checker's real native/semantic environment correspondence is preserved.
  Legacy support-based APIs and their explicit premises remain unchanged.
  `tests/InductiveIndexCheckerClosure.lean` checks 11 interface contracts and an
  explicit impossibility of literal universe uniformity for an accepted nested
  domain. Its exhaustive genuine-prior-foundation audit checks all 12 owned
  declarations, including generated helpers, and rejects owned axioms. Unrestricted
  native opening inherits eight dependencies and checked-trace/batch/CPS bridges
  28, including existing metatheory admissions. Its 2016 native controls check exact
  remaining fuel, indices, name generators, every local declaration, actual stored
  peeled domains, residual and saturated parent typing/typehood, including 1248
  parameter-opening WHNF changes, 288 original-header changes and 960 nonidentity
  stored-domain peelings. They reject 1440 unchecked wrong-domain free-variable
  arrays, 16 malformed/nonsort header controls and eight corresponding native
  declarations; four genuinely type-valued stopped native traversals retain no
  terminal-sort eligibility. Coverage includes all four annotation wrappers with
  nonuniform equivalent universe chains, metadata barriers, dependent index domains,
  zero/one/two/dependent parameters, differing mutual index counts, original/fresh/
  reordered universes, registered/full-run environments, original/local/let contexts,
  both safeties/primitive modes and post-parameter let/beta/metadata wrappers.
  Runtime controls do not fabricate semantic contexts. No executable checker change,
  new axiom or admitted proof is introduced.
- `Verify.InductiveHeaderResidualKinds` retains the semantic sort arity of checked
  partial parent applications for every accepted header, including nonzero fresh
  and reused parameters. `CheckedHeaderTrace.parameterApplicationsWithKind` proves
  both the earlier conversion-aware application receipt and the remaining index
  sort arity from the actual accepted terminal `ensureSort` call. After parameter
  completion, an index-only view reuses the earlier kind proof without changing
  native domains or normalization calls. Fresh and reused parameter branches
  preserve the result kind; index-context growth transports it with the receipt.
  `parameterApplicationsFromSourceWithKind` fixes the receipt's `indexArity` to the
  actual native index count. Legacy application-producing theorem signatures remain
  available as projections of these stronger proofs.
  `CheckedHeaderContinuation.parameterApplicationKinds` now retains the paired
  checked input/result kind for all parents, not just the earlier zero-parameter
  whole-header kind fragment. The actual private header loop transports earlier
  parents' kinds across later shared parameter/index context growth and records the
  selected parent's exact count. Registered kinded batches and accepted complete-run
  continuations derive typed partial parents and those kinds automatically, including
  compatible fresh elimination/reordered universe contexts and exact native arrays.
  Generic conversion-aware argument consumption and translated index traces reduce
  sort arity through dependent instantiation, domain peeling and actual accepted WHNF.
  `parentTypehoodOfKind` and `checkedHeaderBatchTypehood` derive saturated actual
  parent typehood from the resulting zero-arity sort conversion, without a syntactic
  native terminal-sort premise or caller-supplied head/domain typing.
  The actual selected index count must still equal the stored native header index
  count; unconditional normalized header/recursor count alignment, subsequent major/
  motive/recursor closure and complete inductive frontend verification remain open.
  These adapters preserve genuine checker/alignment/reset, reservation, canonical
  annotation and original-normalization premises, and do not manufacture a strong
  checker for the final actual inductive environment. Mere source typehood or an
  unchecked stale count is not a kinded batch receipt.
  `tests/InductiveHeaderResidualKinds.lean` checks 15 interface contracts plus an
  explicit nonuniform-universe impossibility control. Its exhaustive audit covers
  all 226 owned declarations in the two strengthened modules and the new bridge
  (90 parameter-application, 125 continuation and 11 residual-kind declarations),
  against genuine unchanged earlier foundations, rejecting owned axioms. Strong
  trace kinds inherit 28 dependencies and accepted-source/complete-run adapters 31,
  including existing metatheory admissions. Its 2208 native controls check exact
  stored index counts, residual/saturated parent typing/typehood and native contexts,
  with 1248 parameter-opening WHNF changes, 288 original-header changes and 960
  stored-domain peelings. They reject 1920 typed underapplications at typehood,
  1920 overapplications, 2208 unchecked stale-count traversals at count eligibility,
  1536 wrong-domain free-variable arrays, 16 malformed/nonsort header controls and
  eight corresponding native declarations. Four typed stopped traversals still
  acquire no terminal-sort eligibility. Empty/constructor-free, zero/one/two/
  dependent parameters, dependent indices, differing mutual counts, compatible
  universes, registered/full-run environments, original/local/let contexts, both
  safeties/primitive modes and all annotation/normalization wrappers are covered.
  Runtime controls do not fabricate semantic contexts. No executable checker change,
  new axiom or admitted proof is introduced.
- `Verify.InductiveParentCheckerClosure` derives actual major and motive binder
  models from accepted kinded parent applications, including nonzero fresh/reused
  parameters and normalized dependent index domains. `RecursorMajorOpening.ofTypehood`
  uses unrestricted typed annotation peeling, without a uniform-universe premise.
  `HeaderRecursorIndexCheckerEndpoint.parentModelStepOfKind` obtains parent typehood
  from the residual semantic sort arity, then derives the exact native major domain,
  selected-index/major motive abstraction and both typed binder models automatically.
  No caller-supplied head/domain typing, literal terminal sort or model support
  predicate is required. `parentCheckerOfKind` and `checkedHeaderParent` retain the
  genuine index checker and build a genuine final `VContext` aligned with the actual
  motive reader, including its existing native/semantic environment correspondence,
  well-formed mixed context, exact native allocations and a cold reset state.
  Generator-prefix preservation discharges fresh reset namespace reservations;
  selected identifiers are exactly the native index array followed by major/motive.
- `Verify.InductiveParentPassCheckerClosure` transports every checked input, partial
  parent typing and residual kind through actual index/major/motive mixed-context
  extensions. `RecursorParentPassTrace.checkedModels` consequently derives a genuine
  final checker for the complete actual parent pass and preserves the whole kinded
  header batch for later parents/recursor work, including empty and mutual batches.
  It needs only numeric parameter-completion/index-count alignment for each reached
  traversal, not the older zero-parameter annotation/normalization/typing support
  predicates. `RecursorParentPassCountAlignment` records precisely those remaining
  numeric obligations; it does not prove them or manufacture normalized traversals.
  Unconditional normalized header/recursor count alignment remains open: the existing
  WHNF correctness interface proves conversion, not head-normal-form completeness,
  so a stopped non-forall traversal cannot be identified with a terminal sort from
  that interface alone. This is not a kernel discrepancy. Elimination-level mapping,
  entry checker/alignment/reset WF, reservation/canonical annotations and the actual/
  shadow environment boundary remain explicit; no strong checker is fabricated for
  the final actual inductive environment. Minor/recursor/frontend closure remains open.
  `tests/InductiveParentCheckerClosure.lean` checks eight contracts and exhaustively
  audits all 24 declarations owned by the new modules (10 single-parent, 14 parent-pass)
  against unchanged earlier foundations, rejecting owned axioms. Single-parent and
  whole-pass checked adapters inherit 28 dependencies, including existing metatheory
  admissions, without introducing new ones. Extended residual-kind native controls
  check 2208 actual major domains/allocations and 4416 motive domains/allocations and
  saturated applications at zero/fresh elimination levels, with exact native readers,
  dependent index arrays and rejected unmapped universes. 4224 complete native parent passes
  additionally preserve every original partial/saturated parent and all motives in
  the final reader, and reject wrong-domain majors. The previous stale-count,
  under/overapplication, wrong-parameter and malformed/nonsort controls remain.
  Runtime controls do not fabricate semantic contexts. No executable checker change,
  new axiom or admitted proof is introduced.
- `Theory.SortArityCounts` proves uniqueness of semantic sort arity in well-formed
  environments/contexts and positivity of a literal semantic forall's arity. Counts
  therefore cannot be supplied inconsistently through conversion or dependent
  domain/context changes. `Verify.InductiveIndexCountClosure` uses those facts to
  prove that a translated actual index trace cannot overrun its accepted residual
  arity, including dependent instantiation, stored-domain peeling and accepted WHNF.
  `remainingKind` retains the exact unconsumed sort arity at the final context.
  `checkedHeaderIndexBound` selects the accepted whole-batch input and derives the
  native stored-count upper bound without a caller-supplied index-count equality.
  Entry checker/alignment/reset, reservation/canonical annotations, original source
  normalization and parameter completion remain explicit as in the earlier endpoint.
  `exactCountOfSortKind` proves exhaustion from a zero-arity terminal kind;
  `HeaderRecursorIndexCheckerEndpoint.exactCountOfSortCheck` derives that kind from
  an actual accepted terminal `ensureSort` call in the genuine final checker.
  `checkedHeaderParentOfSortCheck` consequently derives exact stored/native index
  agreement and actual major/motive checker closure, without a numeric count premise
  or literal native terminal-sort premise. It still requires that real sort-check
  acceptance; the recursor frontend does not perform this extra check, and acceptance
  has not yet been derived automatically from its reached normalization receipts.
  Unconditional parameter completion and normalized count alignment remain open.
  `tests/InductiveIndexCountClosure.lean` checks six interface contracts and audits
  all 13 owned declarations (three count-theory, ten index-count bridge) against
  genuinely unchanged earlier foundations, rejecting owned axioms. Count-theory
  proofs inherit three dependencies, trace bounds/kinds seven and checked adapters
  28, including existing admissions but no new ones. A formal conversion-only method
  contract countermodel retains a metadata-hidden forall while satisfying the
  existing `Methods.WF` specification. It is explicitly not the actual normalizer
  and supplies no positive frontend/checker receipt: output head completeness must
  be proved for the implementing normalizer, not inferred from that contract alone.
  The fixture passes 64 actual normalized zero/one/two/three-index traversals and
  accepted terminal sort checks under both safeties/primitive modes, with exact-fuel
  rejection and unchecked stale-array controls. Thirty-six typed hidden unchecked
  traversals stop below their normalized count and reject terminal-sort acceptance;
  twelve nonliteral zero-arity terminals retain real sort-check acceptance.
  The residual-kind fixture now checks actual terminal-sort acceptance rather than
  assuming literal terminal syntax across its 2208 parent applications, 4416 motives
  and 4224 complete native parent passes. These are proof-boundary controls, not a
  kernel discrepancy. Runtime controls do not fabricate semantic contexts or strong
  checkers. No executable checker change, new axiom or admitted proof is introduced.
- `Verify.InductiveHeaderInferenceTransport` transports the complete actual
  `TypeChecker.Inner.inferType'` program, in both inference-only and checking
  modes, from reached helper/callback receipts across header shadows. The raw
  readers have equal local contexts, safety and universe parameters; eager flags
  and fuel configurations may differ when the reached method contracts hold.
  `NativeInferEntryReceipt` records the native loose-variable guard and selected
  inference-cache miss. `NativeInferReachable` admits only cold metadata/source
  children, checked function children, and checked arguments reached after the
  actual accepted function-inference and forall-normalization prefixes.
  `NativeInferCallbacks` separates inference-only applications from checked
  applications, demands normalization only after accepted function inference and
  only when the function type is not already a forall, and demands comparison
  only after the actual accepted argument type/state. Eager comparison uses the
  native argument-head/arity test and the scoped updated readers, preserving the
  equivalence-manager insertion performed by the actual `isDefEq` wrapper.
  Lambda/forall/let helper transport and projection helper transport are
  explicit obligations at their reached inputs; the telescope/projection modules
  below derive these from reached method receipts and metadata/freshness frames.
  None of these theorems assumes new-header projections work in an axiom shadow.
  `NativeAppReachable`, `NativeAppCallbacks` and `NativeInferAppCallbacks` derive
  complete native `inferApp` transport, including its actual argument-array
  loop, delayed reverse-range instantiation, direct-forall steps and normalized
  boundaries. The next normalization receipt is required only after an accepted
  earlier boundary result/state; all index movement is the existing native loop.
  Constant inference follows from header signatures and matching reader fields;
  literal checks require only native signature presence, not equal ignored
  constant records. `nativeInferBody` and `inferType'.entry_eq` factor the actual
  computation without changing the executable checker. The original native
  bound-variable panic fallback is retained rather than replacing it with a
  different exception or using the expression-cache interface axiom to assert
  it is unreachable. Every owned declaration excludes admissions and expression
  or persistent-map interface axioms; no panic-freedom claim follows from this
  raw transport theorem.
  Native inference rejects loose variables before consulting either cache.
  Closed cache hits bypass body checks, while every successful cold body inserts
  into exactly the selected cache, retaining every other state field. Unlike
  normalization, metadata wrappers are separately read and saved by inference;
  an outer hit bypasses its child. The recursive module discharges these method
  and projection receipts under its native frame. Initial native parent-closure eligibility,
  semantic cache/state WF, translated-input eligibility and full inductive soundness remain
  open. Strong initial `VContext`/`TrEnv` and checker behavior are unchanged.
- `Verify.InductiveHeaderTelescopeTransport` derives transport of the complete
  native `inferLambda`, `inferForall` and `inferLet` helpers, including their
  actual telescope loops, from reached method callbacks. Raw allocation
  equations preserve the native fresh ID, generator increment and scoped local
  reader update of `withLocalDecl` and `withLetDecl`; final state effects remain
  observable after the scoped reader is restored. `NativeLambdaReachable`,
  `NativeForallReachable` and `NativeLetReachable` extend only after an accepted
  actual checking prefix, allocating from its final generator state and
  recording the instantiated domain/value, pushed fvar and accumulated levels.
  Lambda/let domain checks occur only in checked mode; forall domain checks
  occur in both modes. `NativeSortCallbacks` demands normalization only after
  accepted inference whose result is not already a sort. Checked let receipts
  demand value inference only after accepted domain sorting, and comparison
  only after accepted value inference. The existing `isDefEq` wrapper retains
  its equivalence-manager insertion; a false result never opens the next binder.
  Lambda/let terminal inference retains native reverse instantiation,
  `cheapBetaReduce` and `LocalContext.mkForall`, including retained dependent
  let wrappers and dropped unused lets. The source let nondependent flag does
  not replace the native local-let allocation default. Forall terminal sorting
  preserves the native source expression and right-folded `mkLevelIMax'`.
  `NativeInferMethodCallbacks.toCallbacks` discharges the three previous
  whole-helper obligations, and `inferType'.headerAxiomMethodTransport` composes
  them with the complete inference theorem. The projection module below
  discharges the remaining whole-helper obligation at eligible metadata frames.
  All owned declarations use only standard logical axioms, without admissions
  or expression/persistent-map interface
  axioms. Equal initial local readers remain explicit where closure needs them;
  no semantic fresh-name, local-context, cache or state WF follows from these
  raw equations. Recursive method receipts are derived below; staged projection
  eligibility, translated-input eligibility and full
  inductive soundness remain open. Strong initial `VContext`/`TrEnv` and the
  executable checker are unchanged.
- `Verify.InductiveHeaderProjectionTransport` derives transport of the complete
  native `inferProj` helper, including its actual parameter and preceding-field
  range loops, final field normalization and propositional elimination checks.
  `NativeForInReachable` records only accepted yielding steps of the actual
  finite traversal; the generic transport also preserves native early completion.
  Native range/list equivalence, rather than a replacement executable loop,
  connects those receipts to the original helper. `nativeProjectionView` and
  its structural `withApp` factorization retain the actual head/argument array
  without expression-cache interface axioms. Accepted metadata receipts preserve
  the requested parent name, inductive tag, singleton constructor list, exact
  parameter/index arity and successful constructor lookup. Constructor inference
  reads only the instantiated signature, so its raw transport does not demand
  an ignored constructor-record tag or equality of whole constant records.
  Reached parameter callbacks demand each native normalization. Proposition
  callbacks preserve inference-only inference followed by unconditional
  normalization, including already sorted inferred types. Previous-field domain
  checks occur only for a dependent body of a propositional structure; final
  field domain checks occur whenever the structure is propositional. Exact
  substitution of parameter arguments and earlier `.proj` expressions remains
  the original native behavior, with all accepted state effects preserved.
  `NativeProjectionMetadataFrame` permits either unchanged parent metadata or
  absence of every future constructor. The latter rules out actual success,
  rather than syntactically banning changed-parent projections. Its freshness
  bridge derives this frame from existing header-name/list receipts and
  `ConstructorsFresh`; no new global closure assumption is added. Successful
  actual projections recover their reached normalized entry receipt, forcing
  the stable-metadata alternative. Axiom parents and parents whose constructors
  are absent cannot produce a successful native helper result. After constructor
  registration a new-parent projection may succeed in the actual environment
  while still failing in its axiom shadow; this barrier is not erased.
  `NativeHeaderInferCallbacks` discharges all whole application/telescope/
  projection helper slots through reached method receipts and composes with
  complete inference in both modes via `inferType'.headerAxiomCallbackTransport`.
  All owned declarations exclude admissions and implementation-interface axioms.
  Raw projection eligibility is not semantic constructor/cache/state WF or
  unconditional mutually recursive method transport. The recursive module
  composes these receipts under its native metadata frame. Strong initial `VContext`/
  `TrEnv`, translated-input eligibility, inherited semantic/checker admissions
  and imported-prelude translation obligations remain unchanged. Full inductive
  soundness is still open; the executable checker is unchanged.
- `Verify.InductiveHeaderComparisonTransport` derives transport of the complete
  native lambda/forall comparison spines, quick comparison, right-to-left
  application-argument comparison and head-first, left-to-right application
  comparison. The shared binder-step factorization is proved equal to the
  original helpers. Equal domains skip comparison; unequal domains require only
  the reached reverse-instantiated method call. A false domain comparison exits
  without opening the body. Accepted domain prefixes retain equivalence-cache
  insertion before allocating the native fresh local. Loose bodies open the
  second binder's name, binder information and instantiated domain; closed bodies
  push the native default without allocation. Terminal callbacks use the exact
  accumulated substitution. `NativeBinderComparisonReachable` tracks actual
  accepted prefixes and both scoped readers, including arbitrary initial
  substitutions; it does not assert semantic fresh-name or local-context WF.
  Quick comparison preserves the complete native equivalence-manager query and
  its state effects, including the hash guard and cached-hit bypass. Its callback
  receipt is demanded only after an actual false query, in that query's returned
  state. The exact metavariable panic fallback is retained, not proved unreachable
  using an interface axiom. The original native application loop is transported
  directly by its decreasing remaining count. Its receipts cover only successful
  earlier argument comparisons, preserving early false completion and native
  equivalence insertion. Argument-spine comparison ignores nonapplication heads
  and can compare a trailing argument before discovering unequal arity;
  application comparison checks both application tags and complete arity before
  comparing heads and arguments in the opposite order. Structural `withApp`
  factorization does not rely on cached-expression interface axioms. All owned
  declarations exclude admissions and implementation-interface axioms. The
  remaining non-delta helpers are derived in the following helper module;
  lazy-delta step/loop transport is derived in the following lazy-delta module;
  complete `isDefEqCore'` transport is derived in the following core module;
  recursive `Methods.withFuel` transport is composed under a native metadata
  frame in `InductiveHeaderRecursiveTransport`.
  These raw transport proofs do not establish semantic cache/state WF,
  translated-input eligibility, accepted strong-shadow constructor checking or
  full inductive soundness. Strong initial `VContext`/`TrEnv`, inherited admission
  boundaries and imported-prelude translation obligations remain unchanged;
  the executable checker is unchanged.
- `Verify.InductiveHeaderComparisonHelperTransport` derives complete native eta
  expansion, structure eta, proof irrelevance, natural offset, string expansion
  and unit-like comparison transport, including the original symmetric wrappers.
  Symmetric callbacks are required only in the actual forward action's returned
  state after false/undefined completion. Eta expansion retains its lambda tag
  gate, inference-only inference, unconditional normalization, exact generated
  lambda name/domain/binder information and equivalence insertion. Proof
  irrelevance retains first-type inference, inference-only proposition inference
  followed by unconditional normalization, and the gate on second-type inference
  and type comparison. Offset and string helpers invoke the raw comparison core,
  without the wrapper's extra equivalence insertion, and retain their exact zero,
  successor, literal, application-head and universe-list guards.
  `NativeForInPrimeReachable` and dependent finite-loop transport cover only
  accepted yielding prefixes and preserve native early completion. Structure eta
  uses the actual proof-indexed range traversal and native `MProd` early-return
  accumulator, through proved native range/list equivalence, not an invented
  executable loop. Exact constructor lookup, arity and structure-like entry
  receipts precede inference/type comparison and ascending projected-field
  comparison. `NativeEtaStructMetadataFrame.ofShadowParents` derives its entered
  parent frame from reached native shadow inductive lookups. It does not claim
  automatic constructor-parent closure or semantic-to-native lookup transfer;
  an original semantic-map bridge would inherit persistent-map interface axioms.
  `nativeConstructorLookup` preserves accepted constructor classification and
  records, but not environment-bearing error payload equality. The unit-like
  metadata factorization preserves native nonrecursive, unindexed, singleton,
  nullary-constructor tests and error propagation. Its transport reuses
  `NativeProjectionMetadataFrame`, including the existing constructor-freshness
  bridge: changed-parent syntax is not banned, and an absent future constructor
  cannot produce accepted nullary metadata. Actual accepted false metadata still
  transports where the axiom shadow also returns false. Constructor registration
  can activate actual unit/eta comparison while the axiom shadow rejects, even
  with shared raw constructor records; these metadata barriers remain explicit.
  All owned declarations exclude admissions and implementation-interface axioms.
  The recursive module closes method receipts under its native frame. Semantic
  state/cache WF, translated-input/initial native eligibility and full inductive
  soundness remain open; the constructor module composes accepted strong-shadow
  checking under that frame. Strong initial `VContext`/`TrEnv`, inherited
  semantic/checker admission boundaries, imported-prelude translation and the
  executable checker are unchanged.
- `Verify.InductiveHeaderLazyDeltaTransport` derives the actual native lazy-delta
  step and complete fuelled loop transport. The pure dispatch policy preserves
  exact delta option records, reducibility-hint order, application tags, native
  constant-record pointer equality, regularity and the symmetric failure-cache
  guard. Its factorization is proved equal to the executable step, not substituted
  into the checker. A single delta side first tries the other projection-headed
  application; a projection miss continues from that callback's returned state.
  Definition unfolding retains its exact optional result and `get!` fallback,
  then calls the reached method with `cheapRec := false`, `cheapProj := true`.
  Equal-hint fast argument comparison additionally requires equivalent universe
  lists; success terminates immediately. Rejection inserts the failure only after
  the actual argument callback's returned state, then unfolds first and second
  in order. Unequal universe lists insert failure without comparing arguments.
  Continuation performs the native quick probe with `useHash := false`; body
  callbacks are demanded only after a false probe, in that probe's returned state.
  Native argument/binder receipts derive helper transport instead of assuming
  whole-helper equality. `NativeLazyDeltaReachable` records only actual accepted
  continuing rounds. The round factorization and decreasing-fuel induction
  preserve zero-fuel failure before all helpers, offset priority, first/second
  natural operand normalization and raw comparison calls, native reduction/error
  priority, and terminal versus continuing statuses. Only a continue status
  decrements fuel. Shadow fuel may be larger; reader eager-reduction policy must
  align, because environment agreement alone does not align the natural gate.
  Natural receipts expose only the reached successor/binary WHNF method calls.
  All owned declarations exclude admissions and implementation-interface axioms.
  These are raw result/complete-state proofs, not semantic cache/state WF,
  translated-input/metadata eligibility or automatic recursive method receipts.
  The recursive module supplies all-depth method receipts; accepted strong-shadow
  constructor checking, constructor WF, positivity/recursor equations, semantic
  registration and full inductive soundness remain open. Strong initial
  `VContext`/`TrEnv`, inherited admission boundaries, imported-prelude translation
  obligations and executable checker behavior remain unchanged.
- `Verify.InductiveHeaderDefEqCoreTransport` derives transport of the complete
  actual `isDefEqCore'` body from reached method/metadata receipts and the proved
  native comparison helpers. Its factorization retains the original control-flow
  shapes; separate Boolean-shortcut, normalized-recheck and unknown-result
  factorizations expose the actual accepted states for composition. Initial quick
  comparison uses `useHash := true` and can finish before any normalization or
  lazy-delta fuel is used. The Boolean-true shortcut retains the open-term/eager
  reader gate and normalizes only its first operand. Ordered cheap-projection
  normalization retains the returned states, and actual pointer guards decide
  whether to run the non-hash normalized quick probe. Proof irrelevance precedes
  the complete fuelled lazy-delta loop. Only its actual unknown result enters
  direct constant/universe, local-variable or projection-field comparison;
  projection comparison retains the original index-only parent-tag policy and
  wrapped equivalence insertion. Full normalization restarts the raw method core
  only after an actual pointer change; unchanged operands enter the original
  application, function eta, structure eta, string expansion and unit-like order.
  `NativeDefEqFallbackReachable` tracks actual accepted false/undefined prefixes,
  so later and symmetric receipts are required only in reached returned states.
  The complete theorem derives helper transport, rather than assuming equality
  of any whole helper or of the whole core. It retains native hash/pointer/cache
  guards, reader policy, larger shadow lazy-delta budgets, error propagation and
  the exact original continue-status panic fallback. All owned declarations
  exclude admissions and implementation-interface axioms. Structure/unit
  metadata barriers remain explicit: sharing raw constructor records does not
  turn an axiom shadow into an inductive metadata view. This raw result/state
  theorem does not derive semantic cache/state WF, translated-input/metadata
  eligibility or accepted strong-shadow constructor checking. The recursive
  module supplies the all-depth method receipts under its native frame.
  Constructor WF, positivity/recursor
  equations, semantic registration and full inductive soundness remain open.
  Strong initial `VContext`/`TrEnv`, inherited admission boundaries,
  imported-prelude translation and executable checker behavior are unchanged.
- `boolInductDecl.hasPrimitives` and `natInductDecl.hasPrimitives` derive the
  semantic primitive interface after complete header/constructor registration.
  The literal-availability/signature component is rebuilt from installed
  constructor lookups; unchanged primitive operation signatures preserve their
  existing typing and reduction contracts by semantic environment extension.
  Header-only Bool/Nat staging does not satisfy even this literal component,
  and the proof does not pretend otherwise. `NativePrimitiveSafety` and the
  native header/constructor safety-preservation theorems retain safe monomorphic
  primitive records when primitive names are forbidden, or when new declarations
  are safe and monomorphic. `checkInductiveTypes.refinesPrimitiveInterfaces`
  combines recognized primitive staging with semantic `HasPrimitives` and native
  primitive safety, deriving all final interfaces from their initial versions.
  Both Bool/Nat staging orders compose. The missing structural metadata and
  recursor/reduction obligations still prevent replacing `VContext.trenv` or
  claiming full inductive frontend correctness.
- `NativePrimitiveFrame` proves exact reserved-name lookup preservation,
  including absent primitive names, for ordinary header/constructor staging
  with `allowPrimitive = false`. It applies to unsafe and polymorphic ordinary
  declarations as well as safe monomorphic declarations. Alignment and semantic
  extension turn this native frame into semantic primitive-constant equality;
  `CheckerEnv.hasPrimitives_of_frame` then transports the existing primitive
  typing/reduction interface. The ordinary registration refinements and
  `checkInductiveTypes.refinesOrdinaryInterfaces` combine semantic registration,
  lookup/delta correspondence, semantic primitives, native primitive safety,
  and the exact primitive frame for the checked prefix. They require translated,
  well-typed header/constructor signatures, but do not assume registration
  success or primitive-name exclusion in the semantic models. Complete canonical
  primitive staging composes with ordinary staging. For a successful checked
  non-unsafe ordinary definition whose fresh name is not primitive,
  `addDefinition.nativePrimitiveFrame` gives the same native reserved-name
  frame, and `addDefinition.refinesPrimitiveFrame` packages it with the
  existing `VEnvs.WF`/`CheckerEnv` extension and semantic primitive interface.
  `addAxiom.nativePrimitiveFrame` supplies the corresponding checked-axiom
  registration bridge, including unsafe axioms, under the same explicit
  freshness and primitive-name guards. `addDefinitionHeader.nativePrimitiveFrame`
  isolates the unsafe-definition header stage under those guards; the full
  unsafe body pipeline remains a separate contract. `addDefinition.unsafeHeaderResult`
  extracts the successful header result from the nested unsafe body pipeline,
  without asserting anything beyond the executable result decomposition.
  These ordinary-definition bridges keep freshness and primitive-name guards
  explicit. These results do not
  discharge the remaining inductive metadata/recursor obligations or construct
  full `TrEnv`/`VContext` instances for the actual metadata-bearing staged
  environment. The separate typed axiom shadow above now has these instances;
  checker transport to it remains an independent obligation.
- `TypeChecker.Inner.checkLevel.checker` and `envGet.lookup` prove the leaf
  universe-validation and native lookup contracts needed by a restricted staged
  checker context. `inferConstant.checker` translates validated level arguments,
  preserves semantic constant typing through `CheckerEnv`, handles safe/unsafe
  and partial-definition guards, and produces `TrTyping` for the inferred native
  constant type. `infer_sort.checker` supplies the corresponding sort contract.
  These are leaf contracts only: they do not construct a `VContext`, replace
  the admitted checker stack, or establish application, projection, recursor,
  inductive metadata, or full frontend soundness.
- `RestrictedContext` packages `CheckerEnv`, semantic primitive contracts,
  native primitive safety, universe parameters, and a well-formed no-bound-
  variable semantic scope without requiring `TrEnv`. Its `inferConstant` and
  `inferSort` bridges reuse the leaf contracts above, and ordinary staging
  controls construct such a context after complete header/constructor
  registration. This is an intentionally restricted staged checker relation:
  it carries no native constructor/projection/recursor metadata and does not
  widen the existing `VContext.trenv` admission scope.
- `RestrictedContext.appExpr` and `forallExpr` expose the application and
  one-binder constructor-signature telescope steps as explicit `TrExprS`
  contracts. They require semantic function/argument typing or binder-domain
  and body well-formedness, respectively, and preserve the restricted scope;
  these wrappers alone do not verify native inference or telescope
  instantiation.
- `RestrictedContext.lamExpr`, `letExpr`, `litExpr`, `mdataExpr`, and
  `projExpr` package the remaining recursive `TrExprS` expression constructors
  over the same restricted scope. Their semantic typing, literal-availability,
  and projection-relation premises stay explicit; they do not establish native
  inference, projection metadata, or full frontend soundness.
- `Verify.StagedApplications` proves partial correctness of the actual
  `TypeChecker.Inner.inferApp` and its argument loop under explicit
  `ApplicationMethods` contracts for head inference and normalization. Its
  `RunWF` predicate preserves an arbitrary native-state invariant. The proof
  handles dependent arguments, batched delayed substitutions, and telescope
  tails exposed by normalization, returning `TrTyping` without constructing a
  `VContext` or invoking the existing full-context application theorem. A
  concrete fixture discharges these contracts for constant/sort leaf inference
  and identity or cheap beta normalization, preserving arbitrary state
  invariants. Accepted canonical Nat staging supplies the context and successor
  translation without caller-supplied semantic models. Runtime controls also
  cover dependent substitution, polymorphic heads, delta-exposed telescope
  tails, and missing-head/universe-arity/argument-arity rejection.
  Correctness of the full recursive methods, normalization, caches, native
  local scopes, and metadata-dependent checker paths remains separate.
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
  when the header types are well-formed. `VEnv.addInductHeaders.wf` additionally
  closes semantic `VEnv.WF` under those header-as-axiom registrations, while
  inheriting the existing inductive-declaration foundation encoded in `VEnv.WF`.
  `VInductDecl.HeadersWF` checks uniform universe-parameter counts and
  well-formed header types. Canonical `Bool`/`Nat` declarations satisfy this
  header-only specification in any starting environment.
- `boolInductDecl.constructorWF` and `natInductDecl.constructorWF` prove that
  the canonical primitive constructor signatures are semantically well-formed
  after their corresponding headers are staged in any starting semantic
  environment. Together with
  `VEnv.addConstructorHeaders.wf`, concrete `Bool` and `Nat` constructor
  environments now have semantic `VEnv.WF`; this remains ordinary typed-axiom
  staging and does not install inductive reduction or recursor behavior.
- `PrimitiveInductiveDecl.toVDecl` and `checkPrimitiveInductive.toVDecl` connect
  the recognized primitive shapes to those canonical declarations. Their
  `TrInductDecl` translations check datatype headers in the old environment and
  constructor types in the successfully registered header environment, where
  recursive datatype references are available. These translations do not prove
  the full inductive frontend; no recursor or reduction equation is installed at
  this stage.
- `AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorWF`
  connects successful primitive recognition to the actual checked
  header/constructor registration prefix. From initial `Aligned` correspondence
  and semantic `VEnv.WF`, successful native staging produces both semantic
  registration witnesses, their well-formedness, a source `TrInductDecl`
  translation and final native alignment. Unlike the generic registration
  theorem, primitive header/constructor translations, typing and semantic
  registration success are derived, not caller-supplied premises. This remains
  partial correctness of typed-axiom staging; it does not justify positivity,
  native `TrEnv`, generated recursors or reduction semantics.
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
- `AddInductive.declareInductiveTypes.refinesWF` and
  `AddInductive.checkInductiveTypes.refinesHeadersWF` compose the same header
  refinements with `VEnv.addInductHeaders.wf`. Under an explicit initial
  semantic `venv.WF` and well-formed translated headers, successful staging now
  returns a registered header environment that is semantically well-formed and
  still `Aligned` with the native constants. This is deliberately a semantic
  header-as-axiom result: it does not manufacture the native `TrEnv` extension
  required by `VEnvs.WF`, because the general `AddInduct` relation remains
  unimplemented.
- `VEnv.addConstructorHeaders` installs constructor signatures as fresh ordinary
  typed constants. Its append, extension, installed-lookup, equation-preservation,
  and orderedness properties are proved. `AddInductive.declareConstructors.refines`
  follows both executable registration folds and preserves `Aligned`, given
  translated constructor types and an admitting safety filter. The `ordered`
  corollary additionally assumes abstract constructor-type well-formedness.
  This standalone structural refinement does not justify constructor arities,
  parent/index metadata,
  parameter-count assertions, positivity, projection/injectivity behavior,
  recursor generation, or inductive reduction equations. It does not extend the
  full `TrEnv` relation or discharge `AddInduct`.
- `VEnv.addConstructorHeaders.wf` and
  `AddInductive.declareConstructors.refinesWF` now close the same constructor
  registration path under semantic `VEnv.WF`, given an explicit well-formed
  starting header environment and well-formed translated constructor constants.
  The result remains a sequence of typed ordinary constants: it does not turn
  constructor registration into a native `TrEnv`/`AddInduct` proof or establish
  generated recursors, positivity, metadata soundness, or reduction equations.
- `AddInductive.checkInductiveTypes.refinesHeaderConstructorWF` composes the
  executable header stage with constructor registration under explicit semantic
  header/constructor models. Successful staging returns both a well-formed
  header environment and a well-formed constructor-extended environment, while
  preserving native `Aligned` correspondence. The constructor model is
  supplied for the semantic header environment produced by `addInductHeaders`;
  this remains conditional and does not include `checkConstructors` soundness,
  native `TrEnv` extension, generated recursors, or cache semantics.
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
- `AddInductive.checkInductiveTypes.frameHeaderSizesParamsCountDistinct`
  additionally exposes `InductiveStats.ParamsCount`: the checked parameter-array
  size equals the declared count for nonempty datatype batches and zero for empty
  batches. `paramsCount` supplies this invariant to arbitrary continuations,
  `getParamsCount` returns it with statistics, and `getParamsCount_of_nonempty`
  specializes it to the declared count. The existing traversal invariant proves
  it without repeating checking or changing executable assertions; all older
  contracts remain unchanged projections. The empty-input proof includes the
  logical panic/default model when a nonzero declared count fails the terminal
  assertion; it does not claim runtime acceptance of malformed empty input.
  These proofs need only standard logical axioms, not checker soundness.
- `AddInductive.checkInductiveTypes.frameHeaderSizesAritiesParamsCountDistinct`
  also proves `InductiveStats.HeaderArities`: every source datatype's raw leading
  binder count is at most the declared parameter count plus its checked index
  count. `headerArities` and `getHeaderArities` supply this invariant to arbitrary
  continuations and returned statistics. Equality is not a valid general claim:
  checking weak-head normalizes before and between binders, so delta, beta, let,
  or annotation reduction can expose additional binders.
  The shared traversal proof is parameterized by a private binder measure;
  old contracts instantiate the zero measure and keep their logical-only axiom
  boundaries, while the new raw-arity contract uses the existing executable
  instantiation bridge. Successful WHNF cannot remove a raw leading forall:
  the executable checker returns such a head unchanged, and all other raw heads
  have zero leading binder count. No semantic WHNF soundness premise is needed.
  Empty arrays retain the proof-only panic/default treatment and have no arity
  entries to constrain.
- `Verify.ConstructorArity` proves offset additivity for the actual executable
  constructor binder counter and that substituting a free variable preserves
  its raw leading-forall spine. Consuming one forall binder therefore preserves
  the total when the counter advances by one. The checked parameter invariant
  supplies the substitution premise through `checkInductiveTypes.parameterArity`.
  The specification-level substitution proof uses only `propext`; its bridge to
  `Expr.instantiate1` additionally uses the existing `Lean.Expr.instantiate1_eq`
  interface axiom, without `sorryAx`. These arity prerequisites feed the
  constructor parameter-consumption and full-batch arity proofs below. The four
  foundational count/substitution lemmas now live in
  `Verify.ConstructorArity.Basic` to share them with header statistics without
  introducing an import cycle; their names and statements are unchanged.
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
  well-formedness, or traverse the full constructor batch.
  `checkConstructors.arity` now lifts the inner-loop bound through the actual
  constructor lists and datatype-index range. Successful full batch checking
  guarantees the lower bound for every constructor, given free-variable and
  distinct parameter arrays. The proof handles duplicate-name rejection, the
  source guard, and constructor type checking without assuming type-checker
  soundness. Its traversal invariant requires successful steps to yield, so
  an early loop exit cannot bypass remaining constructors.
  `checkInductiveTypes.checkedConstructorsArity` supplies both parameter
  invariants from checked types and composes them with full batch checking.
  `isValidIndAppIdx.indexNoIndOcc` additionally proves the positivity-relevant
  return invariant that every index argument after the parameters contains no
  occurrence of a datatype under construction. This remains a syntactic
  classifier contract, not a semantic positivity theorem.
  The standalone batch theorem also applies after replacing the context's
  environment with registered datatype headers. These are arity contracts,
  not semantic constructor-typing or positivity proofs. Datatype-header
  registration is not part of the checked-type/batch composition. The numeric
  constructor-registration composition is proved separately below; recursors
  and full inductive soundness remain open.
- `Verify.InductivePositivity` proves a normalized acceptance trace for the
  actual recursive `checkPositivity` checker. `isValidIndApp?.valid` proves that
  its successful first-match classifier returns an in-range datatype index
  accepted by `isValidIndAppIdx`. `PositivityTrace` distinguishes normalized
  absence, a valid recursive inductive application, and a forall with no
  datatype occurrence in its domain. Forall recursion records the exact
  annotation-consumed local declaration, fresh-name advance, and instantiated
  body. `checkPositivity.loop.trace_of_whnf` and `checkPositivity.trace_of_whnf`
  expose an explicit context-sensitive WHNF-result contract;
  `checkPositivity.trace` specializes it to actual successful WHNF calls without
  additional premises. Legitimate recursive fields are included rather than
  incorrectly requiring every normalized field to have no occurrence.
  These are operational/syntactic traces, not semantic WHNF translation,
  constructor typing, or full inductive soundness proofs. No new axiom or
  admitted proof is used; all twelve theorem audits use only standard logical
  axioms.
  `SafeConstructorTrace` now carries the actual positivity trace of each fresh
  field through the safe constructor loop. Its parameter and field constructors
  retain the real `stats.params[index]?` branch witness, so parameter domains
  that bypass positivity cannot be relabeled as checked fields. Fresh fields record the exact
  local context and instantiated continuation; terminal returns carry their
  accepted inductive application. `SafeConstructorTrace.spine` recovers the
  earlier structural spine and valid return witness.
  `checkConstructors.loop.safeTrace_of_whnf` exposes the context-sensitive
  normalization premise, while `checkConstructors.loop.safeTrace` specializes
  to actual WHNF results with no external positivity premise. This includes
  recursive fields that the older normalized-absence-only conditional contract
  cannot cover. These inner-loop theorems do not assert semantic constructor
  typing.
  `InductiveStats.SafeConstructorTraces` records a trace for every constructor
  at its concrete datatype-array index, starting from the original batch
  context and binder counter zero. `checkConstructors.safeTraces_of_whnf`
  lifts safe traces through both actual batch traversals, including duplicate
  rejection, the source guard, and constructor type checking.
  `checkConstructors.safeTraces` specializes to actual WHNF results without
  an external positivity premise. Successful traversal steps must yield, so
  an early exit cannot bypass later constructors or datatypes. The indexed
  `SafeConstructorTraces.spine` projection retains the concrete parent rather
  than replacing it with an existential matching datatype. These are full
  safe-batch operational contracts, not header registration, constructor
  registration, semantic typing, or full inductive soundness.
  `checkInductiveTypes.registeredSafeConstructors` now composes the real
  checked-type continuation, datatype-header registration, and safe constructor
  batch, supplying traces to an arbitrary continuation in the actual installed
  header environment. Checked header sizes, parameter counts, free-variable
  shape, distinctness, and the original context frame are supplied internally.
  `getRegisteredSafeConstructorTraces` returns the checked statistics and actual
  root `Context`; `InductiveStats.RegisteredSafeConstructorTraces` retains those
  invariants, the fixed context fields after restoring the original environment,
  and every indexed trace rooted in the returned context. Neither its local
  context nor its fresh-name generator is reconstructed from `stats.lctx`:
  later datatype indices can extend the real root beyond that stored snapshot.
  The returned environment contains the newly installed datatype headers, not
  registered constructors. Both checks explicitly use the safe-mode flag
  `false`; they do not infer semantic safety from the incoming context or prove
  constructor typing, recursor registration, or complete inductive soundness.
- `Verify.ConstructorMetadata` specifies the exact concrete constructor records
  installed by registration. `declareConstructors.metadataVal` contains the
  source name/type, universe parameters, parent, per-parent constructor index,
  safety flag, actual parameter-array size, and raw arity minus that size.
  `InductiveStats.ConstructorMetadata` additionally requires each installed
  record's parameter and field counts to sum to the raw executable arity.
  `declareConstructors.metadata` follows both registration folds, proves every
  indexed lookup, preserves all old constant entries, and preserves concrete
  constant-map validity. It assumes that validity initially and the raw arity
  lower bound for every source constructor. Fresh-name guards prevent later
  registrations from overwriting earlier records; constructor indices restart
  at zero for each parent.
  `checkConstructors.declareMetadata` supplies the arity guard from successful
  full batch checking. `checkInductiveTypes.checkedConstructorMetadata`
  additionally supplies free-variable and distinct-parameter invariants and
  carries the unchanged context frame into checking/registration. Its only
  initial invariant premise is concrete constant-map validity, not semantic
  environment well-formedness. These numeric contracts refer to the actual
  `stats.params.size`; they do not prove it equals the original declared
  parameter count in every exceptional empty-header case. The checked-type
  composition does not register datatype headers. Semantic constructor typing,
  positivity, recursors, full `TrEnv` extension, and inductive soundness remain
  separate. All three theorem audits exclude `sorryAx`, with no new axioms,
  admitted proofs, executable checker paths, or caches.
- `Verify.InductiveMetadata` completes the numeric checked-type/header-register/
  constructor-check/register prefix. `declareInductiveTypes.metadataVal` models
  the actual header records, including the declared parameter count, each
  datatype's stored index count, family and constructor-name lists, nested count,
  universe parameters, safety, and computed recursion/reflexivity flags.
  `declareInductiveTypes.metadata` proves every indexed header lookup, old-entry
  preservation, and constant-map validity under an initial map-validity premise
  and matching header/index-array sizes. The size premise prevents the executable
  `zipWith` from truncating the input datatype batch.
  `checkInductiveTypes.registeredConstructorMetadata` supplies that size invariant
  and the parameter invariants internally, registers headers, checks the complete
  constructor batch in that environment, and registers its constructors. The
  final environment preserves all original entries and every newly installed
  header, contains the exact constructor records with nontruncating field counts,
  and has a valid concrete constant map. Its only starting invariant premise is
  concrete map validity; no externally supplied translations, semantic typing,
  array-size, or parameter-shape/distinctness premises are required.
  This is a partial-correctness contract for the indicated executable prefix,
  not `AddInductive.run` or unrestricted `addDecl.WF`. The earlier universe-name
  guard and subsequent elimination/recursor stages are not included. Header
  flags are copied from the executable computations, not proved to characterize
  semantic recursion/reflexivity. `DeclaredParameterMetadata` requires exact
  parent/constructor record lookups whose parameter counts both equal the declared
  count, with constructor parameter-plus-field counts equal to raw arity.
  `InductiveStats.declaredParameterMetadata` derives this from the checked count
  and the existing exact metadata contracts: every valid parent index proves the
  batch is nonempty, so no separate nonempty premise is necessary. Empty batches
  have no records to relate and satisfy this contract vacuously.
  `checkInductiveTypes.registeredParameterMetadata` strengthens the complete
  prefix with that alignment and the checked count; the older metadata theorem
  remains an unchanged projection. All four audits exclude `sorryAx`; alignment
  uses only standard logical axioms, while registration additionally uses the
  existing map and guarded-arity interfaces. No new axioms, admitted proofs,
  executable paths, or caches are added.
  `DeclaredHeaderArities` additionally exposes exact header lookups whose raw type
  arity is bounded by the installed parameter-plus-index counts.
  `InductiveStats.declaredHeaderArities` derives it from checked statistics and
  header metadata, including headers with no constructors.
  `checkInductiveTypes.registeredHeaderArities` carries both source/header bounds
  through the full checked prefix, preserving the older metadata APIs as
  projections. The arity contracts are audited separately in
  `tests/InductiveArity.lean`; no semantic typing or inductive soundness claim is
  added. That test and the minimal `tests/InductiveHiddenParameter.lean` demonstrate
  why an isolated-prefix comparison must retain the earlier preprocessing guard:
  full frontend rejection agrees with Lean 4.29.0 on hidden declared parameters.
  The boundary is resolved and documented in `divergences.md`.
- `Verify.InductiveRegistration` combines the safe positivity traces with the
  checked-type/header/constructor registration prefix.
  `InductiveStats.SafeConstructorRegistration` retains the actual header-stage
  root separately from the later constructor environment. Its traces keep
  using WHNF in that original root; no unproved normalization transport to the
  extended environment is assumed. Both environments have valid concrete
  constant maps, all original/header entries are preserved, and exact header
  metadata is retained before and after constructor registration alongside the
  final constructor records and nontruncating parameter/field counts.
  `checkInductiveTypes.safeConstructorRegistration` supplies the contract to an
  arbitrary continuation running in the constructor environment while passing
  the unchanged trace root explicitly. The checking action is executed once:
  its successful result supplies both the safe trace and existing arity guard.
  `getSafeConstructorRegistration` returns statistics, the root, and the later
  environment. `preservesOriginal` and `declaredParameters` expose old-entry
  preservation and declared parent/constructor parameter alignment.
  The only initial invariant premise is concrete map validity, not semantic
  environment well-formedness. All six audits exclude `sorryAx`;
  registration/run proofs use only the existing map and guarded-arity interfaces,
  while the projections need no such interfaces. These are safe-mode
  operational/numeric contracts, not semantic positivity, constructor typing,
  elimination/recursor verification, or complete `AddInductive.run` soundness.
  `AddInductive.run.safeConstructorRegistration` now exposes that intermediate
  registration witness from any successful complete run, under an explicit
  `.safe` context premise and initial map validity. It follows the earlier
  universe-name guard and applies the continuation bridge to the actual
  elimination/recursor suffix, without assuming that suffix's semantic
  correctness. The existential header root and constructor environment remain
  distinct from the returned recursor environment; no final-environment map
  validity, metadata preservation, or WHNF transport is inferred by these
  witness-only runner theorems.
  `run.safeConstructorTraces` projects the indexed traces and proves that their
  original root has safe context safety. Both are operational acceptance
  certificates, not unrestricted inductive frontend or environment soundness.
- `Verify.RecursorRegistration` proves concrete map validity and exact old-entry
  preservation for the actual recursor registration suffix. The executable
  suffix is extracted into `AddInductive.declareRecursors`, called by the
  unchanged runner sequence after recursor information, local context, and
  safety/K flags are obtained. The original zero-initialized minor-index state,
  dependent datatype traversal, rule generation, name checks, and metadata
  payload remain unchanged. `declareRecursors.preserves` needs only validity
  of the initial concrete constant map; every successful result has a valid map
  and retains every previous constant lookup. It covers arbitrary safety flags,
  recursor inputs, and rule-generation outcomes without claiming typing of
  generated metadata or rules. Its audit uses only the three existing map
  interfaces and standard logical axioms, excluding `sorryAx` and expression
  or guarded-arity interfaces. A proof regression composes preservation with
  the constructor-registration certificate, retaining original constants and
  exact header/constructor records in the recursor environment. The separate
  frame and complete-run preservation modules below now connect this suffix
  through the earlier `mkRecInfos` continuation. Semantic recursor correctness,
  WHNF transport, and unrestricted inductive soundness remain separate.
- `Verify.RecursorMetadata` specifies the complete executable recursor record
  with `declareRecursors.metadataVal` and proves `declareRecursors.metadata`
  for the real suffix traversal. Every successful result has a valid concrete
  map, preserves all previous lookups, and satisfies
  `InductiveStats.RecursorMetadata` at every valid datatype index. This retains
  the exact name, universe parameters, abstracted/inferred type, datatype list,
  parameter/index/motive/minor counts, rules, and K/safety flags. Each installed
  rule list also has a successful `mkRecRules` receipt at the actual incoming
  context, with existential starting/ending minor indices from the traversal.
  Receipts come from that successful action, not an extra checking pass or
  unproved rule specification. `sourceRules` projects stored rules and their
  operational provenance. `DeclaredRecursorCounts` and `declaredCounts` relate
  installed counters to declared parameters, datatype count, and total
  constructor count under explicit parameter/motive/minor alignment premises;
  the parameter premise comes from the existing checked prefix, and the
  `RecursorInfoCounts` module below now proves the generation action supplies
  the two remaining alignment premises. The suffix does not validate arbitrary
  recursor inputs, prove index-binder alignment, or establish semantic recursor
  typing/reduction. The original contract leaves starting minor indices
  existential; the offset module below now proves exact prefix-state receipts.
  Both registration audits use only the
  existing three map interfaces; the two metadata projections use only standard
  logical axioms. All exclude `sorryAx` and expression/guarded-arity interfaces.
  Executable kernel code and the original `inferImplicit 1000 false` behavior
  are unchanged. The `InductiveRunMetadata` module below now lifts these stronger
  receipts through the complete safe runner.
- `Verify.RecursorInfoFrame` proves `mkRecInfos.frame` for arbitrary generation
  continuations. The actual motive, major-premise, index, constructor-field,
  recursive-hypothesis, and minor-premise loops preserve `Context.HeaderFrame`:
  environment, universe parameters, safety, primitive-name policy, and fuel.
  Local contexts and fresh-name generators may grow and are not equated with
  their inputs. The theorem needs no environment-validity or safe-mode premise
  and uses only standard logical axioms, without checker-correctness or
  expression-interface assumptions. WHNF/inference/classification results are
  opaque operational values; the proof does not assert their semantic validity.
- `Verify.RecursorInfoCounts` proves `mkRecInfos.frameCounts` for arbitrary
  continuations, retaining the same immutable frame alongside generated-array
  alignment. `RecursorInfoCounts` records exactly one recursor-information
  entry per datatype and exactly one minor per constructor in each entry.
  `motiveTotal` and `minorTotal` recover the mapped motive count and flattened
  minor count; `getCounts` exposes the generated array and context with both
  certificates. The first generation phase preserves empty minor arrays while
  pushing entries; the second preserves array size and other entries while
  adding one minor per constructor. `mkRecInfos.registerCounts` composes actual
  generation with the verified registration suffix, proving final concrete
  map validity, preservation of old entries, and `DeclaredRecursorCounts` from
  initial map validity and the checked parameter-count premise alone. No
  caller-supplied motive/minor alignment premises remain. Count/frame/getter
  audits use only standard logical axioms; the registration audit additionally
  uses the existing three map interfaces. All exclude `sorryAx` and expression
  or guarded-arity interfaces. Executable kernel code is unchanged; semantic
  recursor typing, index-binder alignment, reduction soundness, and WHNF transport
  remain separate. The complete safe-run metadata module below now retains the
  generated count certificates alongside exact installed recursor records.
- `Verify.InductiveRunPreservation` connects successful safe complete runs to
  their actual final environment. `InductiveStats.SafeRunRegistration` retains
  the original rooted constructor-registration certificate and its intermediate
  constructor environment, proves final concrete map validity, and preserves
  every constructor-stage lookup. `run.safeRegistration` composes the existing
  checked registration prefix, the real recursor-information frame, and the
  verified registration suffix; it needs only an explicit safe context and
  initial concrete map validity. `preservesOriginal`, `headerMetadata`,
  `constructorMetadata`, and `declaredParameters` project exact original-entry,
  header/constructor-record, and numeric parameter alignment facts in the final
  environment. `run.safePreserves` exposes final map validity and preservation
  of all original entries without keeping the existential intermediate data.
  Safe positivity traces remain indexed by the original header root: no WHNF
  transport to the final environment is assumed. Both runner audits exclude
  `sorryAx`, using only the existing map and guarded-arity interfaces; all four
  certificate projections use only standard logical axioms. Executable kernel
  code is unchanged. Generated recursor typing, reduction equations, semantic
  `TrEnv` extension, earlier declaration preprocessing, and unrestricted
  inductive frontend soundness remain unproved.
- `Verify.InductiveRunMetadata` proves `run.safeMetadata`, strengthening the
  complete safe-run certificate with exact installed recursor records and
  generated count alignment. `InductiveStats.SafeRunMetadata` extends the
  existing rooted registration certificate and retains existential elimination
  level, generated information array, K flag, and actual rule-generation reader
  context. Its immutable frame anchors that context to the intermediate
  constructor environment, not the final recursor environment; local contexts
  and fresh-name generators may grow. Exact record types use that reader's actual
  local context, the original universe parameters, and the safe record flag
  derived through the preserved safety fields. `declaredRecursors` discharges
  parameter/motive/minor count alignment from the checked prefix and generated
  count certificate. `sourceRules` projects successful stored-rule receipts in
  their original source context. `run.safeDeclaredMetadata` exposes final map
  validity, old-entry preservation, exact header/constructor metadata, declared
  parameter metadata, and declared recursor counters together. Both runner
  theorems need only explicit safe input and initial concrete-map validity; their
  audits use exactly the existing three map and six guarded-arity interfaces.
  Both certificate projections use only standard logical axioms. All audits
  exclude `sorryAx`; no new axioms or executable kernel changes are introduced.
  Positivity traces retain the original header root. Semantic recursor typing,
  index-binder alignment, reduction
  soundness, WHNF transport, earlier preprocessing, and general inductive
  frontend soundness remain separate obligations. The rule-shape module below
  now proves per-parent constructor/order correspondence and rule counts.
- `Verify.RecursorRuleShape` proves `mkRecRules.shape` for the actual rule
  generator. Every successful result has exactly the input parent's constructor
  name sequence, in the same order, and advances the minor state by that parent's
  constructor count. `RecursorRuleShape.count` derives rule-list length from the
  sequence equality. The proof follows the real constructor and recursive-field
  loops and the array-backed `forIn` traversal; inference/normalization results,
  field arrays, and RHS construction remain opaque operational values. It needs
  no environment validity, safety, input-array alignment, or name-uniqueness
  premise. Reordered and repeated constructor names are retained as sequences,
  without assuming that a later declaration-registration stage accepts them.
  Failed actions satisfy only the successful-result contract vacuously.
  `InductiveStats.RecursorMetadata.ruleShape` derives the local shape/state
  certificate from stored-rule source receipts, and `orderedRules` exposes
  installed names and counts through `OrderedRecursorRules`. The corresponding
  `SafeRunMetadata.orderedRules` projection and `run.safeOrderedRules` theorem
  carry those facts into complete safe runs while retaining final map validity
  and original-entry preservation. All five shape/count/certificate audits use
  only standard logical axioms; the complete-run audit adds exactly the existing
  three map and six guarded-arity interfaces. All exclude `sorryAx`; executable
  kernel code and axioms are unchanged. This module proves local minor-state
  advancement; the next module now proves the global starting-index prefix-sum
  formula. The field module below now proves raw and registered field-count
  alignment; semantic rule typing, reduction soundness, index-binder alignment,
  and WHNF transport remain separate.
- `Verify.RecursorMinorOffsets` defines `recursorMinorOffset` as the number of
  constructors in the datatype-array prefix before an index, proving its zero,
  successor, and total-count equations. `declareRecursors.offsetMetadata`
  strengthens the real registration suffix contract to
  `InductiveStats.RecursorOffsetMetadata`: every installed exact record has a
  successful `mkRecRules` receipt starting at that parent's constructor-prefix
  offset and ending at the next parent's offset, in the original reader context.
  The range traversal preserves this invariant from its actual zero starting
  state, using the proved per-parent advancement; it simultaneously retains map
  validity, old lookups, and every earlier record. Empty parents leave the offset
  unchanged. `metadata` recovers the existing exact-record certificate, while
  `sourceRules` projects the precise stored-rule receipts without existential
  starting/ending indices. `InductiveStats.SafeRunMinorOffsets` retains the same
  original header root, intermediate constructor environment, immutable reader
  frame, and generated count certificates with those stronger receipts.
  `run.safeMinorOffsets` proves it for complete safe runs from explicit safe input
  and initial map validity alone. Its `metadata` projection recovers the prior
  `SafeRunMetadata` contract, and `sourceRules` preserves precise receipt contexts.
  All seven prefix/compatibility/source-projection audits use only standard
  logical axioms; the suffix audit adds the existing three map interfaces, and
  the complete-run audit also uses the existing six guarded-arity interfaces.
  All exclude `sorryAx`. Executable kernel code and existing contracts remain
  unchanged. The next module now derives field-count alignment from the checked
  free-variable parameter invariant. Semantic RHS typing/reduction, index-binder
  alignment, WHNF transport, and earlier preprocessing remain unproved.
- `Verify.RecursorRuleFields` proves `mkRecInfos.loopCtorArgs.fields` for arbitrary
  continuations, preserving the immutable reader frame and counting generated
  fields as the raw constructor forall arity minus the parameter-array size.
  Its loop invariant accounts for already collected fields and parameters still
  to consume; substitution by free variables preserves raw arity. The theorem
  requires `InductiveStats.ParamsAreFVars`, which the actual checked prefix
  supplies, but no parameter-count lower bound or uniqueness premise. Truncated
  subtraction is intentional for isolated inputs with too few binders; this is
  not a claim that declaration registration accepts those inputs.
  `RecursorRuleFields` records the exact ordered constructor-name/field-count
  pairs. `mkRecRules.fieldCounts` proves this for the real rule generator, and
  `at` supplies the corresponding rule at a concrete constructor-list position.
  `RecursorMetadata.ruleFields` transfers the result through stored-rule receipts.
  Both `SafeRunMetadata.ruleConstructorFields` and the stronger offset-certificate
  projection join those rules to actual registered constructor records in the
  final environment: matching names have `rule.nfields = info.numFields`.
  `run.safeRuleConstructorFields` exposes this alongside final map validity and
  preservation of old entries, needing only explicit safe input and initial
  concrete-map validity. Original positivity roots and rule reader contexts are
  unchanged. Five new traversal/generator/certificate audits use only standard
  logical axioms and the existing `Expr.instantiate1_eq` interface; the positional
  projection uses only logical axioms. The complete-run audit uses exactly the
  existing three map and six guarded-arity interfaces. All exclude `sorryAx`;
  no new axiom, admission, or executable kernel change is introduced. Counts are
  raw syntactic forall counts, not a semantic typing or normalization theorem.
  RHS typing/reduction, generated index-binder alignment, WHNF transport, and
  earlier preprocessing remain separate.
- `Verify.RecursorMinorIndexing` proves `RecursorInfoCounts.minorPrefix`: the
  generated minor-array prefix has exactly the corresponding constructor-prefix
  length, including saturated prefixes beyond the parent-array size.
  `minorIndexing` proves both local and flattened bounds for every constructor
  position and identifies the flattened optional lookup at its parent's prefix
  offset plus its local index with the parent's own minor entry.
  `RecursorMinorIndexing.at` exposes the same present expression in both arrays;
  `getElem!` gives the equality for the defaulting accessor used by `mkRecRules`,
  justified by proved bounds rather than fallback behavior. No minor uniqueness,
  expression shape, parameter, typing, or normalization premise is needed beyond
  the generated count certificate. Empty parents contribute no entries and
  naturally leave offsets unchanged. `SafeRunMinorOffsets.indexedSourceRules`
  retains the actual generated arrays, immutable reader frame, and successful
  installed-rule receipts alongside their indexing proof.
  `run.safeMinorIndexing` supplies this stronger source contract and the original
  safe-run offset certificate from explicit safe input and initial map validity.
  Five new prefix/indexing/accessor/certificate audits use only standard logical
  axioms; the complete-run audit adds only the existing three map and six
  guarded-arity interfaces. All exclude `sorryAx`, and no new axiom, admission,
  executable kernel change, cache, or fast path is introduced. This establishes
  vector-position alignment, not semantic RHS typing/reduction, generated
  index-binder alignment, WHNF transport, or preprocessing soundness.
- `Verify.RecursorRuleRhs` specifies the literal generated RHS recipe: nested
  abstraction of parameters, motives, minors, and constructor fields, followed
  by application of the selected minor to fields and generated recursive values.
  `RecursorRuleRhsReceipt` retains those argument arrays and the actual local
  context under the original immutable reader frame, with exact constructor
  name, field count, and expression equality. `RecursorRuleRhs` relates the
  constructor list, zipped with its starting minor counter, positionally to the
  rule list; `count` and `at` project its length and individual receipts without
  assuming unique names. `mkRecRules.rhs` proves the complete receipt sequence
  and counter advancement for the real generator. A fixed-context traversal
  proof ensures the recursive-value loop invokes its final continuation in the
  constructor-field context, rather than weakening the receipt to an arbitrary
  local context. This raw generator contract deliberately permits arbitrary
  initial counters and defaulting minor access; it alone does not claim bounds
  or minor presence for unchecked inputs.
  `RecursorOffsetMetadata.localRuleRhs` combines successful stored-rule receipts
  with generated count/indexing proofs to identify each RHS's selected minor
  with its present parent-local entry. `SafeRunMinorOffsets.localRuleRhs` retains
  the actual generated arrays and reader context; `run.safeRuleRhs` supplies this
  contract alongside the original safe-run certificate from explicit safe input
  and initial map validity. Five new count/position/generator/certificate audits
  use only standard logical axioms, with no expression interface; the runner
  adds only the existing three map and six guarded-arity interfaces. All exclude
  `sorryAx`. No executable kernel change, new axiom, or admission is introduced.
  These are syntactic formation receipts, not semantic RHS typing/reduction,
  field/recursive-value scope correctness, generated index-binder alignment,
  WHNF transport, or preprocessing soundness.
- `Verify.RecursorRuleRhsCounts` strengthens formation receipts with argument
  counts without changing the earlier contracts. `mkRecInfos.loopCtorArgs.recursiveFields`
  proves that selected recursive fields form an ordered sublist of all generated
  constructor fields, retaining the immutable reader frame for arbitrary
  continuations. Its loop invariant also handles preexisting arrays; no
  free-variable parameter, distinctness, raw-arity, or semantic positivity
  premise is needed. `mkRecRules.loopU.counts` proves that the value traversal
  appends exactly the remaining selected-field count to its initial value array,
  in the same reader context. The subtraction saturates when the starting index
  is at or beyond the selected-array size.
  `RecursorRuleRhsCountReceipt` keeps the same actual field/value/context witnesses
  as the literal RHS recipe, additionally retaining the selected-field sublist
  and exactly one generated value per selected field. `argumentBound` proves
  that the recursive application argument count is at most `rule.nfields`, for
  those same recipe witnesses. The existing registered-constructor alignment
  transfers this bound to `ConstructorVal.numFields`. Receipt and positional
  sequence projections recover the prior formation contracts.
  `mkRecRules.rhsCounts`, `RecursorOffsetMetadata.localRuleRhsCounts`, and the
  safe-run projections retain present local-minor selection, actual source
  contexts, exact generated recipes, and these stronger counts. The complete
  runner still needs only explicit safe input and initial map validity. Nine new
  traversal/receipt/sequence/certificate audits use only standard logical axioms;
  the runner adds only the existing three map and six guarded-arity interfaces.
  All exclude `sorryAx`, with no new expression interface, axiom, admission,
  executable kernel change, cache, or fast path. These are ordered-selection and
  cardinality proofs, not semantic RHS typing/reduction, field/value scope
  correctness, generated index-binder alignment, WHNF transport, or preprocessing
  soundness.
- `Verify.RecursorRuleRhsFVars` proves the free-variable atom shape of the actual
  constructor-field vectors retained by counted RHS recipes.
  `RecursorFieldsAreFVars` has push and ordered-sublist projections;
  `mkRecInfos.loopCtorArgs.fvars` retains this property, the recursive-field
  sublist, and the immutable reader frame for arbitrary continuations. The
  helper's invariant admits preexisting free-variable fields, while the public
  traversal starts from empty arrays. No parameter free-variable, raw-arity,
  distinctness, freshness, or semantic positivity premise is needed.
  `RecursorRuleRhsFVarReceipt` couples field shape to the same selected fields,
  recursive values, local context, count equalities, and literal RHS recipe.
  `shapes` transfers the atom property to selected fields and retains the numeric
  argument bound; `counts` recovers the earlier receipt without changing its
  witnesses. Positional sequence compatibility/lookup projections and
  `mkRecRules.rhsFVars` lift the contract through actual rule generation.
  Stored offset receipts and complete safe runs retain present parent-local
  minor selection and the actual reader context through `localRuleRhsFVars` and
  `run.safeRuleRhsFVars`. Ten new array/traversal/receipt/sequence/certificate
  audits use only standard logical axioms, with no expression interface; the
  runner adds only existing three map and six guarded-arity interfaces. All
  exclude `sorryAx`, with no new axiom, admission, or executable kernel change.
  Atom shape does not establish declaration membership in any reader context,
  field freshness/uniqueness, or semantic typing. Generated recursive values
  need not themselves be free-variable atoms. Those scope/typing boundaries,
  RHS reduction, generated index-binder alignment, WHNF transport, and earlier
  preprocessing remain separate.
- `Verify.RecursorFieldScope` proves concrete declaration membership for generated
  fields in the retained RHS reader, under explicit initial `LocalContext.WF`
  and `ElimNestedInductive.ContextReserved` premises. These are structural
  context consistency and generator-freshness conditions, not semantic typing.
  `Context.RecursorScopeFrame` strengthens the immutable reader frame with final
  context validity/reservation and an ordered extension of the original local
  declaration list; its `oldLookup` projection preserves every previous
  successful native lookup. `LocalContext.WF.find?_of_mem` turns declaration-list
  membership into an exact concrete map lookup.
  `RecursorFieldsDeclared` records actual declarations, their field expressions,
  absent let-values, and default local-declaration kind. It has push, atom-shape,
  ordered-sublist, and native-lookup projections. `mkRecInfos.loopCtorArgs.scope`
  supplies valid/reserved extensions, declared fields, and ordered recursive
  selections to arbitrary continuations, without parameter atom, source typing,
  or positivity premises. Freshness is maintained through each actual allocation;
  skipped parameters allocate no declarations.
  `RecursorRuleRhsScopeReceipt` retains the same field/selection/value/context
  witnesses, counts, and literal RHS recipe while strengthening the retained
  reader and field membership. Its `fvars` compatibility projection recovers the
  earlier receipt, and `lookups` gives declared fields and selected fields in
  that same reader. Sequence compatibility/position projections and
  `mkRecRules.rhsScope` lift the contract through rule generation.
  `RecursorOffsetMetadata.localRuleRhsScope` joins stored rule traces to present
  parent-local minors, but keeps the actual source reader's validity/reservation
  premises explicit; local receipt compatibility also recovers the earlier atom
  contract without changing witnesses. This item does not establish those premises
  for the full runner's generated motive/minor source context. Seventeen audits
  use only standard logical axioms and, where needed, the existing persistent-array list-push and
  two map interfaces, excluding `sorryAx` and all expression/guarded-arity
  interfaces. No axiom, admission, or executable kernel change is added.
  Declaration presence does not establish freshness/uniqueness of the whole field
  vector, scope or semantic typing of declaration domains/recursive values,
  semantic RHS typing/reduction, index-binder alignment, WHNF transport, or
  preprocessing soundness. A helper context that violates reservation can
  overwrite an old native lookup; this is an explicit premise boundary, not a
  frontend divergence or kernel discrepancy.
- `Verify.RecursorFieldDistinct` strengthens the retained-reader field receipts
  with distinct expression identities. `RecursorFieldsDeclared.fresh` derives
  absence of the next generator identity from concrete declaration lookup and
  the explicit context validity/reservation premises; `nodup_push` preserves
  an existing distinct field vector when that fresh field is appended.
  `mkRecInfos.loopCtorArgs.distinct` carries declaration membership, distinctness,
  the scope frame, and ordered recursive-field selection through the same
  actual traversal witnesses. Selected recursive fields are distinct as a
  sublist, even when all source binder labels are identical. No parameter atom,
  semantic source typing, or positivity premise is added.
  `RecursorRuleRhsDistinctReceipt` keeps those same distinct field vectors,
  selected fields, recursive values, retained reader, counts, and exact RHS
  recipe coupled. Its scope compatibility and selected-distinctness projections
  do not replace the witnesses. Positional sequence projections and
  `mkRecRules.rhsDistinct` lift the receipt through actual rule generation.
  `RecursorOffsetMetadata.localRuleRhsDistinct` identifies stored rules and
  their actual parent-local minors using the existing flattened-minor indexing
  certificate. `mkRecInfos.registeredDistinct` strengthens the generation/
  registration suffix's coupled source/count/map/offset certificate with these
  installed rule receipts, discharging generated-reader validity/reservation
  from its existing source frame. Initial root context and map premises remain
  explicit; this is not a complete safe-run or frontend soundness theorem.
  Eleven axiom audits exclude `sorryAx` and expression/guarded-arity interfaces.
  Only existing logical, persistent-array list-push, and map interfaces are used;
  no axiom, admission, executable kernel change, cache, or fast path is added.
  Field distinctness does not prove semantic typing or scope of declaration
  domains/recursive values, RHS reduction, index-binder alignment, WHNF transport,
  or preprocessing soundness. Declaration membership alone permits duplicate
  vector entries; that unchecked control is not a kernel discrepancy.
- `Verify.RecursorInfoScope` propagates the actual structural local-context
  validity and name-generator reservation through `mkRecInfos`. Fuelled header
  index traversal, motive/major allocation, recursive-hypothesis allocation,
  constructor minors, and both parent traversals retain ordered local-declaration
  extensions and the immutable reader frame. Temporary readers used to compute
  normalized types or higher-order hypothesis types do not escape their binding
  continuations; persistent hypotheses/minors extend the actual source reader.
  `mkRecInfos.scope` supplies `Context.RecursorScopeFrame` to arbitrary
  continuations, given explicit root context validity/reservation. No source
  typing, parameter atom, or positivity premise is needed for this structural
  preservation theorem. `getScopeCounts` combines the scope frame with the
  existing count certificate using the same successful `(infos, current)`
  result, not separate existential witnesses.
  `mkRecInfos.scopeRegistration` is a verification-side wrapper retaining the
  actual recursor-info generation/registration suffix's environment, infos, and
  reader. `registeredScope` proves source scope/counts, final constant-map
  validity, all original environment lookups, exact offset metadata, and
  parent-local RHS scope receipts together. Its RHS receipts discharge their
  source context validity/reservation from the generated scope frame, rather
  than requiring additional source-reader premises. Initial root context
  validity/reservation and environment-map validity remain explicit.
  `InductiveHeaderScope` supplies the checked-header/root allocation bridge;
  `InductiveRunScope` now couples that prefix to the complete runner's suffix.
  The eight audits exclude `sorryAx` and expression or
  guarded-arity interfaces, using only existing logical/map/list-push interfaces.
  No axiom, admission, executable kernel change, cache, or fast path is added.
  These are structural source-reader and generated-field declaration guarantees,
  not semantic typing, recursive-value scope, generated index-binder alignment,
  WHNF transport, RHS reduction, or preprocessing soundness.
- `Verify.RecursorInfoIndices` records the actual successful normalization/index
  traversal: every reused parameter, freshly allocated index, WHNF result and
  reader, terminal non-forall and final parameter position. It proves parameter
  bounds, index-vector growth, declaration/scope retention and a raw outer-forall
  arity upper bound on consumed parameters plus emitted indices. Parent-local
  source receipts retain the initial header normalization, exact index vector,
  major datatype application, motive binding domain and actual allocation readers.
  The same receipts survive both parent traversals and every minor-array update;
  indices/major/motive declarations and exact major-type lookups persist in the
  final source reader. `getIndexSources` couples these receipts to scope/counts
  on the same successful infos/reader pair. `registeredIndexSources` retains
  them through the actual generation/registration suffix with constant-map
  validity, old lookups, exact offset metadata and local RHS scope receipts.
  Sixteen axiom audits exclude `sorryAx`, tracking existing binding/map/list-push
  interfaces; no executable kernel change, axiom or admission is added.
  This module alone does not prove equality between generated index counts and
  checked `stats.nindices`; `InductiveIndexAlignment` proves it for explicit
  sort-telescope headers. General normalization transport between checked-header
  and recursor readers/environments remains separate. Raw source arity is only a
  lower bound on normalized binder counts, and unchecked helper statistics need
  not be correct.
  Terminal helpers can succeed before consuming all parameters, and structural
  receipts do not establish header/source typing, terminal-sort validity, motive
  typing, RHS reduction or full inductive soundness.
- `Verify.InductiveHeaderTraces` retains the actual checked-header normalization
  and binder-consumption traversal. Its traces distinguish first-header shared
  parameter allocation, subsequent parameter reuse with the actual successful
  domain-type lookup and `isDefEq` check, and every fresh index allocation.
  Each body instantiation keeps its actual WHNF result and reader. Successful
  terminal traces require complete parameter consumption and a non-forall
  expression, preserve header arrays/levels and old parameters, and establish
  index-count growth, shared-parameter counts and structural scope extension.
  Per-parent source receipts retain the actual source-variable guard, original
  type-check result, initial WHNF, prefix statistics, traversal, final shared
  parameter vector, and terminal `ensureSort` result. The growing parent fold
  couples each trace's index count to the corresponding final `stats.nindices`
  entry and preserves exactly the same shared parameter vector through every
  later header. `scopedHeaderTraces` passes these receipts to arbitrary callbacks;
  `getHeaderTraces` couples them with scope, parameter counts, atom shape and
  distinctness on the same successful statistics/reader pair.
  Fourteen axiom audits exclude `sorryAx` and use only existing logical/map/list
  interfaces. No executable kernel change, axiom or admission is added.
  Checked-header counts and recursor-generated index vectors now both have
  actual traversal receipts. General equality still requires WHNF transport
  between different readers/environments; the explicit sort-telescope fragment
  is now discharged by `InductiveIndexAlignment`. Action-result equalities are
  not semantic typing/reduction theorems; direct unchecked helpers can start with
  inconsistent statistics or terminate at a non-sort. Complete inductive
  soundness, source typing, nested correctness and generated binder alignment
  remain separate obligations.
- `Verify.InductiveIndexAlignment` proves checked/generated index-count equality
  for explicit sort telescopes: zero or more `forallE` binders ending in `sort`,
  with arbitrary domains, binder information and universe levels. Substitution
  by any expression preserves the telescope and its raw binder count; successful
  WHNF fixes its outer view independently of the environment, local reader,
  fresh-name generator or successful normalization fuel. The actual checked
  trace consumes exactly its parameter/index binder count. The actual recursor
  trace consumes the minimum of available binders and remaining parameters,
  allocates exactly the remaining index binders, and retains both exact counts.
  Combining the same successful checked-header and recursor source receipts
  proves `info.indices.size = stats.nindices[parent]!` for every parent, without
  equating fresh variable names or assuming WHNF transport or count equality.
  `scopedAlignedIndices` passes these counts and source/scope receipts through
  arbitrary continuations; `getAlignedIndices` and `registeredAlignedIndices`
  preserve the same-success count, allocation, map, lookup, metadata and local
  RHS-scope certificates. `safeRegisteredIndexCounts` lifts the equality through
  the actual safe checked-header/constructor/generation/registration prefix,
  including both real declaration-environment extensions.
  Sixteen axiom audits exclude `sorryAx`, using only existing logical/binding/
  map/list interfaces. No executable kernel change, axiom or admission is added.
  This is a structural count theorem, not source/RHS typing, reduction soundness,
  correspondence of individual binder domains, K-target correctness or full
  inductive soundness. Aliases/annotations/let/beta forms in the binder spine
  remain outside this explicit fragment; aliases in binder domains are allowed.
  General normalized-spine transport and nested/preprocessing correctness remain
  separate, and bare helper statistics do not gain a validity certificate.
- `Verify.InductiveNormalizedHeaders` introduces `NormalizedSortTelescope`, an
  explicit canonical normalized-spine receipt: the normalized expression is an
  actual `SortTelescope`, and every reader/environment's successful `whnf`
  action on the source returns that same expression. `CheckedHeaderSource` and
  `RecursorInfoIndexSource` consume the same receipt to rewrite their actual
  successful initial WHNF results before applying the explicit-telescope count
  theorems. Consequently, `normalizedTelescopeIndexCounts` and its CPS/getter
  forms prove checked/generated index-count equality for any source whose
  normalization receipt is retained uniformly across both readers; they do not
  infer that receipt from an unchecked action or equate raw source arity with a
  normalized count. `registeredNormalizedAlignedIndices` preserves the same
  normalized-count proof through actual registration alongside source/scope,
  map/old-lookup, offset-metadata and local RHS-scope receipts.
  `safeRegisteredNormalizedIndexCounts` lifts it through the actual safe
  checked-header/constructor/generation/registration prefix and both environment
  extensions. Concrete wrapper normalization receipts are supplied separately
  by `InductiveNormalizedWrappers`, not assumed by those constructors.
  Ten native fixtures exercise annotated, let, beta and mixed source headers
  through actual checking, generation and registration. Three boundaries retain
  inconsistent bare counts and partial checked fuel behavior. Five original
  audits exclude `sorryAx`; existing `Expr.instantiate1_eq` and map/list
  interfaces are inherited. No executable
  kernel change, axiom or admission is added.
  This is a transport-aware structural certificate, not a semantic source/
  binder-domain/RHS typing or reduction theorem, and it does not establish
  nested/preprocessing/full inductive soundness.
- `Verify.InductiveNormalizedWrappers` constructs concrete canonical receipts,
  rather than assuming reader-independent normalization for each wrapper.
  `SortTelescope.normalized` supplies the identity receipt;
  `NormalizedSortTelescope.mdata` composes arbitrary outer metadata annotations
  with any existing receipt. `SortTelescope.normalizedLet` handles a direct let
  whose substituted body is an explicit sort telescope, and
  `SortTelescope.normalizedBeta` handles a single lambda application with an
  explicit telescope body. Both return the actual substituted expression,
  allowing used substitutions in binder domains and arbitrary binder metadata,
  values and environments. Outer annotation chains compose with both receipts.
  The proofs follow the actual fresh checker state, core/full WHNF actions and
  cache-save effects; they do not equate final states with direct telescope
  normalization. Depth and WHNF-loop exhaustion remain errors: these are
  successful-result certificates, not termination or typing theorems.
  Concrete proof fixtures pass the constructed receipts through the safe
  checked-header/constructor/registration count bridge without an external
  normalization premise. Finite mixed-wrapper receipts are supplied separately
  by `InductiveWrappedSpines`, not asserted by these direct constructors. Hidden
  aliases, wrapped telescope tails, pointwise binder-domain correspondence,
  semantic source/RHS typing, nested preprocessing and full inductive soundness
  remain separate. No executable kernel change, new axiom or admission is added.
- `Verify.InductiveWrappedSpines` defines `WrappedSortTelescope`, a finite
  syntactic reduction witness from a source expression to one explicit sort
  telescope. Its constructors retain actual metadata elimination and the
  substituted let/single-argument beta bodies, so mixed wrapper chains are
  proved recursively rather than assumed to inherit a full-WHNF receipt.
  Core normalization tracks the actual empty initial core cache, recursive
  method depth and cache-save effects; successful output states may differ.
  Lifting the core receipt through full WHNF proves one canonical normalized
  expression for all readers/environments without a normalization oracle.
  Substitution values and binder domains need not be closed or well typed for
  this structural theorem. Fuel exhaustion remains an error, not a successful
  normalization claim. Hidden aliases, projections, wrapped binder-spine tails,
  semantic reduction/typing and arbitrary normalization remain outside this
  finite head-wrapper fragment.
- `Verify.InductiveWrappedHeaders` lifts those syntactic witnesses to each
  parent via `WrappedHeaderTelescope`. `normalizedHeaders` constructs the
  canonical receipts consumed by the existing checked/recursor traces;
  `wrappedTelescopeIndexCounts` therefore proves actual checked/generated
  equality, not raw source-arity equality. `registeredWrappedAlignedIndices`
  retains the count proof alongside source/scope, map/lookup, offset-metadata
  and local RHS-scope certificates. `safeRegisteredWrappedIndexCounts` passes
  it through actual safe checking, both datatype/constructor environment
  extensions, generation and registration. No new executable path, cache,
  axiom or admission is added. Domain alpha-correspondence, source/RHS
  typing, nested preprocessing and full inductive soundness remain separate.
- `Verify.InductiveBinderDomains` retains each actual telescope-opening step:
  parameter/index role, source name, raw domain, binder information and chosen
  substitution expression. `OpenedTelescope` follows `body.instantiate1` at
  every step, avoiding a batch-substitution or closed-argument assumption.
  The checked extractor jointly proves that parameter values are the actual
  final/shared parameter array, counts index values, and retains exact index
  declaration lookup/type/name/binder-info equations in the successful reader.
  The generated extractor retains the actual `info.indices` array and the
  precise consumed parameter prefix. The consumed local domain is the actual
  `rawDomain.consumeTypeAnnotations` used by allocation. Reused parameters
  remain pure source-opening steps: their existing declaration type is checked
  by `isDefEq`, not asserted equal to that consumed raw domain.
- `Verify.InductiveBinderAlignment` pairs checked/generated openings of the
  same canonical normalized source. The successful checked count proves
  complete generated parameter consumption, so both opening histories use the
  same actual shared parameter array. Index values and reader contexts remain
  separate. `ParentBinderDomainAlignment` retains exact separately opened
  domains, index counts/values and native declaration lookup receipts; it also
  proves identical ordered binder names and binder information. Its CPS/getter
  bridges preserve count/source/scope certificates; registration additionally
  retains map/old-lookup, offset metadata and local RHS-scope certificates from
  the same success.
  The normalized/wrapped safe-prefix theorems retain the actual checked-header
  reader/source witness through both real declaration-environment extensions,
  constructor checking, generation and registration. Concrete finite wrapper
  witnesses supply canonical normalization rather than assuming an oracle.
  This is paired domain provenance, not equality of domains containing
  different fresh IDs, alpha-correspondence, semantic binder/source/RHS typing
  or full inductive/nested soundness. No executable kernel path, cache, new
  axiom or admission is added.
- `Verify.InductiveBinderPrefixes` strengthens the actual checked/generated
  opening receipts with ordered parameter-then-index roles. The parameter
  history, role prefix, index values/counts and native declaration lookups
  belong to the same witness. Checked success supplies the parameter bound
  needed for complete generated consumption; unchecked helper calls can still
  leave extra parameters unconsumed.
- `Verify.InductiveBinderOpening` proves deterministic sequential opening
  through any equal prefix of substitution values and roles. The complete
  prefix steps agree, and the immediately following raw and consumed domain
  agree, including the case where neither opening has another binder. These
  structural proofs use only `propext`; arbitrary substitution expressions
  are permitted, without closedness or batch-substitution assumptions.
- `Verify.InductiveBinderPrefixAlignment` couples those facts to each parent's
  actual shared parameter array. Checked/generated parameter steps are exactly
  equal, and their first index domains agree syntactically, before and after
  annotation consumption. Native index-declaration receipts remain anchored
  in their separate successful readers; `firstIndexTypeAgreement` proves that
  the natively found first declarations have exactly equal stored types when
  both heads exist, without identifying their fresh IDs.
  CPS/getter/registration and concrete
  normalized/wrapped safe-prefix bridges retain the stronger alignment;
  projections recover the previous paired-domain contracts. This compares
  two openings of the same parent, not different mutual parents' parameter
  source syntax. Later dependent index domains can still differ with fresh
  IDs; general index renaming, semantic typing, hidden aliases/tails, nested
  preprocessing and full inductive soundness remain separate. No executable
  checker path, cache, new axiom or admission is added.
- `Verify.InductiveIndexRenaming` defines finite structural correspondence:
  a free variable keeps its ID or follows an explicitly listed pair; all
  other constructors, constants/levels, literals, metavariable IDs, binder
  metadata and projection metadata remain exact. Reflexivity, pair-list
  monotonicity, loose-variable lifting and sequential instantiation are proved
  for arbitrary substitution expressions. This is an identity-or-paired
  relation, not a deterministic substitution map, bijection, typing theorem
  or semantic equivalence. Structural proofs are axiom-free except the
  signature proof (`propext`) and actual instantiation bridge (the existing
  `Expr.instantiate1_eq` interface).
  `ConsumedIndexRenaming` retains related raw expressions and exact equations
  for their total `peelTypeAnnotations` outputs. Deterministic consumed
  correspondence is proved separately by `ConsumedIndexLookupRenaming`.
  The external `Expr.consumeTypeAnnotations` remains opaque and has no safe
  equation interface here; no universal native-equivalence axiom is added.
- `Verify.InductiveBinderCorrespondence` couples the actual two telescope
  openings. Parameter values remain identical; each index value is proved
  to be a native declaration's actual free variable before its IDs are paired.
  Each raw domain is structurally related using only preceding index pairs;
  the current pair is appended for the following body substitution. Consumed
  local domains retain exact raw-domain provenance. `finalPairs` proves the
  final chronological list is precisely the zip of actual index-value IDs;
  `pairedIndices` also retains terminal correspondence. No independent
  existential histories are combined.
- `Verify.InductiveBinderRenamingAlignment` strengthens each existing joint
  prefix witness with that sequential correspondence and its actual final
  index-pair zip. `indexHeadTypes` projects a residual index node to the two
  natively found declaration types and consumed provenance under exactly its
  incoming prior pairs. `renamingTypes` similarly lifts explicit declaration
  anchors and raw correspondence. Normalized/wrapped source, CPS/getter,
  registration and safe-prefix bridges retain the stronger same-reader
  receipts; projections recover previous prefix/domain contracts. Shared
  parameter-step equality and first-index exact type agreement still hold;
  later dependent domains and fresh IDs remain concretely unequal. Distinct
  or injective pairs, global alpha-renaming, annotation-reduction semantics,
  semantic typing, hidden aliases/tails, nested preprocessing and full
  inductive soundness remain separate. No executable kernel path, cache,
  new axiom or admission is added.
- `Verify.InductiveIndexPositions` retains each native index declaration's
  exact stored `LocalDecl.index`, in addition to lookup, expression, domain,
  user name and binder information. `BinderIndexAllocations` skips parameters
  and advances positions exactly once per index. Its ordinal projection
  retains the exact declaration position; increasing positions under the
  same reader's functional lookup prove distinct index IDs.
  `IndexPairInjection` records duplicate-free source and target projections;
  `of_zip`, `functional` and `injective` prove uniqueness of listed pairs.
  Generic zip projections may truncate, while `indexZipExactProjections`
  explicitly requires equal lengths to retain both whole lists.
- `Verify.InductiveBinderAllocations` strengthens the original opening
  extractor with native positions in the same induction/witness as parameter
  history, ordered roles, index counts/values and declaration lookup evidence.
  The checked base is entry `decls.size` plus remaining freshly allocated
  parameters for the first header; reused parameters do not shift it.
  Generated parameters are all reused, so the generated base is entry
  `decls.size`. Scope frames preserve exact stored declarations and positions.
- `Verify.InductiveBinderAllocationAlignment` couples those stronger
  checked/generated histories, their sequential raw-domain correspondence
  and the injective actual index-ID zip. `injectiveIndexZip` retains exact
  checked count and whole source/target projections, not truncated prefixes.
  Normalized/wrapped source, CPS/getter, registration and safe-prefix bridges
  retain the stronger same-reader receipts; projections recover previous
  renaming/prefix/domain contracts. An older existential domain-only witness
  is not independently merged with a new allocation history.
  Certified inputs retain the existing dense `LocalContext.WF` premise;
  erased/hole-containing readers are outside it. Stored declaration-index
  receipts are not an arbitrary physical `getAt?`-slot theorem. Pair zip
  injectivity does not imply disjoint source/target IDs or functionality of
  the identity-or-listed-pair expression relation. Structural
  external native annotation-consumption compatibility, semantic typing,
  hidden aliases/tails, nested preprocessing and full inductive soundness
  remain separate. No executable kernel path, cache, new axiom or admission
  is added.
- `Verify.InductiveIndexLookup` supplies deterministic finite index lookup:
  native listed lookup takes precedence over identity, which applies outside
  the source projection. Injective pair receipts prove exact lookup of every
  listed pair. `IndexParameterSupport` explicitly excludes shared parameter
  IDs from that source projection and proves they are fixed. The structural
  `indexRenameExpr` and functional `IndexLookupRenaming` imply the existing
  identity-or-listed-pair relation, not conversely. Even an injective pair
  list need not give a globally injective identity-defaulting function.
- `Verify.InductiveBinderSupport` and
  `Verify.InductiveBinderSupportAlignment` retain shared-parameter/index ID
  separation in the same checked/generated histories as native allocation,
  declaration lookup and sequential raw-domain correspondence. Their exact
  index zip supports deterministic lookup and excludes shared parameters
  from both projections. Normalized/wrapped source, CPS/getter, registration
  and safe-prefix bridges retain those stronger receipts and project previous
  allocation contracts. This is a finite-support boundary, not a claim that
  source and target IDs are disjoint across readers, that every related raw
  domain equals the deterministic structural result, or that external native
  annotation consumption respects structural renaming. Semantic typing, hidden
  aliases/tails, nested preprocessing and full inductive soundness remain
  separate. No executable checker path, cache, new axiom or admission is added.
- `Verify.InductiveHeaderParameterSupport` strengthens actual checked-header
  source extraction with the parameter declaration boundary at each source's
  entry reader and at the final header reader. Ordinary independent source
  predicates do not imply this boundary: checked reuse performs `getType`
  through a defaulting lookup, while recursor opening reuses parameter values
  without a declaration check. The low-level support bridges therefore use
  supported checked sources and an explicit generated-root declaration
  boundary; the actual safe-prefix bridge derives both from the successful
  checked-header traversal. It never merges independent opening witnesses or
  assumes equality of reused declaration types with raw/consumed domains.
- `Verify.InductiveIndexLookupSubstitution` proves deterministic renaming
  commutes with structural loose-variable lifting and single substitution at
  arbitrary depths, including replacements containing loose bound variables.
  Native `instantiate1` uses only the existing structural-instantiation
  interface. The functional relation inherits these operations and preserves
  binder signatures. No pair injection or support premise is needed for
  commutation under the same finite lookup.
- `Verify.InductiveIndexLookupSupport` gives explicit structural free-variable
  containment/exclusion and bridges them to the existing pure `fvarsList`
  traversal. Appending one fresh source key maps that key to its listed target
  and leaves every other lookup unchanged; a source body excluding that key
  therefore retains its previous structural renaming. Arbitrary old duplicate
  keys are permitted in the stability theorem. Expressions supported solely
  by the excluded shared-parameter IDs remain entirely fixed.
- `Verify.InductiveIndexLookupOpening` combines those facts into fresh-index,
  already-mapped-index and fixed-parameter opening rules. Native current-index
  opening requires declaration lookups for incoming source keys and explicit
  `SourceReserved` for the incoming body; context reservation alone does not
  reserve arbitrary body FVars, and scope frames do not imply generator
  monotonicity or transport reservation through normalization. Pair injection
  survives extension when both projected IDs are fresh; parameter support
  survives when the new source is outside the parameter IDs. Actual native
  parameter-declaration receipts discharge that last freshness condition.
  `ParentBinderSupportAlignment.openingLookup` retains the same actual full
  index zip, count, projections and parameter-support receipts, adding the
  conditional opening operations for deterministically related input bodies.
  It does not assert that the actual later raw domains already satisfy that
  stronger relation or that external native annotation consumption preserves it. Semantic
  typing, normalization support, hidden aliases/tails, nested preprocessing
  and full inductive soundness remain separate. No executable checker path,
  cache, new axiom or admission is added.
- `Verify.InductiveNormalizedFreeVars` proves structural free-variable support
  survives loose-variable lifting and single substitution. The explicit
  wrapped-telescope normalization trace yields a free-variable subset of its
  original source, including beta and let substitution. Actual checked-source
  guard correctness then proves wrapped normalized headers contain no free
  variables. If another normalized witness is selected, equality follows from
  the successful normalization receipt inside the same source record; no
  general normalization-scope theorem or metadata axiom is invented.
- `Verify.InductiveBinderLookupCorrespondence` strengthens sequential raw
  domains to the deterministic lookup relation at exactly the incoming pair
  list. Parameter nodes retain that list; index nodes append their actual
  checked/generated IDs. Its exact final zip and terminal correspondence are
  proved for the same opening histories. Explicit initial source support,
  parameter FVar shapes, shared-parameter exclusion and full finite-pair
  injection provide fresh-body/key support at each step. Generic incoming
  pairs are permitted; overlapping source/target IDs do not require global
  separation. Projection recovers the old structural relation and consumed
  raw-domain provenance. Total peeling additionally yields deterministic
  correspondence of the actual stored types under the same incoming map.
- `Verify.InductiveBinderLookupAlignment` retains those deterministic domain
  receipts in the same actual parameter/index histories, allocation positions,
  native declaration lookups and pair zip as the supported-source alignment.
  The normalized bridge states source support explicitly; the wrapped bridge
  discharges it through checked guards and proved wrapper scope. CPS/getter,
  registration and safe-prefix contracts retain the stronger receipts and
  project the previous support contracts. Reused parameter declaration types
  still have only their actual definitional-equality checks; the new raw-domain
  theorem does not turn those checks into raw/consumed type equality. General
  normalization support, external native annotation-consumption compatibility,
  semantic typing, hidden aliases/tails, nested preprocessing and full
  inductive soundness remain separate. No executable checker path, cache,
  new axiom or admission is added.
- `Verify.InductiveConsumedLookupRenaming` projects deterministic raw-domain
  correspondence onto native index declaration types. Its consumed relation
  retains the actual raw origins, their deterministic lookup equation, and
  both total `peelTypeAnnotations` equations. It implies the previous structural
  raw-provenance receipt and, through `toIndexLookupRenaming`, deterministic
  correspondence of the actual consumed outputs for arbitrary pair lists.
  Native lookup anchors identify both stored declaration types; no external
  native annotation-consumption equation is required.
- `Verify.InductiveBinderLookupPositions` projects each binder position onto
  exactly the incoming map: the initial pairs followed by the zip of index IDs
  strictly before that position. The current and future index pairs are absent;
  parameter binders neither extend the map nor advance index allocation ordinals.
  The native allocation projection records each stored `LocalDecl.index` as its
  history's starting index plus the number of preceding index binders, without
  asserting physical-slot access or additional declaration-type equalities.
- `Verify.InductiveBinderLookupTypes` retains these all-index receipts inside
  the same actual checked/generated opening histories, allocation bases,
  terminal correspondence and full index zip. Each native declaration lookup
  has the matching value, name, binder information, exact stored position and
  consumed local type, with deterministic raw provenance at that position's
  incoming map. Parent/recursor projections recover the previous alignment;
  normalized and wrapped source bridges, CPS/getter, registration and safe
  prefixes preserve the stronger receipt on the same successful result. Source
  support remains explicit for the normalized bridge and guard-derived for
  supported wrappers. Identity and overlapping index IDs remain allowed.
  Reused parameter declaration types keep only their actual `isDefEq` checks;
  they are not included in the new native type relation. External native
  consumption compatibility, semantic typing, arbitrary normalization support and full
  inductive soundness remain separate. No checker path, cache, new axiom or
  admission is added.
- `Verify.InductiveBinderRawScope` proves chronological FVar support for the
  actual raw domains in an opened telescope. Each domain is supported by the
  initial parameter IDs plus the IDs of index binders strictly before its
  position. Parameter substitutions stay in that initial support; index
  substitutions extend it only after their own domain has been checked.
  Parameter FVar shapes and native index declaration receipts discharge the
  substitution premises. Arbitrarily interspersed roles and overlapping IDs
  are permitted by this generic support theorem; no freshness or global
  separation premise is needed. This is FVar support, not a proof of loose
  bound-variable closure, metavariable absence or semantic typing.
- `Verify.InductiveBinderRawScopeExclusion` combines that incoming support
  with one history's full index-ID distinctness and parameter/index
  disjointness to exclude every current or later index ID from a raw domain.
  Full checked/generated distinctness is recovered from the same deterministic
  correspondence and injected final pair list, without cross-history ID
  separation or an arbitrary-map-extension assumption.
- `Verify.InductiveBinderRawScopeAlignment` retains both histories' raw-domain
  support and current/future-index exclusions inside the same native-type
  witnesses, preserving all previous openings, lookups, allocation bases,
  exact pair maps and consumed raw-provenance receipts. Normalized source
  support remains explicit; supported wrappers discharge it through the
  actual source guards. CPS/getter, registration and safe-prefix bridges
  preserve the stronger receipt on the same successful result. Actual stored
  types now use total peeling; `InductiveAnnotationStoredTypes` projects raw
  support, avoidance and deterministic correspondence to those exact types.
  No semantic local typing is inferred from syntactic support. In pinned
  Lean 4.29.0, the external native
  `Expr.consumeTypeAnnotations` declaration is opaque and exposes no imported
  safe defining-equation interface; runtime stripping controls are not a
  theorem bridging it to a total model. Reused parameter types retain their
  original definitional-equality checks. No cache, new axiom or admission
  is added; full inductive soundness remains separate.
- `Inductive.Annotation` implements total structural leading type-annotation
  peeling as `Lean4Lean.AddInductive.peelTypeAnnotations`. All thirteen local
  allocation sites in `Inductive.Add` use this utility instead of the opaque
  native consumer, and their trace/context/domain receipts use the same
  executable definition. `Verify.InductiveAnnotationModel` imports that utility
  and proves its defining equations. Exactly unary `outParam`/`semiOutParam` applications
  and binary `optParam`/`autoParam` applications peel to their carrier, repeating
  along that leading carrier chain only. Binary defaults/tactics are discarded;
  universe arguments do not affect recognition. Wrong arities, metadata and
  annotations inside ordinary nested expressions remain unchanged. Its safe
  defining equations describe this checker's actual consumer, not a universal
  equality to the opaque external native consumer. No cache or fast path is added.
- `Verify.InductiveAnnotationModelScope` proves model output FVars are a subset
  of input FVars, preserves syntactic support and avoidance, and proves model
  idempotence. `Verify.InductiveAnnotationModelRenaming` proves the model
  commutes with deterministic FVar renaming for arbitrary pair lists, including
  duplicate keys, identity pairs and overlapping supports. Exact constant-head
  arity tests are also preserved. No injection or separation premise is needed
  for these model theorems, and no native consumption interface is assumed.
- `Verify.InductiveAnnotationStoredTypes` projects chronological raw-domain
  scope and current/future index exclusion to the actual total-consumer local
  domains. Native declaration type projections retain the same steps, lookups,
  names, binder information, allocation positions and exact strictly-prior
  pair lists while deriving stored-type support and deterministic
  correspondence. Parent histories keep the same normalized telescope,
  shared parameters and whole actual index-ID zip. These results require the
  existing raw receipts but no native/model compatibility premise. Discarded
  binary defaults cannot introduce FVars into stored types. Reused parameters
  retain only their original `isDefEq` checks. No semantic typing, unrestricted
  normalization or full inductive-soundness claim is introduced.
- `Verify.InductiveBinderStoredTypeAlignment` bundles those unconditional
  stored-type facts into the same parent witnesses as the complete raw-scope
  receipt. Normalized source/opening histories, shared parameters, role
  prefixes, declaration lookups, binder metadata, allocation positions,
  full index-ID zip and exact strictly-prior maps remain coupled. Both
  histories retain stored-domain support and current/future index exclusion;
  each actual index declaration retains deterministic stored-type
  correspondence. Projection recovers the previous raw-scope contract.
  Source bridges, arbitrary CPS continuations, getters, recursor registration
  and safe normalized/wrapped prefixes deliver the stronger receipt for the
  same successful result, not independently selected existential histories.
  Normalized headers still require explicit source support; supported wrappers
  discharge it through the existing checked source guards. No external
  native/model compatibility premise, reused-parameter syntactic type equality,
  semantic local typing or full inductive soundness is asserted. These are
  proof-only result contracts; no checker path, cache, new axiom or admission
  is added.
- `Verify.InductiveAnnotationModelFVarsIn` proves total peeling preserves
  `Expr.FVarsIn` for arbitrary FVar predicates. Unlike FVar-only support, this
  predicate also excludes expression and universe metavariables. Its native
  `hasMVar = false` projection uses the existing expression/level interfaces,
  not a native annotation-consumption equation. Preservation is not reflection:
  discarded binary defaults and annotation-head universe arguments may contain
  metavariables that disappear from the peeled result.
- `Verify.InductiveBinderFVarsIn` preserves this integrity through native
  single substitution and explicit metadata/let/beta normalization traces.
  Successful checked-source guards supply source integrity; the normalized
  projection uses the same successful normalization witness, not an unrelated
  existential telescope. FVar binder opening gives every raw domain exactly
  the initial parameter IDs plus strictly-prior index IDs, excluding expression
  and universe metavariables at the same time. General normalized headers
  retain an explicit `NormalizedHeaderFVarsIn` premise; no generic WHNF
  integrity theorem is assumed. Projection recovers the old FVar-only scope.
- `Verify.InductiveBinderIntegrity` retains the full previous raw/stored
  parent contract and appends both histories' raw-domain, peeled index-domain
  and actual native-declaration-type integrity on those same witnesses. Native
  lookup uniqueness ties each type fact to the declaration already selected by
  its own allocation receipt. Normalized/wrapped source and successful result
  contracts carry these facts without native/model compatibility premises;
  supported wrappers discharge integrity through the checked source guards.
  This remains syntactic FVar membership and metavariable absence: `FVarsIn`
  permits loose BVars and does not establish semantic typing. Reused parameter
  declaration types keep their original `isDefEq` checks, not a new literal
  type-equality claim. No runtime checker change, cache, new axiom or admission
  is introduced; full inductive soundness remains separate.
- `Verify.InductiveAnnotationNativeScope` provides explicitly conditional
  bridges. `NativeAnnotationModelAt` is a pointwise equation between one raw
  expression's native consumed output and the total model; it is a premise,
  not an axiom or a universal compatibility theorem. Raw support/avoidance
  transfers to native consumption only with that expression's model premise;
  deterministic consumed renaming requires premises for both actual raw
  domains. Binder model receipts cover actual index domains only. A native
  type projection retains the same declaration lookups and exact incoming
  map. Actual stored-type scope and deterministic correspondence now follow
  directly from total peeling; its two final external-native type equalities
  still require the explicit compatibility premises. Runtime comparison controls do not discharge them
  in the kernel. Reused parameters, native defining-equation availability,
  semantic typing and full inductive soundness remain separate. No cache,
  new axiom or admission is added.
- `Verify.InductiveAnnotationOpeningShape` proves that actual FVar binder
  instantiation preserves exact constant-head arities. It cannot create a
  constant or an application from another constructor, so the original unary
  and binary annotation heads are recovered from their opened shapes. A
  counterexample proves why unrestricted replacement is excluded: replacing
  a function-position BVar by an annotation constant can create a new head
  that the model then peels. No freshness, scope or global ID separation
  premise is required for the FVar shape theorem.
- `Verify.InductiveAnnotationModelOpening` proves total-model peeling commutes
  with FVar `instantiate1'` at every depth, including loose bound variables.
  Its `instantiate1` projection uses the existing native instantiation equation,
  not a native annotation-consumption equation. The replacement may coincide
  with an existing FVar; arbitrary expression replacement is not claimed.
- `Verify.InductiveAnnotationBinderOpening` transforms each syntactic telescope
  domain using the total model and proves that the same actual FVar opening
  history opens the transformed telescope. Binder values, parameter/index
  vectors, roles, names and binder information remain unchanged; the final
  sort remains the same. Actual parameter shapes and native index declarations
  discharge the FVar-value premises. The same deterministic incoming pair
  correspondence and chronological raw-domain support project to model-domain
  histories. Original-history local domains are definitionally total-model
  outputs; peeling transformed domains again yields the same types by proved
  idempotence. This does not identify either domain with the external native
  consumer without compatibility.
  Native consumption/opening commutation remains conditional on pointwise
  model equations for both the original and the opened raw expression. No
  automatic native-equation transport, unrestricted substitution theorem,
  new axiom or admission is introduced.
- `Verify.InductiveHeaderScope` proves structural context validity, generator
  reservation, and ordered declaration extension through `checkInductiveTypes`.
  Initial `LocalContext.WF` and `ContextReserved` remain explicit. The fuelled
  binder traversal distinguishes first-header shared parameter allocation,
  subsequent-header parameter reuse, and every datatype's fresh index allocation.
  Normalization, source/type guards, mutual parameter/universe checks, and
  arbitrary continuation failures retain their existing behavior. The complete
  parent traversal supplies `Context.RecursorScopeFrame` to arbitrary callbacks.
  `getScopeStats` couples the frame with header sizes, parameter counts, atom
  shape, and parameter distinctness using the same successful statistics/reader
  pair, not independent existential witnesses.
  `Context.RecursorScopeFrame.withEnv` uniformly rebases both ends of a structural
  frame without claiming semantic typing or WHNF transport. It permits
  `constructorRootScope` to retain the actual header/positivity reader across
  constructor registration, for either low-level safety flag.
  `getScopedConstructorRegistration` couples that exact root with its existing
  safe constructor-registration certificate and distinct installed-constructor
  environment. It does not replace the original positivity root by the final
  environment. Six structural audits use only logical/map/list-push interfaces;
  the seventh additionally inherits the existing third map and six constructor
  metadata/arity interfaces. All exclude `sorryAx`; no new axiom, admission,
  executable kernel change, cache, or fast path is added.
  `InductiveRunScope` now composes this prefix into complete safe runs.
  Context consistency and
  declared-field presence are not semantic typing of declaration domains or
  recursive values, source reconstruction, generated index alignment, RHS
  typing/reduction, normalization transport, or preprocessing soundness.
  Empty batches with nonzero declared parameter counts remain proof-only
  terminal-assertion boundaries, not runtime acceptance claims. An unreserved
  helper context can overwrite an old native lookup; this is an explicit premise
  boundary, not a frontend/kernel discrepancy.
- `Verify.InductiveCPS` proves uniform continuation morphism equations for
  checked headers and recursor-info generation. Capturing the actual result and
  reader before binding an arbitrary callback equals running that callback in
  the original CPS traversal, including prefix failures and callback errors.
  Every fuelled binder loop and finite parent/constructor traversal is covered;
  temporary hypothesis-type computations remain encapsulated rather than
  replaced by a fabricated reader. These equations use only standard logical
  axioms. `checkInductiveTypes.scopedStats` and `mkRecInfos.scopedCounts` derive
  arbitrary-continuation contracts from the existing coupled collectors, so
  structural scope and statistics/counts refer to the same captured witnesses.
  Their audits inherit only existing logical/map/list-push interfaces.
- `Verify.InductiveRunScope` removes additional root/source-context premises
  from the complete safe-run RHS scope/distinctness contract. Initial safety,
  constant-map validity, `LocalContext.WF`, and generator reservation are the
  only caller premises. `safeScopedConstructorRegistration` combines checked
  statistics, structural root scope, actual positivity traces, and installed
  header/constructor metadata in one continuation. `InductiveStats.SafeRunScope`
  extends the earlier complete registration certificate with the exact header/
  positivity root frame and coupled elimination level, infos, source reader,
  K flag, source scope/counts, exact offset metadata, and local-minor distinct
  RHS receipts. The intermediate constructor environment remains distinct from
  both that original positivity root and the final environment.
  `run.safeScope` proves this certificate for the actual complete runner.
  `run.safeRhsDistinct` retains final map validity and all original constant
  lookups alongside its coupled certificate/source/rule witnesses. Compatibility
  recovers the previous minor-offset certificate; local and original-reader
  projections preserve actual source frames and distinct receipts. The
  original-reader projection composes structural rebasing/extension only,
  without assuming typing or normalization transport between environments.
  All ten axiom audits exclude `sorryAx`. Composition uses only existing
  logical, persistent-array list-push, three map, and six constructor metadata/
  arity interfaces. No new axiom, admission, executable change, cache, or fast
  path is added. This is structural/operational verification, not semantic
  inductive or public frontend soundness. Semantic declaration-domain/value
  typing, generated binder/index alignment, RHS typing/reduction, WHNF transport,
  and nested preprocessing correctness remain separate. Empty batches with
  nonzero parameter assertions remain proof-only boundaries.
- `Verify.InductiveFrontendScope` lifts the complete safe-run structural
  certificate through the actual safe public `Environment.addInductive`
  no-nested-auxiliary branch. `inductivePreprocessing` names the exact existing
  preprocessing computation, and `inductiveScopeContext` retains the runner's
  actual empty initial local context. `safeStages` supplies the original-source
  preflight contract and a successful preprocessing witness for every successful
  safe public addition; only when that witness has zero nested auxiliaries does
  it attach the complete `SafeRunScope` certificate to the public final
  environment. `NonNestedInductivePreprocessing` records this operational
  branch condition, not a syntactic or semantic classification of source types.
  `of_result` discharges it from a specific successful preprocessing result and
  its zero auxiliary count. `safeNonNested` and `safeNonNestedResult` produce
  `NonNestedInductiveScope`, retaining the exact rewritten `preprocessing.types`,
  checked header/positivity root, separate constructor environment, actual
  recursor source reader, counts, offsets, and declared distinct RHS fields.
  Initial local-context validity and generator reservation are discharged from
  the empty runner context, leaving original map validity and the operational
  no-auxiliary premise as caller obligations. `preserves` and `localRules`
  project map validity, all old constant lookups, and the coupled actual-source
  rule receipt without replacing the preprocessing witness. The actual
  `addDecl.safeNonNestedInductive` primitive-dispatch branch works with either
  `check` flag and retains the runner's selected `allowPrimitive` value;
  `safeNonNestedPreserves` exports its preservation contract. All eight audits
  exclude `sorryAx` and inherit only existing logical/map/list-push and
  constructor metadata/arity interfaces. No executable code changes. These
  contracts do not prove preprocessing equals the original source, nested
  transformation/restoration correctness, semantic inductive soundness,
  declaration-domain/value typing, generated binder/index alignment, RHS typing
  or reduction, or WHNF transport. The nested branch of `safeStages` deliberately
  supplies no final-run certificate, and failed preprocessing is not acceptance.
- `Verify.InductiveFrontendRestoration` extends structural map preservation
  through the actual public safe frontend's nested restoration branch.
  `FreshRegistrationTrace` records an ordered chain of fresh insertions with an
  explicit allowed-record predicate; its composition and preservation theorems
  retain constant-map validity and all old lookups. `lookup`/`newLookup` further
  show every final record is either an unchanged original or one allowed by the
  trace. `RestoredInductiveRecord` fixes the exact staged lookup and existing
  restoration recipe for each emitted header, constructor, and main/renamed
  auxiliary recursor, including exact restored rule constructor names and RHSs.
  Proof-facing restoration actions mirror the current datatype/constructor/
  recursor loops and final auxiliary type-check gate. Their trace theorems
  compose without semantic premises on restoration or auxiliary checking;
  checks may still fail, and no postcondition assumes their success in advance.
  The actions are verification-only: `safeFrontend` unfolds them against the
  actual existing `Environment.addInductive` path, with no executable kernel
  change. `SafeInductiveFrontendScope` retains original map validity, source
  preflight, exact successful preprocessing, the complete scoped rewritten-run
  certificate, and an explicit direct-versus-nested final branch receipt. A
  direct result is the staged environment with zero auxiliaries; a nested
  result is a fresh restoration trace starting from the original environment,
  not an extension of the staged auxiliary environment. Its preservation
  projection, `Environment.addInductive.safePreserves`, and both `addDecl`
  specializations need only original map validity, with no no-auxiliary premise.
  Actual primitive dispatch and either declaration check flag are covered.
  All fourteen audits exclude `sorryAx`; trace composition is logical, restoration
  traces inherit the existing freshness-check map interface, preservation/lookup
  adds existing map interfaces, and complete frontend composition additionally
  inherits existing list-push and constructor metadata/arity interfaces.
  These are exact operational record/freshness receipts, not semantic
  preprocessing/restoration correctness or inductive soundness. They do not
  prove all expected restored records are installed, unreachable/assertion
  branches never occur, auxiliary expression typing, restored RHS typing or
  reduction, generated binder/index alignment, or WHNF transport. Lean-level
  panic defaults are handled structurally, not asserted unreachable.
- `Verify.InductiveRestorationMetadata` proves complete final installed-record
  receipts for successful nested restoration under explicit staged source
  coverage. Pure record lists retain the exact original-header, staged
  constructor, main-recursor, and renamed auxiliary-recursor traversal recipes.
  `RestoredRegistrationReceipt` couples final map validity, all old lookups, and
  every exact list entry's final lookup. Receipt composition preserves earlier
  records through subsequent fresh registrations instead of asserting only
  allowed-record origin. Individual recursor/constructor proofs retain exact
  rewritten types/rules; constructor and datatype receipts also return `.yield`,
  so complete list traversal cannot silently stop before later records.
  `RestorationDatatypeSources`/`RestorationSources` make all typed staged
  lookups explicit and prevent missing-record panic/default branches from being
  mistaken for successful complete installation. The complete batch receipt
  survives the final auxiliary-check gate, including its possible failures.
  Header, constructor, main-recursor and auxiliary-recursor projections expose
  exact final metadata records, not just new-record classification.
  `RestorationNameCoverage` separates original datatype-name and generated
  auxiliary-rec name-map membership obligations from typed lookup coverage.
  `SafeRunScope.restorationSources` derives all typed sources from the same
  complete checked rewritten-run certificate once name coverage is supplied.
  `SafeInductiveRestorationMetadata` retains exact successful preprocessing and
  runner equations, the same root/constructor/source certificate and direct/
  nested branch trace, and a conditional complete installed-record receipt.
  `Environment.addInductive.safeRestorationStages` and actual `addDecl` dispatch
  construct this coupled receipt with only initial map validity; `installed`
  and `installedFromNames` discharge its conditional restoration receipt from
  source or pure-name coverage respectively. Neither substitutes unrelated
  existential preprocessing/runner witnesses. The previous unconditional map
  preservation certificate is recovered by projection. All seventeen added
  audits exclude `sorryAx`; only existing logical/map/list-push and constructor
  metadata/arity interfaces are inherited. No executable kernel change or new
  axiom/admission/cache/fast path. This module's low-level installation receipts
  remain conditional on staged coverage; the following module derives it from
  actual preprocessing and checked rewritten metadata. Semantic source
  or restored typing/reduction, nested transformation/restoration correctness,
  generated binder/index alignment, WHNF transport, auxiliary expression typing,
  and inductive soundness remain separate obligations.
- `Verify.InductiveRestorationNames` discharges that coverage obligation without
  a caller-supplied source/name premise. `InductiveNamePrefix` records size
  monotonicity and every original datatype name at its original position, not
  just membership. Compositional proofs cover parameter extraction, nested
  replacement, all expression-traversal branches, auxiliary pushes, and
  constructor rewriting in the growing preprocessing loop. Successful
  `inductivePreprocessing` preserves this prefix. `mkAuxRecNameMap.names` proves
  the exact ordered recursor-name enumeration of the staged header's datatype
  suffix, retaining the empty logical default when its length assertion fails.
  `SafeRunScope.restorationNameCoverage` joins the positional prefix with exact
  checked header metadata to establish every original/auxiliary name lookup.
  `SafeInductiveRestorationMetadata.completeStages` retains the same successful
  preprocessing/runner equations, checked root/constructor/source certificate,
  direct/nested branch trace, positional prefix, derived name and typed source
  coverage, and complete final nested installed-record receipt.
  `installedComplete`, `Environment.addInductive.safeInstalledMetadata`, and
  actual `addDecl.safeInductiveInstalledMetadata` project complete nested
  installation with only initial map validity, no user coverage assumption.
  All eighteen added audits exclude `sorryAx`; prefix/enumeration/coverage and
  metadata projections use only standard logical axioms, while the public
  constructors inherit the existing map/list-push/checker interfaces. Logical
  panic defaults remain explicit, not asserted unreachable. Executable kernel
  code is unchanged. The following module strengthens retention to source
  constructor names/order and raw header types. Semantic source/restored typing
  or reduction, nested transformation/restoration correctness, generated
  binder/index alignment, WHNF transport, auxiliary expression typing, and
  inductive soundness remain separate obligations.
- `Verify.InductiveRestorationConstructors` proves positional source-signature
  retention and source-indexed final constructor metadata. The shared nested
  replacement proofs now establish `ElimNestedInductive.TypePrefix`: every old
  datatype entry remains exactly unchanged while new auxiliaries are appended.
  Existing names-only APIs remain projections of the stronger frame, avoiding
  duplicated nested traversal proofs. `withParams.newTypesFrame` supplies the
  unchanged datatype array to arbitrary parameter-extraction continuations.
  `InductiveSignaturePrefix` records original datatype names, raw header types,
  and exact ordered constructor-name lists at their original positions. The
  actual growing preprocessing loop preserves this signature through every
  constructor rewrite; count and per-position name projections expose the
  original constructor indexing, including empty lists and multiple parents.
  `SafeRunScope.sourceConstructor` joins that prefix with checked metadata to
  provide the actual staged constructor under each original source name, with
  its original parent/position, declared parameter count, level parameters and
  safe flag, plus the staged header's exact source type and constructor names.
  `SourceConstructorLookups` retains that same staged value and provides exact
  final lookups on both branches: unchanged staged records for direct runs,
  literal restored-type updates for nested runs. `constructorStages` couples
  these receipts with the same successful preprocessing/runner equations,
  complete checked root/constructor/source certificate, signature prefix and
  branch trace. Both actual public frontends construct these source-indexed
  receipts from only initial map validity, with no caller retention/coverage
  premise. Twenty-four added audits exclude `sorryAx`; only the public
  constructors inherit existing map/list-push/checker interfaces. No executable
  kernel change, new axiom/admission/cache/fast path, or assertion-unreachability
  assumption. Constructor types may change under nested rewriting; the source
  signature does not assert their equality, semantic typing/reduction, original
  field-count preservation, generated binder/index alignment, WHNF transport,
  auxiliary typing, nested restoration correctness, or inductive soundness.
- `Verify.InductiveNestedArity` proves raw outer-forall arity preservation by
  the actual nested-expression replacement. Both cached and newly generated
  auxiliary replacements are constant-headed applications, with raw arity zero;
  the expression traversal retains every outer forall. A general `withParams.bind`
  equation couples parameter-prefix and structural-context receipts to the same
  successful extraction. Re-abstraction after replacement therefore recovers the
  source arity, and the actual constructor callback preserves its name, raw arity
  and exact old datatype-entry prefix. No source typing or scope assumption is
  needed for these syntactic receipts. Arity means the raw `declareConstructors.arity`
  count, not WHNF arity; annotations, lets and lambdas are not extra outer foralls.
  The application-range proof uses the existing `Expr.mkAppRangeAux.eq_def`
  interface. Re-abstraction additionally inherits the existing array/map,
  `Expr.instantiate1_eq` and `Expr.abstract_eq` interfaces, without `sorryAx`.
- `Verify.InductiveRestorationArity` extends the signature prefix with exact
  ordered source-constructor arities. The actual growing preprocessing loop
  preserves the stronger prefix at every original datatype/constructor position,
  including empty constructor lists and appended auxiliaries. Checked staged
  metadata then establishes `numFields = sourceArity - nparams` and
  `nparams + numFields = sourceArity`. `constructorFieldStages` couples these
  receipts to the same successful preprocessing/runner/root/source witnesses
  and the exact direct/nested final constructor recipes. `finalFields` exposes
  actual final records with the original parent, position, parameters, levels,
  safety and field count. Both public frontends require only initial map validity.
  Twenty-four added audits exclude `sorryAx` and explicitly track the existing
  application-range, binding and public frontend interfaces. No executable kernel
  change, new axiom/admission/cache/fast path or assertion-unreachability premise.
  This extends the earlier signature-only contract with source field counts;
  semantic source/restored typing and reduction, nested correctness, binder/index
  alignment, WHNF transport, auxiliary typing and inductive soundness remain open.
- `Verify.InductiveRestorationRules` transports checked recursor-rule recipes to
  original datatype/constructor positions. Signature retention preserves every
  original minor offset, including the boundary after the final original parent;
  source-indexed minor lookups refer to the same actual local/flattened generated
  minor vectors. Arity retention also preserves ordered constructor-name/field-count
  pairs. `SafeRunScope.sourceRuleSources` retains the same elimination level,
  recursor-info array, structurally valid/reserved source reader and local rule
  distinctness certificate while rewriting both recipe offsets to source offsets.
  Every staged source rule has the source constructor's name, position and raw
  field count, with a checked constructor lookup and its complete source metadata.
  `sourceRecursorRuleStages` couples those recipes, the complete checked scope,
  preprocessing prefix and exact final direct/nested recursor records. `finalRecursor`
  exposes final rule counts/field vectors, including empty parents; `finalRule`
  additionally ties each final indexed field count to its checked constructor and
  original raw arity. Both public frontends need only initial map validity.
  Nested restoration retains rule positions and field counts and uses the literal
  mapped recursor name/constructor-label recipe. Rename-map identity is not assumed:
  original constructor labels are retained when the recursor's mapped name is
  unchanged, and otherwise the exact `restoreCtorName` recipe is exposed. Eighteen
  added audits exclude `sorryAx`, explicitly tracking existing arity, binding and
  public frontend interfaces. No executable kernel change or new axiom/admission.
  Source/restored semantic typing, RHS reduction, nested correctness,
  binder/index alignment, WHNF transport and inductive soundness
  remain separate; generated auxiliary contributions to total minors are retained.
- `Verify.InductiveRecursorNames` derives datatype-name uniqueness from the actual
  successful fresh header-registration fold, with exact header-array alignment,
  and from the full runner for either safety using only initial map validity.
  Prefix retention and rewritten-name uniqueness exclude original datatype names
  from the auxiliary suffix. The literal auxiliary-map loop preserves lookups
  outside its enumerated keys, proving absence and fallback identity, including
  logical empty/missing/non-inductive-header and failed-length defaults.
- `Verify.InductiveRestorationRuleNames` discharges original recursor rename-map
  nonoverlap on the same successful preprocessing/runner/root/source witnesses.
  It derives original-key absence/identity rather than accepting a caller identity
  premise. Final recursors are installed under their original names and retain
  original ordered constructor labels, counts and field vectors, including empty
  parents; indexed rules retain their checked staged constructor and original raw
  arity equation. Exact direct/nested record recipes, elimination level/info array,
  minor indexing and local-distinctness receipts remain coupled. Both public
  frontends require only initial map validity. Axiom audits track existing map,
  binding and frontend interfaces and exclude `sorryAx`; no executable kernel
  change or new axiom/admission. These are structural name/rule receipts, not
  source/restored semantic typing, RHS reduction, nested correctness, binder/index
  alignment, WHNF transport, auxiliary typing or inductive soundness.
- `Verify.InductiveRestorationRecursors` couples original source recursors to
  their exact `declareRecursors.metadataVal` records and actual indexed rule
  recipes, retaining the same elimination level, info array, local source context
  and K flag from the successful runner. Original-name final header projections
  retain level parameters, parameter/index counts, motive/minor totals, K flag
  and safety. Motive/minor totals include generated auxiliary datatypes/minors,
  rather than incorrectly counting only the original prefix. Exact generated
  source types and final `all` lists are projected through literal direct/nested
  restoration. Indexed final rules keep source constructor labels/field counts
  and expose the exact `restoreNested` expression for each source RHS, with the
  actual auxiliary-rec-name map. Checked source constructor metadata and raw
  arity equations remain attached to the same indexed rules. Successful
  preprocessing/full-run/root/constructor/source witnesses, minor indexing,
  local RHS distinctness and original rename-map identity remain coupled; both
  public frontends require only initial map validity. Sixteen axiom audits exclude
  `sorryAx` and track existing binding/map/frontend interfaces. No executable
  kernel change or new axiom/admission. These are structural record and literal
  expression equations, not semantic source/restored typing, reduction,
  correctness of nested elimination, K-target semantics, binder/index alignment,
  WHNF transport, auxiliary typing or inductive soundness.
- `Verify.InductiveParams` verifies the earlier syntactic parameter guard.
  `ElimNestedInductive.ParamPrefix` records the extracted array's exact declared
  size, free-variable shape, and source raw arity as extracted parameters plus
  residual raw arity. `withParams.prefix` supplies this contract to arbitrary
  continuations in any environment/preprocessing state, and `getPrefix` returns
  it with the extraction result. `paramArity` exposes the necessary raw binder
  lower bound for any successful extraction, without a typing or WHNF premise.
  `withParams.reject_of_arity_lt` proves the exact parameter-count diagnostic when
  too few syntactic binders exist, including hidden parameters behind reductions.
  The rejection propagates through `ElimNestedInductive.run` and
  `Environment.addInductive`. `addDecl.inductiveParamArity` proves every successful
  nonempty inductive call has enough raw parameter binders in its first source
  datatype; `reject_inductive_of_paramArity` rules out successful full frontend
  registration otherwise. These contracts quantify over both safety/checking
  flags, all fuel configurations, and arbitrary environments/states.
  They do not assert header/constructor semantic typing, complete preprocessing
  soundness, recursor correctness, or general inductive declaration soundness.
  The proofs use only standard logical axioms and the existing
  `Lean.Expr.instantiate1_eq` interface, without new axioms or `sorryAx`.
  Executable behavior is unchanged: the full frontend already enforces the guard
  before the isolated numeric checking/registration prefix.
  `withParams.assert_size` proves the extracted-size guard can be removed without
  changing the action, including errors, for arbitrary continuations and mismatch
  branches. `run.loop.paramCount` uses this equality to discharge the actual
  constructor-prefix assertion before following the preprocessing loop. Its fuel
  induction allows arbitrary state mutations and auxiliary datatype growth;
  no fixed `newTypes` size or header/constructor typing premise is required.
  `run.paramCount` proves every successful nested preprocessing result stores the
  original declared parameter count, for arbitrary fuel, input lists, environments,
  and states. `paramCount_run'` supplies the state-discarding projection used by
  `Environment.addInductive`. Empty inputs and exhausted fuel cannot return a
  result and satisfy the successful-result contract vacuously. This does not
  verify nested rewriting, auxiliary constructor typing, other internal assertions,
  or the subsequent checker/recursor stages. All four audits exclude `sorryAx`;
  guard/loop proofs use only standard logical axioms, while the public run proofs
  also inherit the existing extraction instantiation interface.
  `ParamContext` adds a structural context contract: the declared parameter count
  equals both the context's index count and the parameter array size, and mapping
  the context's local declaration list to free variables yields the extracted
  parameters in reverse order. Every declaration has default kind and no value,
  including nondependent let values. Its `length` and `declaration` theorems expose
  an exact declaration count and a corresponding declaration for every parameter.
  `withParams.context` supplies this contract to arbitrary continuations;
  `getContext` returns it and `getContextPrefix` combines it with the existing raw
  arity/free-variable prefix contract. `run.loop.frame` proves the preprocessing
  loop returns the exact lexical parameter context despite constructor rewriting
  and auxiliary-array growth. `Result.ParamContext`, `run.paramContext`, and its
  state-discarding projection carry the context contract to successful results;
  `run.contextCount` exposes both index and declaration counts.
  These structural proofs use the existing `PersistentArray.toList'_push` interface
  for declaration-list observations, not new axioms. The combined extraction
  theorem additionally uses the existing instantiation bridge. The older prefix
  and numeric count APIs retain their original audited axiom sets. Actual map
  lookup equality, fresh-ID/distinctness, or local-context map validity do not
  follow from the structural-only contract; the next module verifies those
  additional obligations. Semantic domain typing and nested transformation
  correctness remain separate; exact source-domain metadata is runtime evidence.
- `Verify.InductiveParamValidity` verifies concrete parameter-context validity.
  `ContextReserved` records that every existing local free-variable identifier is
  reserved by the current name generator. Its `fresh` theorem proves the next
  generated identifier is absent from a well-formed concrete context, and
  `push_current` preserves reservations when that identifier is declared.
  `ParamValidity` combines the structural parameter contract with `LocalContext.WF`.
  It proves distinct extracted parameters, exact `find?` equality for every local
  declaration, and a default-kind/non-let lookup record for every extracted
  parameter. `withParams.validContext` supplies validity and reservations to
  arbitrary continuations; `getValidContext` returns them with the extraction
  result and its generator. No initial environment or state validity premise is
  required: extraction starts with an empty local context.
  `Result.ParamValidity`, `run.paramValidity`, and the state-discarding projection
  preserve this validity through the exact preprocessing context frame, including
  auxiliary datatype growth. `contextWF` and `contextLookup` expose the concrete
  map validity and exact final declaration lookups. These are concrete-data
  partial-correctness contracts, not semantic `TrLCtx` or binder-domain typing.
  Reservations are proved at the extraction boundary, not against the final
  preprocessing generator after opaque nested-rewriting actions. Freshness
  relative to arbitrary free variables in the source expression, nested rewriting,
  positivity, recursors, and unrestricted inductive soundness remain separate.
  All fourteen audits exclude `sorryAx` and instantiation/typing interfaces; the
  proofs reuse the existing persistent-array push and persistent-map lookup/insert
  bridges without adding axioms or changing older theorem audit sets.
- `ParamValidity.indices` identifies the chronological declaration indices with
  `List.range numParams`; `declarationAt` identifies the declaration at each
  bounded parameter-array position. `parameterLookupAt` proves that concrete
  `findFVar?` returns that declaration with exactly the array index, parameter
  expression, default kind, and no let value. `getFVar!_index` verifies the actual
  getter's index. `IndexedParamLookup` packages this indexed lookup contract with
  the exact array size, and `withParams.getIndexedLookup` supplies it for successful
  extraction. `Result.IndexedParamLookup`, `run.indexedLookup`, and its
  state-discarding projection preserve it through arbitrary nested preprocessing.
  These proofs do not establish parameter re-abstraction or semantic binder typing.
  Source-expression freshness, nested rewriting, positivity, recursors, and full
  inductive soundness remain unproved. All eight new audits exclude `sorryAx` and
  use only existing array/map bridges, without expanding older theorem assumptions.
- `Verify.InductiveParamBinding` verifies concrete parameter re-abstraction.
  `ParamValidity.mkForall_eq` identifies the executable `LocalContext.mkForall`
  with `paramForall`: a chronological declaration fold retaining names and binder
  flags, abstracting each domain over its indexed parameter prefix and the body
  over the full parameter array. This exact equation uses only existing array/map
  bridges, not the expression-abstraction interfaces, and permits loose variables
  in bodies/domains. `mkForall_arity` proves the exact raw binder count is
  `numParams + arity body`; it additionally inherits `Expr.abstract_eq`.
  `ParamBinding`, extraction, and both preprocessing projections expose these
  contracts. `withParams.getReabstractArity` recovers the original source's raw
  arity, additionally using the existing instantiation bridge.
  `withParams.mkForall_arity` verifies the parameter-prefix lower bound after any
  successful transformed-body action, including the actual constructor callback.
  These are syntactic contracts, not binder typing, nested rewriting correctness,
  original-expression reconstruction, or unrestricted inductive soundness.
  The loose-variable regression exposed an abstraction-interface scope mismatch
  documented in `divergences.md`; the exact fold avoids that interface, while
  its arity projection now uses leading-binder preservation of the corrected raw
  abstraction specification through the existing audited implementation bridge.
- `Verify.InductiveParamScope` verifies the no-loose-bound-variable extraction
  invariant. Given a source with structural `looseBVarRange' = 0`, every extracted
  parameter domain and the remaining expression also have range zero.
  `ContextNoLooseBVars` records the domain property; ordinary local declaration
  insertion and one-binder instantiation preserve it. `withParams.noLooseBVars`
  supplies both facts to arbitrary continuations, and `getScopedContext` combines
  them with concrete parameter validity. `ParamValidity.parameterScopeAt` proves
  the actual indexed getter's domain has range zero. Flag projections additionally
  expose `hasLooseBVars = false` through the existing range-metadata bridge.
  `run.contextScope`, its state-discarding projection, and final context flags
  preserve domain scope through the exact preprocessing frame; only the first
  source header needs the range-zero premise. They do not claim scope preservation
  for opaque rewritten bodies or auxiliary datatype types.
  All thirteen audits exclude `sorryAx` and expression-abstraction interfaces.
  Structural extraction uses existing array-push/instantiation bridges; concrete
  getter/validity projections also use existing map bridges, and flag projections
  use `Expr.looseBVarRange_eq`. Range zero permits metavariables and arbitrary free
  variables: it is not semantic typing, `Expr.Closed`, or source-ID freshness.
  The former unconditional sequential-abstraction specification is now corrected
  using the raw model and scope/distinctness proof described below.
- The direct binding reconstruction interfaces now expose their missing scope
  premises. `LocalContext.BindingScope` records range-zero declaration types and
  let values, including nondependent lets; `LocalContext.mkBinding_eq` requires
  that predicate, a range-zero body, and distinct identifiers. `MLCtx.WF.bindingScope`
  derives context scope from translated domains/values and exact declaration
  lookup. The partial/full `MLCtx.WF.mkForall` and full `mkLambda` reconstruction
  equalities require body scope and derive distinctness from context validity.
  Both actual `InferType` callers discharge scope using their cheap-beta-reduced
  type translations. Runtime counterexamples show duplicate identifiers also
  invalidate the former sequential abstraction bridge on a range-zero body.
  The binding proof now uses its scope/distinctness premises to pass from the
  corrected raw model to the sequential fold, including each declaration's
  indexed domain/value prefix. It still inherits `Expr.abstract_eq` as a trusted
  implementation bridge. The scalar-arity consumer instead uses raw constructor
  preservation and retains its arbitrary-body public contract.
  Typed scope/reconstruction audits inherit the existing translation stack's
  `sorryAx`; no new admission, axiom, dependency, or executable checker change is
  introduced. The raw scoped binding equality and empty-context scope audits
  exclude `sorryAx`.
- `Verify.InductiveParamReconstruction` proves source-expression round trips for
  successful parameter extraction. `SourceReserved` requires every source free
  variable in the generator's namespace to precede its starting index; free
  variables outside that namespace are unrestricted. It excludes capture by
  every subsequently generated parameter ID, not merely the first one.
  `SourceReserved.noFVars` discharges this sufficient freshness condition from
  `hasFVar = false`, without excluding expression or level metavariables.
  `withParams.reconstruct` supplies arbitrary continuations with the exact
  sequential `reconstructParams` fold back to the source; this structural
  contract needs freshness but no bound-variable scope premise.
  `ParamValidity.bindingScope` connects extracted domain scope to the generic
  binding interface, ruling out local let declarations using parameter validity.
  `mkForall_reconstruct` identifies native re-abstraction with the sequential
  fold for a scoped context/body. `withParams.getReconstruction` combines these
  proofs with scoped extraction to recover the complete original expression,
  retaining names, dependent domains, binder flags, and remaining binders.
  `getReconstruction_noFVars` exposes the scoped free-variable-free corollary.
  `sourceReconstruction` supplies the native source equality to arbitrary
  continuations using a uniform extraction/bind factorization; `mkForall_source`
  verifies the direct extraction-and-re-abstraction callback.
  All sixteen new audits exclude `sorryAx`; native reconstruction still inherits
  the existing corrected abstraction and map/array/instantiation bridges, and
  the no-free-variable corollary additionally uses `Expr.hasFVar_eq`.
  The source scope/freshness conditions remain explicit, not newly proved
  consequences of the inductive frontend. These syntactic round trips do not
  establish semantic typing, rewritten-body scope, nested rewriting correctness,
  positivity, recursors, or full inductive soundness.
- `Verify.InductiveSourceChecks` verifies the uniform original-source preflight
  now executed by `Environment.addInductive` before parameter extraction/nested
  rewriting. `InductiveSourcesNoMVarNoFVar` records the structural no-expression-
  metavariable, no-level-metavariable, and no-free-variable contract for every
  header and constructor type. `checkInductiveSources.WF` proves complete list
  coverage; `.eq_pure` proves the guard is a no-op on valid sources. Header and
  constructor projections discharge `SourceReserved` for arbitrary generators.
  `addInductive.sources`, `.constructorReserved`, and `addDecl.inductiveSources`
  establish the original-source contract from actual successful frontend calls,
  including both safety modes and the existing inductive `check`-flag behavior.
  All eight new audits exclude `sorryAx`, abstraction/instantiation interfaces,
  and map/array interfaces; three need only logical axioms and the others inherit
  the existing variable-metadata bridges from `checkNoMVarNoFVar`.
  This resolves an observed source-capture validation bug, reproduced separately
  against native Lean 4.29.0: the native kernel accepts an undeclared constructor
  free variable `_nested_fresh.1` and stores it as a bound parameter. The old
  unguarded lean4lean pipeline captures `_nested_fresh.2`. The new frontend rejects
  both, deliberately diverging on those invalid sources; see `bugs-found.md` and
  `divergences.md`. It does not establish logical unsoundness of the native kernel.
  Frontend parameter-shortage rejection now first propagates source-preflight
  errors, without weakening its unconditional successful-result arity bound.
  Bound-variable source scope, transformed-body scope, semantic typing, positivity,
  recursors, and full inductive soundness remain separate obligations.
- `Verify.InductiveNestedScope` proves that successful nested preprocessing
  retains its actual chronological parameter array with its local-context
  validity. The executable final auxiliary check now opens that array before
  checking each expression, resolving the parameterized nested rejection
  documented in `divergences.md`. The scope/metadata contracts require an explicit
  auxiliary range bound, not semantic typing or full rewriting correctness.
- `Verify.InductiveNestedRebinding` derives that range bound for the concrete
  parameter-rebinding/final-abstraction chain. The raw structural theorem
  `Expr.abstractFVars_looseBVarRange` bounds abstraction by the maximum of the
  original range and binder depth plus identifier count, including duplicate
  identifiers and initially loose expressions; it uses no implementation bridge.
  `ParamContext.params_eq_fvars` connects actual chronological arrays to the
  native abstraction specification. `.abstract_range` and `.abstract_scopedRange`
  establish the native bounds, and `replaceParams.eq_ok` proves the size-matched
  helper preserves its preprocessing state. `.noLooseBVars` proves rebinding a
  scoped source between equal-sized parameter contexts remains scoped;
  `.auxRange` derives the final abstraction bound, and `.finalAux_scope` carries
  it through the actual `Result.openAux` metadata check. No output-range premise
  is assumed for this chain. All eight audits exclude `sorryAx`; three use only
  logical axioms, and the rest use the existing abstraction/instantiation bridge
  and, for the flag corollary, the range-metadata bridge.
  The nested-app guard's parameter-prefix source scope is now supplied by
  `Verify.InductiveNestedGuard`; preservation across the complete rewrite traversal/map
  is supplied by `Verify.InductiveNestedRewrite` at the state-only level. Auxiliary
  semantic typing, positivity, recursors, and full inductive soundness remain open.
  Tests deliberately bypass the nested-app guard to demonstrate why source scope
  and a free-variable target context are necessary; these helper boundaries are
  not newly accepted invalid frontend declarations. The checker is unchanged.
- `Verify.InductiveNestedGuard` verifies the actual `isNestedInductiveApp?`
  classifier without changing its executable code. `.scope` proves every
  successful result preserves the preprocessing state, and every returned
  inductive value has a constant application head, enough arguments, and no
  loose variables in any parameter argument. `.frame` projects state identity;
  `NestedAppScope.argRange` and `.prefixRange` establish structural range zero
  for the exact `mkAppRange` prefix consumed by `replaceParams`. `.prefixScope`
  and `.prefixScopeFlag` carry those contracts through the actual classifier.
  `.checkedRebinding` composes classification, rebinding, final abstraction, and
  `Result.openAux`, requiring parameter-context validity but no original-prefix
  or rewritten-output scope premise. Seven audits exclude `sorryAx`; the two
  classifier/frame audits use only logical axioms, while range/opening proofs
  inherit the existing metadata, application-building, abstraction, and
  instantiation interfaces. No new axiom, admission, or executable guard is added.
  The contract deliberately concerns parameter arguments, not index arguments:
  a loose index can coexist with a scoped parameter prefix. Non-nested inputs
  may also contain loose variables and still classify as `none`; unchanged
  parameter-count/error priority is regression-tested. Fixtures use native-checked
  container declarations but test local classifier/rebinding expressions, not
  full declaration typing or frontend acceptance. Semantic typing, positivity,
  recursors, and full inductive soundness remain open.
- `Verify.InductiveNestedRewrite` introduces the `State.NestedAuxScoped` invariant
  for the auxiliary map. It proves `replaceIfNested.scope`: a scoped result of
  `replaceParams` can be pushed into `nestedAux`, and the invariant survives the
  complete mutual-family `forIn` traversal, constructor `mapM`, and final
  `newTypes` update. A structural `Expr.replaceM` induction composes that
  callback contract into `replaceAllNested.scope`, covering every expression
  constructor and preserving state scope across the full rewrite traversal. The
  `withParams.contextScope`, `run.loop.nestedAuxScoped`, and
  `run.nestedAuxScoped` contracts now carry the invariant through constructor
  parameter extraction, every generated auxiliary constructor rewrite, the
  `newTypes` update, and the final preprocessing result. Its final result map
  contract proves every folded auxiliary expression has bound-variable range at
  most the retained parameter count, using the existing scoped abstraction
  contract and the standard `NameMap` insertion equation. The classifier's
  constant-prefix range is transferred to arbitrary mutual family names.
  `mkAppN_range` and `mkAppRange_tail_range` provide the structural range
  bounds needed for generated applications. `replaceIfNested.range` proves
  each generated nested replacement stays within the original expression's
  loose-bound-variable range, and `replaceAllNested.range` lifts that contract
  through the complete structural traversal. `withParams.contextRange` now
  combines the state invariant with a bounded remainder contract: parameter
  extraction preserves a `≤ numParams` loose range and carries explicit
  parameter validity, fresh-name reservation, and bounded local-domain facts.
  `ParamContext.abstractRange_range` and `ParamValidity.mkForall_range` bound
  native parameter re-abstraction at the same limit. `replaceAllNested.rangeWithNewTypes`
  explicitly isolates the generated auxiliary `newTypes` closure and retained-index
  premise instead of assuming arbitrary environment declaration ranges or
  `instantiateForallParams` behavior. The new
  `Expr.instantiateRevRange_looseBVarRange` and `instantiateForallParams.range`
  contracts prove bounded reverse substitution after leading-binder stripping;
  `Lean.Expr.instantiateLevelParams_looseBVarRange` proves that universe-level
  substitution preserves expression bound-variable range. The explicit
  `Lean4Lean.Environment.InductiveDeclRange` predicate now also requires every
  listed constructor to resolve as a constructor declaration; its closure
  theorem and two range-transport lemmas establish the same bound after level
  substitution.
  `replaceIfNested.rangeWithNewTypes` uses that closure together with the bounded
  forall-parameter contract to discharge each generated auxiliary constructor and
  `newTypes` range. `replaceAllNested.rangeWithNewTypesStructural` lifts that
  callback contract through the complete expression traversal and proves both
  generated-state range and retained-index preservation. The older
  `replaceAllNested.rangeWithNewTypes` theorem remains an explicit-premise
  compatibility contract, while `run.loop.newTypesRange` now derives its
  per-constructor contract structurally and takes only the explicit environment
  declaration-closure premise. `State.NewTypesRange` and
  `run.loop.newTypesRange` then propagate preexisting and generated ranges through
  constructor `mapM`, bounded re-abstraction, and the executable `set!` update into
  both the final state and result types. The top-level `run.newTypesRange`
  contract now carries the initial declaration range, retained-index, and
  environment closure premises through parameter extraction into the final
  state and result types, with a `StateT.run'` bridge for the frontend caller.
  Thirty-seven focused audits exclude
  `sorryAx` and use only the existing logical, metadata, application-building,
  abstraction, instantiation, and array interfaces. These are explicit range
  contracts; they do not prove environment declaration closure, auxiliary
  environment declaration translation, auxiliary semantic typing, positivity,
  recursors, or full inductive soundness.
- `Expr.abstractFVars` models native abstraction over free-variable-only arrays,
  preserving existing bound variables and unmatched metavariables and choosing
  the last duplicate identifier at the appropriate binder depth. The existing
  `Expr.abstract_eq` axiom now targets this raw model rather than the incorrect
  unrestricted sequential `abstractList` equation; no axiom is added.
  `abstractFVars_eq_abstractList` proves their agreement under structural scope
  and identifier distinctness, and `abstract_eq_of_scope` transfers it to native
  abstraction. `arity_abstractFVars` proves raw leading-binder-count preservation
  for arbitrary bodies, identifiers, starting counts, and depths, using no
  implementation interface. `arity_abstract` transfers that property through
  the corrected bridge. This fixes the demonstrated verification specification,
  not the executable checker; the native C++ implementation remains trusted.
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
  shape. These contracts are not yet extracted from the modulo validator;
  neither modulo's primitive-extension proof nor its native reduction is
  connected.
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
  These are prerequisites for the unfinished modulo bridge, not a proof of it.
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
  Extraction from modulo's fresh-local checks, assembly of its loop/entry
  contracts, and the declaration-extension proof remain unfinished; native
  modulo is still disabled.
- `natModEntryBody.spec` supplies the successor entry contracts from the open
  two-local equation, including zero and oversized divisors.
  `natModLoopBody.spec` supplies the recursive contract from the open five-local
  equation, preserving the dependent proof arguments. Their source substitution
  lemmas identify the templates with the executable fresh-local bodies and their
  literal instances. The recursive substitution proof is shared with division
  through a private helper; division's published statement is unchanged.
  `NatModSpec.ofEntry` combines these contracts with a separately supplied zero
  equation. Extraction of all three equations from the complete modulo validator
  and the primitive-extension/native-reduction connection remain unfinished.
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
- Native `Nat.gcd`, `Nat.mod`, `Nat.land`, `Nat.lor`, and `Nat.xor` reductions
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
lake env lean tests/InductiveArity.lean
lake env lean tests/InductiveHiddenParameter.lean
lake env lean tests/InductiveParams.lean
lake env lean tests/InductiveParamContext.lean
lake env lean tests/InductiveParamValidity.lean
lake env lean tests/InductiveParamIndices.lean
lake env lean tests/InductiveParamBinding.lean
lake env lean tests/InductiveParamScope.lean
lake env lean tests/InductiveNestedScope.lean
lake env lean tests/InductiveNestedRebinding.lean
lake env lean tests/InductiveNestedGuard.lean
lake env lean tests/NestedInductiveParams.lean
lake env lean tests/ConstructorHeaders.lean
lake env lean tests/ConstructorArity.lean
lake env lean tests/ConstructorParams.lean
lake env lean tests/ConstructorBatchArity.lean
lake env lean tests/ConstructorMetadata.lean
lake env lean tests/InductiveMetadata.lean
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
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorArity.Basic
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorParams
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.ConstructorMetadata
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveMetadata
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveParams
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveParamValidity
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveParamBinding
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveParamScope
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveNestedScope
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveNestedRebinding
lake env .lake/build/bin/lean4lean Lean4Lean.Verify.InductiveNestedGuard
```

The tests cover acceptance/rejection from an empty environment, rejection of
incorrect arithmetic implementations, large literal arithmetic with low fuel,
subtraction truncation at zero, equal and unequal large literals, rejection of
incorrect equality and ordering implementations, left shifts beyond machine-word
sizes, right shifts at and beyond the input's bit length (including a shift count
beyond machine-word sizes), both sides of the native exponent-limit boundary, and
agreement with upstream on 3,280 small normalizations and 10,000 generated level
cases. The executable successfully replayed 862 declarations across the primitive
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
orderedness, with nineteen proof regressions and fifteen axiom audits. It
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
`propext`. The semantic `VEnv.WF` closure inherits `sorryAx` through the
existing `VDecl.WF`/`VInductDecl.WF` foundation; it adds no new admission.
`PrimitiveInductiveDecl.toVDecl` additionally inherits
`Classical.choice` and `sorryAx` through the existing structural-translation
API (`TrExprS` includes the admitted `TrProj` specification).
`checkPrimitiveInductive.toVDecl` also inherits the three equality interface
assumptions of the validator classification. No new axiom or admitted proof
is added, and these bridges do not claim unconditional inductive soundness.
Focused executable replay checks 24 declarations in `Theory.InductiveHeaders`
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

`tests/InductiveStats.lean` contains twenty-two proof regressions and fourteen axiom audits
for the paired header-array lengths, fixed callback-context fields, and parameter
counts/distinctness. Count regressions cover arbitrary continuations, nonempty
successful checks, and proof-only empty batches with arbitrary declared counts.
Twenty-one executable acceptance cases cover
empty, singleton, and mutual batches; safe and unsafe contexts; parameters;
dependent indices; distinct index counts; three dependent parameters with mixed
binder annotations; and universe parameters. Six rejection
cases cover missing or mismatched parameters, mismatched result universes,
undeclared universes, invalid types, and exhausted inductive fuel. The size/frame
theorems use only `propext`, `Quot.sound`, and `Classical.choice`; their audits
exclude `sorryAx` and all implementation-interface axioms.
The proof tracks parameter and universe counts internally to justify the terminal
assertions for nonempty batches. Its empty-batch case also accounts for the
kernel-level default value of a failed parameter-count assertion; the size/count
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
Focused executable replay checks 114 declarations in `Verify.InductiveStats`,
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
the separate numeric registration theorem below supplies the arity assertion's
precondition from checked parameter arrays and successful full batch checking.
Focused executable replay checks fifteen declarations in `Theory.ConstructorHeaders`
and twenty-eight in `Verify.ConstructorHeaders`, assuming their imported dependencies
are correct.

`tests/PrimitiveInductiveStaging.lean` exercises the primitive checked-prefix
refinement without supplying header/constructor translations or typing models.
Proof controls cover empty and typed-axiom-seeded starting environments,
arbitrary `Nat.succ` binder names/annotations and arbitrary admitting safety
filters. The derived final model preserves old semantic constants and
definitional equations. Twenty-six executable acceptance fixtures cover `Bool`
and twelve `Nat.succ` binder variations in each starting environment, with
156 duplicate, primitive-authorization, zero-fuel and individual header/constructor
name-collision rejections. Recognition still succeeds for occupied primitive
names; registration rejects them, confirming that the theorem is partial
correctness rather than an acceptance guarantee. An exact ten-axiom manifest
pins the new theorem to the existing logical, translation, persistent-map and
inherited `sorryAx` foundations. Run
`lake env lean tests/PrimitiveInductiveStaging.lean`.

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
26 declarations in `Verify.ConstructorArity` and 22 in
`Verify.ConstructorArity.Basic`, assuming imports are correct.

`tests/InductiveArity.lean` adds ten proof regressions and seven axiom audits for
WHNF/instantiation binder bounds, arbitrary continuations, successful indexed
statistics, proof-only empty batches, exact header metadata, and the complete
registered prefix. All audits exclude `sorryAx`; raw-arity substitution uses only
the existing `Lean.Expr.instantiate1_eq` bridge beyond standard logical axioms,
and registration additionally inherits the existing map/guarded-arity interfaces.
Twenty-six safe/unsafe normalized-prefix outcomes cover explicit telescopes,
delta aliases, dependent hidden tails, annotations, beta reduction, let reduction,
and mutual types. Sixteen fixtures agree with the native kernel's accepted
parameter/index counts; ten prefixes hiding declared parameters succeed while
the native kernel rejects the identical declarations with its parameter-count
diagnostic. Native checking is enabled. The minimal safe-mode reproducer is
`tests/InductiveHiddenParameter.lean`. Each fixture now additionally runs the full
lean4lean `addDecl` frontend: it agrees with native acceptance/rejection, and the
sixteen accepted cases check final header counts and generated recursor presence.
This is runtime evidence of the complete path, not a recursor soundness theorem.
Existing statistics and registration fixtures also check the new raw-arity
lower bounds. No executable checker behavior changes. Focused replay additionally
checks 114 declarations in `Verify.InductiveStats` and 16 in
`Verify.InductiveMetadata`, assuming imports are correct.

`tests/InductiveParams.lean` contains ten proof regressions and eight axiom audits
for arbitrary extraction continuations, returned counts/free-variable arrays,
raw/residual arity, exact guard rejection, preprocessing, environment registration,
and the full inductive frontend. The audits exclude `sorryAx` and all interface
axioms except the existing executable instantiation bridge.
Thirty-two extraction outcomes cover zero/one/two dependent parameters, too few
syntactic binders, parameters hidden after an explicit binder, constant/annotation/
beta/let heads, and default or seeded preprocessing states. Accepted cases check
local-count growth, exact fresh-variable names/order, and unrelated state fields;
these state checks are regressions, not extra premises of the numeric proof.
Sixteen full frontend rejections cover safe/unsafe declarations, both checking
flags, and ordinary or zero inductive fuel. Hidden parameters fail before later
checking/recursor stages. Normalized indices remain accepted in the separate full
frontend fixtures. No executable guards, caches, or special paths are added.

`tests/NestedInductiveParams.lean` contains eight proof regressions and four axiom
audits for the arbitrary mismatch branch, the literal `assert!` action, the exact
constructor preprocessing callback, the fuel loop, and both result projections.
Fifty-six preprocessing outcomes cover zero/one/two parameters, dependent
constructor fields, default and seeded fresh-name/auxiliary states, empty input,
zero/insufficient fuel, and constructors with missing or hidden parameters.
Twenty-four accept and thirty-two reject with exact diagnostics. Six accepted
nested `List` fixtures grow the datatype array from one to two entries and check
the final declared count, auxiliary growth, and every header/constructor prefix.
Additional-state-header and empty-state-array fixtures exercise the low-level
theorem without assuming the initial array matches the input list. These runtime
observations do not prove nested transformation or context-hygiene semantics.
Every successful fixture also compares the result context's executable declaration
array against the original extraction, including free-variable order, indices,
names, instantiated domains, binder information, kind, and let status.
Each resulting declaration also checks exact executable lookup metadata against
the declaration array and its parameter-array position, including the actual
`getFVar!` index in all auxiliary-growing cases.
Every accepted fixture additionally checks parameter re-abstraction of its original
source header through the final preprocessing context. This is runtime round-trip
evidence for these closed fixtures, not a general source-reconstruction theorem.
All accepted preprocessing fixtures also check zero structural bound-variable
range and false executable loose-variable flags for every final parameter domain.
Executable preprocessing is unchanged; no new guard, cache, or special path is
introduced.

`tests/InductiveParamContext.lean` contains twelve proof regressions and eleven
axiom audits for empty/extended contexts, declaration witnesses, extraction
continuations, exact preprocessing context preservation, and result projections.
The audit allowlists distinguish the existing persistent-array bridge from the
combined theorem's additional instantiation bridge; all exclude `sorryAx`.
Thirty extraction outcomes cover default and seeded preprocessing states,
zero through four dependent parameters, repeated/anonymous/namespaced binder names,
all four binder-info forms, annotated heads/tails, and exact guard rejection.
Ten accepted wide contexts exercise persistent-array boundaries at 31, 32, 33,
64, and 65 declarations. Twenty-four outcomes accept and six reject. Accepted
cases check every executable declaration's index, free variable, name, instantiated
domain, binder information, default kind, absence of let values, and executable
lookup metadata. These observations do not replace structural proofs with
semantic typing or map-lookup correctness claims.

Focused executable replay checks 83 declarations in `Verify.InductiveParams`,
including the structural context proofs, assuming its imported dependencies are
correct.

`tests/InductiveParamValidity.lean` contains seventeen proof regressions and fourteen
axiom audits for reservations, fresh insertion, concrete context validity,
parameter distinctness, exact extraction/result lookups, arbitrary continuations,
and state-discarding projections. A duplicate-parameter proof regression shows
why the older structural-only contract cannot supply distinctness by itself.
Sixty-four extraction outcomes (32 accept, 32 exact-diagnostic rejections) cover
zero/one/two/three and 31/32/33/65 dependent parameters, repeated binder names,
default/seeded/anonymous generator prefixes, and a large initial generator index.
Accepted cases check exact fresh identifiers, distinctness, generator progress,
next-name absence, and concrete lookup metadata. These runtime progress checks
are not additional monotonicity claims for nested rewriting. No executable checker
path, guard, cache, or dependency is added.

`tests/InductiveParamIndices.lean` contains twelve proof regressions and eight axiom
audits for chronological indices, bounded declaration witnesses, concrete indexed
lookup, the actual getter, extraction, and both preprocessing projections. Empty,
first/last-index, and duplicate-parameter boundaries are included. Sixteen accepted
extractions cover two initial states and 0/1/2/3/31/32/33/65 dependent parameters,
repeated/anonymous binder names, and all four binder-info forms. Every extraction
checks chronological declaration indices and actual lookup/getter indices; twelve
reversed-array checks show that correspondence depends on parameter order.
The declaration-list audits use only the existing persistent-array push bridge;
the lookup audits additionally use existing persistent-map lookup/insert bridges.
No executable checker change, dependency, axiom, or admitted proof is introduced.

Focused executable replay checks 40 declarations in `Verify.InductiveParamValidity`,
including the indexed lookup proofs, and 83 in `Verify.InductiveParams`, assuming
imported dependencies are correct.

`tests/InductiveParamBinding.lean` contains sixteen proof regressions and eleven
axiom audits for the chronological binding fold, exact arity, arbitrary successful
body transformations, extraction, and both preprocessing projections. Empty/single
parameters, annotation-hidden binders, and the exact constructor callback including
its count assertion are covered. The exact fold's audit excludes every expression
interface; arity adds only the corrected raw-model `Expr.abstract_eq`, and
source-arity restoration also adds `Expr.instantiate1_eq`. All audits exclude `sorryAx`.
Forty-eight closed-source round trips cover two initial states, 0/1/2/3/31/32/33/65
dependent parameters, and zero/one/two residual binders. They also check 576 body
replacements spanning all expression constructors, including loose variables,
metavariables, external free variables, dependent applications, lets, lambdas,
annotations, and projections. Two unscoped-source fixtures check the exact
executable fold with loose domains. Two source-capture and two unused-let fixtures
demonstrate why structural validity alone does not imply source reconstruction or
permit let-bound parameters. A minimal loose-variable abstraction observation
reproduces the existing trusted-interface scope mismatch in `divergences.md`.
No checker change, dependency, new axiom, or admitted proof is introduced.

Focused executable replay checks 41 declarations in `Verify.InductiveParamBinding`,
assuming imported dependencies and the explicitly audited interfaces are correct.

`tests/InductiveParamScope.lean` contains eighteen proof regressions and thirteen
axiom audits for empty/extended domain scope, one-binder instantiation, arbitrary
continuations, concrete indexed getters, extraction validity, metadata flags,
the preprocessing frame, and result projections. Zero-parameter, loose-variable,
metavariable, and source-capture boundaries are included. The audit allowlists keep
the structural, concrete lookup, and executable metadata assumptions separate;
none uses an expression-abstraction interface.
One hundred forty-four accepted well-scoped extractions cover two initial states,
0/1/2/3/31/32/33/65 dependent parameters, repeated/anonymous names, all binder-info
forms, and nine residual expression forms including binders, lets, annotations,
projections, metavariables, and external free variables. Every case checks stored
domains, concrete lookup/getter domains, and the remainder against both structural
range and executable flags. Twelve accepted ill-scoped helper-boundary fixtures
expose loose domains or remainders when the source premise is omitted; this does
not add an executable rejection guard. Two range-zero capture fixtures show that
bound-variable scope does not imply free-variable freshness or source round trips.
No checker change, dependency, new axiom, or admitted proof is introduced.

Focused executable replay checks 17 declarations in `Verify.InductiveParamScope`,
assuming imported dependencies and the explicitly audited interfaces are correct.

`tests/BindingScope.lean` contains thirteen proof regressions and thirteen axiom
audits for context scope, declaration types/let values, the scoped generic binding
bridge, partial/full forall reconstruction, lambda reconstruction, and empty
contexts. Negative proof boundaries cover loose bodies/domains/values and repeated
identifiers. The audits separate existing array/map bridges from abstraction,
loose-variable metadata, and lowering interfaces; typed statements inherit
`sorryAx` from the existing translation stack, while the raw binding and empty
scope statements do not.
Three hundred twenty syntactically scoped forall/lambda fixtures compare the
executable binding against both the sequential binding fold and `MLCtx`
reconstruction (640 equalities). They cover 0/1/2/3/31/32/33/65 binders,
dependent domains, used/unused lets, repeated/anonymous user names, all binder-info
forms, and ten expression forms including metavariables/external free variables.
These are structural scope fixtures, not semantic well-formedness witnesses.
Ten negative runtime fixtures isolate four loose-body failures, two loose-domain
failures, two loose-let-value failures, and two duplicate-ID failures. The latter
also check the minimal native `.bvar 0` versus sequential `.bvar 1` observation
with a range-zero free-variable body. Run `lake env lean tests/BindingScope.lean`.
The former sequential-abstraction interface is corrected by the raw specification
and scoped/distinct proof; the native implementation bridge remains trusted.
See `divergences.md`.

`tests/NativeAbstraction.lean` contains fourteen proof regressions and fifteen
axiom audits for selected-index bounds, empty/cons raw abstraction, scoped/distinct
sequential agreement, and raw/native arity preservation. Ten audits use only
logical axioms; five additionally use the corrected existing `Expr.abstract_eq`.
All exclude `sorryAx`. Nine hundred twelve raw native/model fixtures cover twelve
empty/single/multiple/wide ID arrays, including duplicates in different positions,
nineteen expression forms, and 0/1/2/33 surrounding binders. They include existing
loose/bound variables, unmatched metavariables sharing a free-variable name,
dependent domains/let values, both nondependent-let flags, and all constructors.
Every case also checks native leading-binder preservation at starting counts
0/1/7 (2736 checks); 396 scope/distinctness cases additionally compare the
sequential model. Run `lake env lean tests/NativeAbstraction.lean`.

`tests/InductiveParamReconstruction.lean` contains sixteen proof regressions and
sixteen axiom audits for source freshness, fresh instantiation/abstraction,
extracted-context binding scope, sequential continuation reconstruction, native
round trips, arbitrary native continuations, and the no-free-variable corollary.
All audits exclude `sorryAx`; seven use only logical axioms.
Six hundred twenty-four native/sequential/direct-callback source fixtures
(1872 reconstruction comparisons) cover three generator states,
0/1/2/3/31/32/33/65 parameters,
dependent/external-variable domains, prior generated free variables, repeated
binder names, all binder flags, both let flags, remaining binders, metadata,
projections, literals, and expression/level metavariables. Twelve capture cases
isolate current/future generated IDs in bodies and later domains. Six loose-source
cases distinguish native reconstruction failure from valid sequential inversion;
three parameter-shortage cases retain the exact diagnostic. These are helper
boundaries, not accepted ill-typed frontend declarations. Run
`lake env lean tests/InductiveParamReconstruction.lean`.

`tests/InductiveSourceChecks.lean` contains eight proof regressions and eight
axiom audits for the preflight, clean-source no-op, original-source frontend
contracts, and generator-independent freshness. Twenty clean source batches
cover empty/single/multiple/wide datatype and constructor lists; 168 invalid
batches place fourteen free-variable/expression-metavariable/level-metavariable
forms in first, middle, and last headers/constructors. Every rejection retains
the exact original name/expression, including metavariable-first diagnostics.
Sixteen source-capture frontend rejections cover four generator-ID choices,
both safety modes, and both check-flag settings. Twenty-four clean plain/nested
inputs all pass native validation across 0/1/2 parameters and both safety/check
settings. Sixteen also pass the lean4lean frontend; eight parameterized nested
cases record its existing loose-bound-variable rejection, not repaired here.
An explicitly unguarded old preprocessing/checking pipeline still
demonstrates its source capture. Run `lake env lean tests/InductiveSourceChecks.lean`.
The minimal native-only reproducer is `tests/NativeInductiveSourceCapture.lean`;
it asserts acceptance and exact constructor-type mutation on pinned Lean 4.29.0.

Focused executable replays check 168 declarations in `Verify.Axioms`,
817 in `Verify.Expr`, 144 in `Verify.LocalContext`,
440 in `Verify.TypeChecker.Basic`, 210 in `Verify.TypeChecker.InferType`,
41 in `Verify.InductiveParamBinding`, and 17 in `Verify.InductiveParamScope`,
assuming imported dependencies and the explicitly audited interfaces are correct.

`tests/ConstructorParams.lean` contains twelve proof regressions and eighteen axiom
audits, all excluding `sorryAx`. The core constructor-loop arity proof uses
standard logical axioms and the existing `Lean.Expr.eqv_eq` and
`Lean.Expr.instantiate1_eq` interface axioms. The guarded bridge additionally
uses the existing expression free/metavariable-flag interfaces and
`Lean.Level.hasMVar_eq`. No new axiom, admitted proof, executable checker path,
or cache is introduced. The constructor-loop spine proof additionally exposes
the successful traversal's terminal return expression and its syntactic
`isValidIndAppIdx` witness; it uses only the same expression interfaces.
`checkConstructors.spine` lifts that witness through the complete nested
datatype/constructor batch and retains the concrete datatype index so duplicate
array entries do not introduce an unjustified `idxOf` uniqueness premise.
`checkInductiveTypes.registeredConstructorSpine` carries the same witness
through the actual header-registration/environment-replacement callback and
the final `(stats, env)` result without assuming header or constructor metadata
soundness.
`checkConstructors.loop_positive_spine` adds a safe-mode field witness only
under an explicit WF contract for `checkPositivity` that supplies a normalized
expression, a caller-provided WHNF relation, and its no-occurrence result; it
does not treat opaque WHNF reduction as syntactic preservation or assert
unconditional positivity.
Eleven return-application fixtures check missing,
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
`tests/InductivePositivity.lean` adds thirteen proof regressions and seven axiom
audits, excluding both `sorryAx` and expression interface axioms. Twelve
classifier fixtures cover empty, mutual, duplicate, parameterized, and indexed
datatype arrays. Twenty-eight positivity outcomes cover nonrecursive and
recursive fields, higher-order positive and negative domains, dependent index
instantiation, invalid recursive indices, annotation/let/beta normalization,
seeded fresh names, and independent constructor/WHNF fuel exhaustion. A beta
erasure boundary checks that an accepted normalized expression can lack an
occurrence present in the raw source. These are helper-boundary fixtures, not
full declaration acceptance or semantic positivity evidence.
Twenty-five further safe constructor-loop outcomes cover stored parameters,
fresh nonrecursive/recursive fields, higher-order positive and negative fields,
dependent return indices, annotation consumption, seeded fresh names, wrong
parameter domains/returns, and fuel exhaustion. An unsafe control confirms the
positivity check is bypassed only outside the theorem's safe-mode scope, and an
accepted recursive-field occurrence demonstrates why normalized absence alone
is insufficient. These remain helper-boundary tests: an open return can still
be accepted without consuming its stored parameter when the source guard is
bypassed.

`tests/ConstructorBatchPositivity.lean` adds six proof regressions and three
standard-logical-only axiom audits for the full safe-batch trace contract,
indexed extraction, spine projection, and exact root context under `withEnv`.
Thirty batch outcomes cover empty arrays and constructor lists, recursive and
higher-order fields, mutual parent indices, repeated names across distinct
parents, later duplicate/positivity/source/type failures, dependent indices,
parameter consumption, seeded fresh names, and independent per-constructor
fuel. An unsafe control confirms that negative fields are outside the safe
theorem's scope. The source guard rejects an open parameter return that the
inner loop alone can accept. These fixtures check the actual full constructor
batch in an imported environment with explicit statistics; they do not check
the datatype headers or claim complete declaration acceptance.

`tests/RegisteredConstructorPositivity.lean` adds six proof regressions and two
standard-logical-only axiom audits for the checked-type/header/safe-batch
composition, successful-result extraction, indexed traces, fixed frame fields,
and the declared parameter count for nonempty inputs. Twenty-six prefix
outcomes cover empty input, recursive and higher-order fields, one/two
parameters, mutual and indexed datatypes, seeded local contexts, universe
parameters, nested-header metadata, header freshness, later failures, and fuel.
Successful fixtures inspect the returned root, installed headers, preserved
imported constants, and absence of constructor registration. An indexed mutual
boundary confirms that later index locals occur in the trace root but not in
`stats.lctx`. These fixtures exercise the actual registered-header prefix, not
constructor/recursor registration or complete declaration acceptance.

`tests/SafeConstructorRegistration.lean` adds eight proof regressions and four
axiom audits for the combined registration contract, arbitrary continuations,
successful-result extraction, root-indexed traces, exact constructor records,
old-entry preservation, declared parameter alignment, and both map-validity
witnesses. Twenty-six executable prefix outcomes cover recursive and
higher-order fields, one/two parameters, mutual and indexed batches, universe
parameters, seeded contexts, nested metadata, later failures, and fuel.
Successful fixtures inspect exact headers in both environments, exact
constructor records only in the final environment, parameter/field totals,
per-parent constructor indices, and preserved imported constants. Registration
rejects constructor names shared across parents or colliding with headers or
imported entries, even where checker-only acceptance is possible. An indexed
boundary keeps the header root distinct from the constructor environment and
retains later index locals absent from `stats.lctx`. The fixtures stop before
elimination/recursor generation and do not claim full declaration acceptance.

`tests/InductiveRunRegistration.lean` adds forty-two proof regressions and twenty-two axiom
audits for the complete runner's intermediate registration witness, successful
result extraction, safe-root positivity traces, intermediate metadata/map
validity, indexed spine projection, final exact recursor metadata, generated
counter alignment, rule-source context preservation, installed rule name/order/
count correspondence, exact starting/ending minor-prefix receipts, stronger
certificate compatibility, positional rule/registered-constructor field-count
alignment, source-array minor indexing and present-entry extraction, positional
RHS receipts at present local minors, counted recursive application arguments
bounded by the actual registered constructor's field count, free-variable shape
of the same generated field/selection witnesses, and the combined declared
metadata contract. Thirty-two full-run outcomes cover
empty input, recursive and higher-order fields, one/two parameters, mutual and
indexed types, seeded contexts, universe parameters, rejection paths, and fuel.
Seven added fixtures cover empty input with nested metadata, an empty middle
datatype, reordered mutual declarations, thirty-three constructors, empty input
with zero fuel, an empty constructor list with one fuel, and nonempty nested
metadata.
Successful fixtures inspect installed headers, constructors, recursors, and
rules, including closure and numeric/name metadata as runtime smoke checks;
these are not semantic recursor proofs. Early and late boundaries distinguish
constructor-prefix acceptance from duplicate-universe rejection and a recursor
name collision after successful constructor registration. An unsafe negative
field control remains outside the theorem's explicit safe-context scope.
The stronger metadata certificate preserves the distinct intermediate
constructor environment and original positivity root while identifying installed
records in the actual final environment. It does not transport WHNF or cover
earlier declaration preprocessing guards. All nine metadata/order/offset/field/indexing/RHS/count/shape
runner audits use only the existing map and guarded-arity interfaces; five
compatibility/source/count projections use only standard logical axioms, while
the two field projections additionally use the existing `Expr.instantiate1_eq`
interface. The indexed-source and local-RHS/count/shape projections use only standard logical axioms.
All audits exclude `sorryAx`.
Empty batches with a nonzero declared parameter count remain proof-only
boundaries: the known terminal assertion does not justify runtime acceptance.

`tests/InductiveRunScope.lean` adds ten proof regressions and ten axiom audits for
continuation morphism equations, coupled recursor continuations, actual complete
safe-run scope certificates, minor-offset compatibility, original-reader/source
projections, root validity/reservation, old constant lookups, and installed
distinct RHS receipts. Sixteen complete safe runs cover empty and constructorless
batches, recursive/higher-order fields, repeated thirty-three-field labels,
shared parameters, mutual parents with an empty middle datatype, dependent
indices, default/seeded contexts with old declarations/lets, nested-count
metadata, and zero-fuel empty batches. Instrumented actual readers retain exact
root/constructor/source boundaries and native lookups; direct complete runs
agree on installed recursor metadata and every literal RHS recipe. Replays use
the actual elimination universes and local minor entry, preserve distinct
ordered field selections, and check exact offsets. Five early/late failures
cover fuel, parameter shortage, duplicate constructors, imported-header and
late-recursor collisions. Five continuation fixtures compare captured callbacks
with direct CPS traversal on successful and rejected prefixes. All ten audits
exclude `sorryAx`; morphism/compatibility equations use only standard logical
axioms, structural continuations add existing map/list-push interfaces, and full
registration adds existing constructor metadata/arity interfaces.
Run `lake env lean tests/InductiveRunScope.lean`. No semantic domain/value typing,
normalization transport, public frontend acceptance, or inductive soundness is
claimed by these structural receipts.

`tests/InductiveFrontendScope.lean` adds eight proof regressions and eight axiom
audits for the exact public stages, operational no-auxiliary specialization,
actual primitive-dispatch branch, and preservation/local-rule projections.
Ten successful fixtures cover constructorless datatypes, recursive/higher-order
and repeated thirty-three-field constructors, shared parameters, dependent
indices, mutual parents with an empty middle datatype, unused and polymorphic
universes, and primitive `Bool`/`Nat` addition in empty environments. Each keeps
the exact successful preprocessing result and zero auxiliary count, compares
instrumented/staged/public records and both declaration check flags, retains
separate header/positivity and constructor environments, checks actual source
readers and native declared distinct fields, and replays every stored RHS with
the actual elimination universes, local minor, and exact prefix offsets. Old
`Nat`/`List` lookups are unchanged where present. Sixteen negative controls cover
empty batches, original source free variables, preprocessing fuel exhaustion,
parameter shortage, duplicate constructors/universe parameters, imported names,
and late recursor collisions. A successful nested `List` control has nonzero
auxiliaries and is explicitly outside the no-auxiliary certificate. All eight
audits exclude `sorryAx`; no semantic preprocessing/restoration or inductive
soundness claim is made. Run `lake env lean tests/InductiveFrontendScope.lean`.

`tests/InductiveFrontendRestoration.lean` contains fifty-four proof regressions
and forty-nine axiom audits for fresh trace composition, preservation/final lookup
classification, individual/batch restoration receipts, both public frontend
branches, and actual declaration dispatch. Twenty-two native-accepted safe fixtures
cover direct and nested inputs with zero/one/two parameters, repeated nested
fields/auxiliary reuse, a mutual batch with an empty original datatype, closed
recursive index arguments, and polymorphic universes. Both declaration check
flags and the direct public frontend agree with staged/restored records;
checks include exact headers, constructor types, renamed main/auxiliary recursor
metadata, every restored rule name/RHS, auxiliary header/constructor non-leakage,
and old `Nat`/`List`/`Bool` lookups. Helper controls reject colliding installed
headers, constructors, and main/auxiliary recursors; frontend controls retain
source/preprocessing failures, and a final auxiliary check rejects zero
recursion-depth fuel after restoration registration. All forty-nine audits
exclude `sorryAx`; no semantic restoration or inductive soundness is claimed.
The metadata extension adds twenty-two proof regressions and seventeen audits
for receipt composition, complete individual/batch installation, final exact
record projections, coupled successful preprocessing/runner equations, source
coverage derived from checked rewritten metadata and pure name-map coverage,
and both public dispatches. Five proof-only controls expose omitted recipe
entries and missing header/constructor/main/auxiliary sources; no panic branch
is executed to manufacture an installation guarantee. Existing nested fixtures
also verify pure rewritten-name/auxiliary-rec coverage, the complete expected
record count, distinct output names, and every final recipe lookup. The name
extension adds nineteen proof regressions and eighteen audits for positional
prefix composition, preprocessing retention, exact auxiliary-name enumeration,
derived staged coverage, coupled complete stages, and both public installation
projections without a coverage premise. Five added proof-only controls reject
shortened/reordered prefixes and retain empty/missing-header/short-suffix name-map
defaults; no panic is executed as a test fixture. All successful inputs check
the exact original-name prefix; nested fixtures check exact auxiliary-rec suffix
enumeration. Three new native-accepted fixtures cover direct and nested
three-original batches, distinct nested auxiliary groups, and deeply nested
`List (List I)` occurrences. Complete nested installation no longer needs caller
coverage, but does not establish semantic preprocessing/restoration correctness.
The constructor-signature extension checks exact raw header types and ordered
source constructor names/counts through preprocessing, then verifies every
source constructor's staged/final parent, position, parameter count, universes,
safe flag and exact direct/restored record under its original name. Four new
native-accepted fixtures have three constructors with zero/one/three fields,
cover nested zero/one-parameter and direct two-parameter families, and a mutual
batch with two multi-constructor parents and an empty original datatype. Both
declaration flags and the direct public frontend retain these checks.
Run `lake env lean tests/InductiveFrontendRestoration.lean`.

`tests/InductiveSourceConstructors.lean` adds twenty-five proof regressions and
twenty-four axiom audits for exact nested datatype-array frames, compositional
signature prefixes, header/constructor-list retention, constructor counts and
positions, actual preprocessing, source-indexed checked metadata, coupled
successful stages and both public frontends. Direct/nested final projections
retain the same staged constructor. Four proof-only controls reject altered
headers, altered constructor order/counts and missing staged source constructors
under a checked signature certificate. No panic fixture is executed; all audits
exclude `sorryAx`. Constructor type equality and semantic soundness are not
assumed. Run `lake env lean tests/InductiveSourceConstructors.lean`.

`tests/InductiveSourceArity.lean` adds thirty-two proof regressions and twenty-four
axiom audits for constant-headed applications, optional/nested replacement,
same-success parameter extraction, re-abstraction, the actual constructor callback,
compositional arity prefixes, the growing preprocessing loop, checked staged field
counts, coupled source/final metadata and both public frontends. Four proof-only
failure controls reject changed arity vectors, wrong field counts, insufficient
raw arity and missing final source constructors; a metadata-wrapped forall control
keeps raw arity distinct from WHNF arity. All audits exclude `sorryAx`, with explicit
existing interface allowances. The native-accepted restoration fixtures
also compare every original/staged raw constructor arity and check both field-count
equations, retaining exact final record checks for both flags and the direct public
frontend. Run `lake env lean tests/InductiveSourceArity.lean` and
`lake env lean tests/InductiveFrontendRestoration.lean`.

`tests/InductiveSourceRules.lean` adds thirty proof regressions and eighteen axiom
audits for source minor offsets/flattened lookups, ordered source rule pairs,
checked constructor consistency, same-source exact rule-generator receipts,
coupled complete stages, final rule counts/indexed field metadata and both public
frontends. Six proof-only failure controls reject changed rule counts/labels,
missing rules, wrong field counts, changed prefix minor offsets and absent final
recursors. Empty source lists, empty parents and both literal rename-map branches
are covered without executing panic defaults. The restoration test now checks
staged source rule pairs/minor offsets, rule-to-constructor field consistency and
exact final recursor recipes for twenty-four native-accepted fixtures, both flags
and the direct public frontend. Two added fixtures put an empty original datatype
before a three-constructor parent, on direct and nested branches, exercising zero
minor offsets and retained empty recursors. Run
`lake env lean tests/InductiveSourceRules.lean` and
`lake env lean tests/InductiveFrontendRestoration.lean`.

`tests/InductiveOriginalRecursorNames.lean` adds thirty-three proof regressions and
fifteen axiom audits for actual header/runner name uniqueness, prefix/suffix
nonoverlap, recursor-name injectivity, literal map-key support, derived original
recursor identity, final original labels/counts/fields, indexed checked constructor
metadata and both public frontends. Proof-only controls cover duplicate datatype
names, overlapping suffixes/rename keys, changed map values, missing final
recursors and a malformed header whose auxiliary suffix aliases an original name.
Logical empty/missing/non-inductive-header and short-header defaults are proved
without executing panic fixtures. Empty source/constructor lists and both exact
restoration branches are covered. All twenty-four native-accepted restoration
fixtures now check final original-name lookups and original constructor-label/field
pairs; nested fixtures also check actual rename-map absence and fallback identity.
Run `lake env lean tests/InductiveOriginalRecursorNames.lean` and
`lake env lean tests/InductiveFrontendRestoration.lean`.

`tests/InductiveSourceRecursorRecords.lean` adds thirty-seven proof regressions
and sixteen axiom audits for same-source exact generated records/rule recipes,
retained recursor headers, original-name final lookups, exact type/`all`/indexed
RHS restoration, checked constructor fields and both public frontends. Empty
source lists and both literal restoration branches are covered without requiring
nonempty helper inputs or executing panic defaults. Twelve proof-only failure
controls reject wrong indices/motive/minor counts, changed K/level/safety fields,
wrong direct/nested final types, wrong restored `all`, changed RHS expressions,
missing indexed rules and missing final recursors. All twenty-four native-accepted
restoration fixtures now check staged header/count metadata, retained final
levels/counts/K/safety and exact indexed source-to-final RHS expressions, both
flags and the direct public frontend. No semantic typing/reduction claim is
added. Run `lake env lean tests/InductiveSourceRecursorRecords.lean` and
`lake env lean tests/InductiveFrontendRestoration.lean`.

`tests/InductiveHeaderScope.lean` adds nine proof regressions and seven axiom
audits for arbitrary checked-header continuations, coupled scope/statistics,
root validity/reservation, declaration extension, old native lookups, environment
rebasing, constructor-root continuations, and coupled safe registration.
Thirty-six header fixtures cover safe/unsafe and default/seeded contexts, shared
and dependent parameters, differently indexed mutual parents, normalized aliases,
polymorphic sorts, thirty-three fresh indices, and the zero-fuel empty batch.
Native iteration checks declaration indices, distinct identifiers, lookup/list
agreement, reservation, immutable readers, and exact allocation counts; seeded
contexts retain both an old declaration and a let. Six constructor prefixes
retain actual positivity roots and separate header/constructor environments.
Six failure fixtures retain exact fuel, parameter, universe, and continuation
diagnostics. An unreserved helper demonstrates native overwrite outside the
theorem's premises. All seven audits exclude `sorryAx`; only the coupled
registration audit adds the existing constructor metadata/arity interfaces.
Run `lake env lean tests/InductiveHeaderScope.lean`. These guarantees are
structural, not semantic typing or full inductive soundness.

`tests/RecursorFieldDistinct.lean` adds twelve proof regressions and eleven axiom
audits for fresh-identity exclusion, distinct-vector growth, arbitrary traversal
continuations, selected-field distinctness, coupled RHS receipts, positional
sequence projections, stored-rule/local-minor composition, and the complete
generation/registration suffix certificate. Twelve helper fixtures cover empty,
recursive, mixed-visibility/higher-order, dependent-domain, and thirty-three-field
telescopes under default/seeded generators, skipped parameters, and unchecked
forall-valued parameter substitution. All generated binders share the `field`
label; identities are checked against chronological generator allocation, not
labels. Eight exact RHS replays cover zero/shifted offsets and zero/one/two/
thirty-three fields, preserving distinct selected vectors, count bounds, and
literal recipes. A declared-duplicate vector control distinguishes membership
from distinctness; zero-fuel and partial-allocation failures still propagate.
Audits use only existing logical/map/list-push interfaces, with the third map
interface needed only for actual registration, and exclude `sorryAx`.
Run `lake env lean tests/RecursorFieldDistinct.lean`. These helper controls do
not claim full frontend acceptance or semantic typing.

`tests/RecursorInfoScope.lean` adds six proof regressions and eight axiom audits
for actual source-reader validity/reservation, old native lookup preservation,
coupled count witnesses, and scope-certified generation/registration. Nine
direct generation fixtures and their registrations exercise empty input,
constructorless parents, nullary/ordinary recursive constructors, higher-order
recursion, indexed headers, mutual recursion with an empty middle parent, and
parameterized constructors under a seeded generator and existing declaration,
and thirty-three recursive fields/hypotheses with repeated binder names.
Native source declaration-list/map agreement, old lookups, next-name freshness,
exact context/generator advancement, actual index/major/motive/minor declarations,
and recursor/rule counts are checked. Zero-fuel and partially allocated traversal
failures propagate. An unchecked free-variable header control shows that structural
context validity is not a header-typing theorem. These unchecked helper fixtures do not claim complete frontend
acceptance or semantic typing.

`tests/RecursorInfoIndices.lean` adds twenty-six proof regressions and sixteen
axiom audits for actual scoped normalization traces, terminal/parameter/vector
bounds, raw arity, generated declarations, exact major domains, preservation
through minor updates and same-success generation/registration receipts. Six
proof-only controls reject decreasing parameter positions, shortened vectors,
forall terminals, wrong info-array sizes, absent majors and altered major types.
Ten fixtures start from actual checked headers and exercise zero/one/thirty-three
indices, differently indexed mutual parents, dependent parameters, recursive
constructor minors, a seeded reader and polymorphic parameters, followed by the
actual registration suffix. Two alias fixtures show strictly larger normalized
binder counts than raw source arity; their runtime index/header equality checks
are not a general normalization-transport theorem. Boundary fixtures cover a
terminal helper with unconsumed parameters, zero/partial fuel, unchecked stored
index counts and an untyped free-variable header. No panic default is executed,
and helper fixtures do not claim full frontend acceptance or semantic typing.
Run `lake env lean tests/RecursorInfoIndices.lean`.

`tests/InductiveHeaderTraces.lean` adds fifteen proof regressions, six proof-only
failure controls and fourteen axiom audits for checked-header traces, terminal
parameter consumption, index-count bounds, preserved header arrays/shared
parameters and same-success checked-header source receipts. Fifteen native
fixtures cover empty and mutual headers, fresh/reused/dependent parameters,
heterogeneous index counts, initial/tail/domain aliases, annotated/let/beta
headers, polymorphic and seeded readers, and exact sufficient traversal fuel.
Six fixtures expose strictly larger normalized binder counts than raw source
arity. Ten failure fixtures retain source-variable/type, parameter, universe,
fuel and continuation rejection; three direct-helper controls distinguish
initial statistic validity and terminal-sort checking from the structural
trace's complete parameter-consumption guarantee. These runtime checks do not
prove WHNF transport or checked/generated index equality.
Run `lake env lean tests/InductiveHeaderTraces.lean`.

`Verify.InductiveHeaderModels` builds a canonical checker model directly from
the accepted first-header source trace. `acceptedHeaderNormalization` transports
the initial source translation through the recorded WHNF result. The recursive
`CheckedHeaderTrace.firstModels` provider then follows each actual fresh
parameter/index allocation and recorded normalization, resetting the semantic
checker state only after proving a distinct fresh-name prefix, preserving the
existing context lookups and ambient reader frame. It returns one
`ParameterPrefix` for the canonical parameters and a second prefix for the
retained index suffix, rather than identifying the full indexed reader with the
parameter-only context. `FirstHeaderCheckerModels.selectedParameterDomain`
recovers each canonical parameter's stored-domain translation, semantic sort,
and native lookup through that split, including lookups retained by subsequent
index binders. A public `checkInductiveTypes.firstModels` adapter supplies this
model from the actual first member of a successful nonempty header batch.
`FirstHeaderCheckerModels.constructorDomainReceipts` now composes the two
prefixes into the full constructor reader and invokes the split constructor
receipt provider, so accepted constructor receipts terminate at the parameter
model while the header's index suffix remains explicit.

The provider uses the existing unrestricted annotation-domain peeling theorem,
so accepted annotations may have distinct but definitionally equivalent literal
universes. It does not invent WHNF or type checks: every normalization and
source acceptance premise is the corresponding native call recorded by
`CheckedHeaderTrace`. It remains a conditional model theorem: the semantic
environment, initial checker correspondence/WF, reset-name separation and
canonical annotation constants/definitions are explicit. It does not yet prove
full mutual-family registration, constructor positivity, recursor generation,
or the final frontend theorem.

`tests/InductiveHeaderModels.lean` adds six proof controls and twenty-eight
runtime controls. Runtime cases cover zero/one/two parameter/index combinations,
both safety flags, retained old locals, dependent peeled domains, mixed
nonuniform annotation universes, mutual later-header index suffixes and rejected
bad arity/free-variable headers. The fixture explicitly proves that a full
indexed reader is not a parameter-only prefix, splits the canonical history at
the parameter boundary, and retains parameter lookups across indices. The new
production module has twenty exhaustive declarations; accepted-trace/source
bridges retain the existing checker dependencies and source-guard expression
dependencies, with no module-owned axiom or new admission. No kernel
discrepancy found.

`tests/InductiveIndexAlignment.lean` exercises explicit telescope stability under
arbitrary substitution and different normalization readers, exact checked and
generated binder counts, complete parameter consumption when enough binders
exist, source-receipt count alignment, arbitrary CPS callbacks, registration and
the actual safe declaration prefix. Sixteen axiom audits exclude `sorryAx`.
Twenty-two native safe prefixes cover empty/mutual/dependent/polymorphic
headers, differing index counts, alias domains and binder information, exact
sufficient fuel, seeded fresh-name/local readers, both K metadata flags and
recursive constructor minors. They check equality of checked, generated and
registered index counts and retained local declarations. Four direct-helper/
fuel controls retain inconsistent stored-count, incomplete-parameter and
partial traversal behavior. A hidden-header alias still succeeds with a strict
raw/normalized arity gap but is deliberately excluded by the theorem's explicit
fragment premise. Proof-only controls reject incorrect counts and non-telescope
spines. General alias transport and semantic binder typing remain separate.
Run `lake env lean tests/InductiveIndexAlignment.lean`.

`tests/InductiveNormalizedHeaders.lean` adds seven proof regressions for the
canonical normalized receipt and checked/recursor/source/generator bridges,
five axiom audits, ten native annotated/let/beta/mixed fixtures and three
unchecked-count/partial-fuel controls. Runtime fixtures verify actual
checked/generated/registered counts but intentionally do not turn wrapper
normalization into an unproved theorem. Run
`lake env lean tests/InductiveNormalizedHeaders.lean`.

`tests/InductiveNormalizedWrappers.lean` adds sixteen proof regressions and
thirteen axiom audits for concrete metadata, let and beta receipts, used
substitutions, actual safe-prefix specializations and the normalized
registration bridge. Fifty-one native registration prefixes and fifty-one
successful WHNF observations cover outer annotations,
mixed wrappers, dependent parameters, substituted index domains, zero indices,
mutual declarations, polymorphic readers and seeded local/fresh-name contexts;
they preserve strict raw/normalized arity gaps and registered index metadata.
Seven fuel, unchecked-statistics and under-binder wrapper controls retain the
exact proof boundary; direct let/beta normalization succeeds at depth two and
WHNF-loop fuel one. Axiom audits reject `sorryAx`. Let receipts use only the
existing `Expr.instantiate1_eq` substitution interface beyond logical axioms;
beta additionally uses `Expr.instantiateRange_eq` and `Expr.instantiate_eq`.
Safe/registration bridges inherit only the existing persistent-map/list and
substitution interfaces. Run
`lake env lean tests/InductiveNormalizedWrappers.lean`.

`tests/InductiveWrappedSpines.lean` adds eighteen proof regressions and seventeen
axiom audits for finite mixed-wrapper witnesses, canonical normalization and
safe registered counts. Used let-to-beta and beta-to-let substitutions,
captured-domain substitution across nested binders, and let exposure of a
wrapped value all construct actual traces. A five-parent safe mutual prefix
uses those traces without an external normalization oracle. Across four
readers, 208 actual registration prefixes and 207 successful WHNF observations
exercise all wrapper pairs/triples, mixed depth 65, metadata depth 128,
dependent parameters and seeded locals. Metadata-only normalization succeeds
at method depth one with zero WHNF-loop fuel; mixed core descent succeeds with
one outer WHNF iteration. Nine fuel errors, unchecked stored counts and a
poisoned existing core-cache control retain partiality and the explicit
empty-core-cache premise. `shape` is axiom-free; core/full receipts use only
logical axioms and the three existing expression-substitution interfaces.
Scope/registration bridges inherit the existing map/list interfaces; every
audit rejects `sorryAx`. No executable checker path or cache is added. Run
`lake env lean tests/InductiveWrappedSpines.lean`.

`tests/InductiveBinderDomains.lean` adds seventeen proof regressions and
twenty-four axiom audits for actual telescope openings, shared parameter
histories, native index-domain lookups, paired signatures and safe registration.
Its concrete finite-wrapper safe prefix retains checked source receipts and
domain alignment without a normalization oracle. Across four readers, 44
registration fixtures cover 56 parents and 112 separately checked/generated
opening plans, including dependent `Eq` domains, annotations, binder metadata,
domain aliases and mutual reused parameters. Each plan matches its own actual
local declarations; corresponding fresh IDs and dependent domains deliberately
differ. An axiom-free counterexample shows that equal ordered signatures and
shared parameters do not imply equal domain expressions. Controls retain
different reused-parameter source syntax, raw-arity gaps, arbitrary/undeclared
parameter substitutions, unchecked stored counts and unconsumed extra helper
parameters. All audits reject `sorryAx` and use only existing logical,
substitution and scope/map/list interfaces. Run
`lake env lean tests/InductiveBinderDomains.lean`.

`tests/InductiveBinderPrefixes.lean` adds seventeen proof regressions and
twenty-nine axiom audits for ordered checked/generated roles, deterministic
shared-parameter opening, complete parameter-step equality, and exact first
index raw/consumed/native-declaration types. Its concrete wrapped mutual
safe-prefix proof supplies normalization rather than assuming an oracle.
Across five readers, 90 registration fixtures cover 100 parent pairs and
200 opening plans, including zero/multiple/shared parameters, zero/dependent
indices, annotations, aliases and wrappers. Controls preserve unequal second
dependent domains, interleaved pure-opening roles, changed arbitrary
substitutions, unchecked counts and unconsumed extra parameters. Structural
prefix/opening and first-declaration comparison lemmas use only `propext`;
all audits reject `sorryAx` and use only existing logical, substitution and
scope/map/list interfaces. Run
`lake env lean tests/InductiveBinderPrefixes.lean`.

`tests/InductiveBinderRenaming.lean` adds twenty-seven proof regressions and
fifty-six axiom audits for structural correspondence, arbitrary sequential
substitutions, exact chronological index histories, consumed provenance and
both native declaration projections. Concrete wrapped mutual registration
supplies normalization rather than assuming an oracle. Across five readers,
160 full registration fixtures cover 175 parent pairs, 350 opening plans,
715 paired domain steps (raw and consumed), 245 shared parameter records and
470 differing fresh-index pairs. Five additional registration runs retain
ten concretely unequal later-domain type comparisons. Fixtures include deep
dependencies, multiple parameters, metadata and let/app/forall/lam/proj
domains. Negative proofs and controls reject unpaired, reversed, future-only
and own-step pairs, changed constants/levels/metadata, and reversed
dependencies. Structural checks of consumed outputs are empirical fixture
measurements only; general consumed-output structural compatibility is not
proved. All audits reject `sorryAx` and use only existing logical,
substitution and scope/map/list interfaces. Run
`lake env lean tests/InductiveBinderRenaming.lean`.

`tests/InductiveBinderAllocations.lean` adds twenty-six proof regressions and
fifty-three axiom audits for exact native declaration indices, ordinal
allocation receipts, distinct index IDs, full injective zip projections,
fake-position rejection and duplicate-ID/pair controls. Concrete wrapped
registration uses proved normalization traces. Across five dense readers,
100 registration fixtures cover 125 parent pairs and 250 opening plans,
275 fresh index pairs and 205 shared parameter records. They check native
`find?`, physical `getAt?`, stored indices, contiguous per-parent allocations,
reused parameters and intervening major/motive allocation gaps. Physical slot
checks are empirical, not a general proved slot contract. Four separate
unchecked hole registrations cover six additional parent pairs, explicitly
outside the existing dense `LocalContext.WF` fragment. Counterexamples retain
overlapping injective pairs, identical IDs across independent different
readers and nondeterministic identity-or-listed-pair correspondence. All
audits reject `sorryAx` and use only existing logical, substitution and
scope/map/list interfaces. Run
`lake env lean tests/InductiveBinderAllocations.lean`.

`tests/InductiveIndexLookup.lean` adds thirty-nine proof regressions and
seventy-six axiom audits for deterministic listed lookup, fixed shared
parameters, same-witness native allocation/support receipts and the actual
supported-header extraction. All audits reject `sorryAx`. Across five dense
readers, 100 full registrations cover 125 parent pairs; four additional
hole-reader registrations remain unchecked controls outside `LocalContext.WF`.
Eight generic lookup control groups cover overlapping and identity pairs,
duplicate-key precedence, a sufficient-but-not-necessary parameter boundary,
target overlap, every expression constructor and global noninjectivity.
Independent-reader helpers preserve identical IDs without assuming global
source/target separation. A successful unchecked helper deliberately aliases
a future shared-parameter ID with an allocated index, demonstrating why
ordinary helper success alone does not establish parameter support. This is
a missing-premise boundary, not an accepted invalid complete declaration or
kernel discrepancy. Run `lake env lean tests/InductiveIndexLookup.lean`.

`tests/InductiveIndexLookupOpening.lean` adds forty-five proof regressions
and seventy-five axiom audits, all rejecting `sorryAx`. It compares 1,440
single substitutions and 864 loose-variable lifts across all twelve expression
constructors, six finite pair lists, nonzero depths and loose replacement
variables. Forty native registrations cover forty-four parent pairs and 156
matched binder steps across four dense readers. Eight boundary-control groups
cover overlapping/identity pairs, duplicate source keys, missing source-body
support, reused targets and shared-parameter/source collisions. Regressions
retain injection/support extension premises, native freshness, contextual
opening and safe wrapped-registration operation receipts. No consumed-output
compatibility, normalization reservation or global source/target disjointness
is assumed. Run `lake env lean tests/InductiveIndexLookupOpening.lean`.

`tests/InductiveBinderLookup.lean` adds thirty-two proof regressions and
sixty-three axiom audits, all rejecting `sorryAx`. Eighty full registrations
cover 100 parent pairs and 388 binder steps across four readers; each actual
raw domain agrees with the deterministic lookup at its incoming chronological
index zip. Fixtures include dependent/multiple parameters and indices, mutual
reuse, metadata, let/beta wrappers, projections, literals and nested-let
domains. Sixty pure constructor checks and 180 substitutions span every
expression constructor and five generic pair lists. Independent-reader
controls permit identity and overlapping source/target IDs. An unchecked
successful helper retains the necessary parameter/index support boundary;
wrapper normalization is also shown not to reflect source closedness.
Consumed types now retain exact total-consumer equations and project to proved
deterministic correspondence. External native comparisons remain empirical
controls. Run `lake env lean tests/InductiveBinderLookup.lean`.

`tests/InductiveTotalAnnotationConsumer.lean` adds eleven proof regressions
and twenty-two logical-axiom-only audits for actual stored-type support,
discarded-default elimination, arbitrary-pair deterministic correspondence,
chronological scope, current/future exclusion and the same parent histories.
None assumes an external native/model equation. Three annotated-header
registrations check stored domains; a recursive registration exercises
constructor fields, positivity/function binders, recursive helpers and
recursor construction. Two unchecked index-helper allocations discard
unsupported default FVars. Existing annotation fixtures retain exact-arity,
metadata-barrier, carrier-chain, FVar-opening and empirical native controls;
the six allocation/domain/lookup fixtures use the actual total consumer in
their proof receipts. These checks establish syntactic storage properties,
not semantic local typing or full inductive soundness. Run
`lake env lean tests/InductiveTotalAnnotationConsumer.lean`.

`tests/InductiveBinderStoredTypes.lean` adds twenty-three proof regressions
and thirty-seven axiom audits, including all fourteen declarations in the
stored-type alignment module. CPS/getter/general registration consumers and
safe normalized/metadata/let/beta-wrapped prefixes compile without native
model premises. Same-witness projections retain raw/stored scope and exclusion,
actual declaration lookup/value/type/name/binder-information/index anchors,
strictly-prior maps and the full index-ID zip. Thirty-nine registrations cover
fifty-four parent pairs, 246 paired binder domains and 144 paired index
declarations across three readers, including empty, mutual, all-parameter,
dependent annotated and discarded-default cases. Generic low-level registration
proofs retain both K/safety metadata flags; independent-reader controls permit
identity/overlapping IDs, and reused parameter types retain checked `isDefEq`
without literal equality. Audits allow only logical and existing storage,
instantiation/source-guard interfaces, rejecting `sorryAx`. No semantic typing
or general normalization integrity theorem is inferred. Run
`lake env lean tests/InductiveBinderStoredTypes.lean`.

`tests/InductiveBinderIntegrity.lean` adds forty proof regressions and
seventy-one axiom audits, covering all thirty-one public declarations in the
three integrity modules; a separate whole-module census includes the private
opening helper. FVar-only support is shown to admit expression/level
metavariables, while `FVarsIn` rejects them but still permits loose BVars.
Discarded defaults, gadget universe arguments and explicit normalization
controls demonstrate preservation without reflection. Compiled consumers keep
the same raw/stored/native witnesses through normalized/wrapped sources,
CPS/getter/registration and safe prefixes. Thirty registrations cover
forty-eight parent pairs, 153 paired binder domains and 96 paired index
declarations across three readers; actual stored types are checked for
`hasMVar = false` and chronological FVar support. Five checked-source meta
rejections and two unchecked-helper controls keep clean stored output distinct
from guarded source acceptance. Audits reject `sorryAx` and allow only logical
and existing storage/instantiation/source-guard interfaces. These checks do not
establish loose-BVar closure or semantic typing. Run
`lake env lean tests/InductiveBinderIntegrity.lean`.

The depth-indexed closure extension proves `Expr.Closed` preservation for the
actual total annotation consumer, structurally modeled substitution at any
valid binder offset, and native `instantiate1` via its existing interface.
Closed replacements do not acquire loose variables when lifted under binders.
Supported metadata/let/beta normalization and actual FVar telescope opening
retain closure, with explicit source/normalized closure premises. The stronger
parent and recursor receipts keep closure on the same checked/generated
histories as the existing forty integrity facts, including actual stored index
declaration types recovered by native lookup uniqueness. They project back to
the existing integrity contracts rather than extracting unrelated witnesses.
Closure does not imply semantic local typing or exclude universe metavariables;
the separate `FVarsIn` receipts retain that universe-integrity obligation.
Conversely, `FVarsIn` alone does not imply closure, and peeling or supported
normalization may discard loose variables without establishing source closure.

`Verify.InductiveHeaderClosureGuard` proves that successful type checking rejects
native loose-bound-variable metadata before either inference cache is consulted,
even for arbitrary methods and cache states. This operational proof bypasses
the admitted semantic checker stack. Structural range bounds together with
`FVarsIn` imply depth-indexed closure, but converting the native guard to source
closure retains an explicit native/structural range bridge. The extension does
not silently use the existing unbounded `Expr.looseBVarRange_eq` interface:
native metadata has a twenty-bit range, and Lean 4.29.0 accepts BVar index
1,048,574 but panics when constructing index 1,048,575. This is a constructor
domain boundary, not silent range saturation or a newly found kernel bug.

`tests/InductiveBinderClosure.lean` adds thirty-eight proof regressions and
eighty-one strict axiom audits, including explicit rejection of the unbounded
range interface. Twenty-seven registrations span forty-five parent pairs,
141 paired raw domains and ninety paired actual index declarations across
three readers. Four successful sources and two clean cache hits contrast with
twelve checked-source rejections and forty-eight polluted-cache/uncached
infer/check rejections, including the maximum supported native BVar index.
Two unchecked-helper controls distinguish persistent loose domains from clean
stored output after discarded defaults. An independent guard audit compares
seventeen native cases and checks 104 spoofed-cache rejections. Whole-module
audits include generated/private declarations and reject `sorryAx`; all four
new modules also replay successfully through lean4lean. Run
`lake env lean tests/InductiveBinderClosure.lean`.

`Verify.ExprBoundedRange` packages the native constructor-domain premise as
`BVarRangeFits`: every raw BVar index plus one fits the twenty-bit metadata
field. This is stronger than a bound on the final loose-variable range, since
binders can hide large raw indices. Under that explicit syntactic premise,
constructor-data proofs establish native/structural range accuracy without
the unbounded `Expr.looseBVarRange_eq` axiom. They reuse the existing data-layout
interfaces and three existing bit-storage proof axioms from `Verify.Expr`;
no new axiom or native bit-proof oracle is introduced.

`Verify.InductiveBoundedHeaderClosure` combines this bound with the actual
successful type-checker guard and checked-source metavariable guard to discharge
source closure. General cache-state bridges retain separate `FVarsIn` premises:
numeric fit and a successful loose-variable guard alone do not rule out
metavariables returned by an arbitrary polluted inference cache. Supported
wrapped headers then normalize closed without an additional source-closure
or arbitrary range-accuracy hypothesis. `Verify.InductiveBinderBoundedClosure`
threads the bound-only source premise through source, CPS/getter/registration
and safe wrapped contracts, reusing the exact existing eight histories and
forty-nine facts. The numeric constructor bound remains explicit; it is not
inferred from native metadata, closure or source acceptance. No semantic typing
or full inductive soundness claim is added.

`tests/InductiveBoundedClosure.lean` adds thirty-three proof regressions and
155 strict audits, including all 122 declarations / 113 theorems in the three
new modules. Provenance checks pin the existing data interfaces and bit-proof
axioms, and reject module-owned axioms, `sorryAx` and the unbounded range
interface. Precise `simp only` lists prevent range/guard simplification from
silently importing that interface. Pure tall/high-index controls distinguish
constructor fit from closure without evaluating invalid native constructors.
Twenty-seven registrations cover forty-five parent pairs, 141 paired domains
and ninety paired index declarations across three readers. Twelve bounded loose
sources and forty-eight poisoned-cache/uncached checks reject, four bounded
meta sources fail the source guard, and two cache-accepted-meta controls preserve
the independent integrity premise. Source, normalized, CPS/getter/registration
and safe wrapped consumers compile using only the numeric bound instead of
explicit source-closure or range-equality premises. Run
`lake env lean tests/InductiveBoundedClosure.lean`.

`Verify.InductiveAnnotationModelRangeFits` preserves the constructor bound
through the actual total annotation consumer and substitution at arbitrary
binder offsets. Replacement closure and constructor fit are independent
premises: lifting an open but bounded replacement can exceed the native
constructor limit. The native `instantiate1` bridge retains its existing
interface, without an unbounded range-equality premise.

`Verify.InductiveBinderRangeFits` transports that bound through supported
metadata/let/beta normalization and actual FVar opening. Checked source guards
discharge the closure needed for supported substitution; general normalized
closure and fit remain explicit. Raw domains, peeled index domains and actual
stored index declaration types retain constructor fit. Native lookup uniqueness
ties those stored types to the same actual declarations. The opened terminal's
sort shape independently establishes its constructor fit.

`Verify.InductiveBinderMetadata` retains the exact eight histories and all
forty-nine existing closure/integrity facts, appending nine constructor-fit and
nine native-closure facts: sixty-seven facts on the same witnesses. Native
closure materializes cached loose-variable range zero and expression-meta flag
false for normalized types, raw/peeled/stored domains and both terminals. It
does not assert universe-meta absence from `Closed`; the separate existing
`FVarsIn` domain/type receipts retain that integrity boundary. Actual stored
type facts remain index-role only, not literal equality for reused parameters.
Projection and promotion reuse the old closure/integrity receipts. Source,
CPS/getter/registration and safe contracts retain these same histories, with
wrapped contracts requiring only the explicit source constructor bound. No
general WHNF closure, semantic typing or full inductive soundness is inferred;
no runtime allocation, cache or checker path changes.

`tests/InductiveBinderMetadata.lean` adds thirty-four proof regressions,
ninety-nine strict audits and six axiom-print checks. Whole-module census covers
sixty-five declarations / fifty-two theorems, including private/generated
helpers, and pins the inherited native bit-proof provenance. Pure overflow and
annotation controls retain closed-replacement and constructor-bound premises;
metadata alone is not a semantic typing or universe-integrity theorem. The
same-witness projection exposes all nine fit and nine native-closure facts.
Twenty-seven registrations cover forty-five parent pairs, 141 paired domains
and ninety paired index declarations across three readers. Runtime checks
compare native and structural ranges on raw/peeled/actual stored types, with
declaration assertions restricted to index roles. All new modules replay
through lean4lean; audits reject `sorryAx`, module-owned axioms and the unbounded
range interface. Run `lake env lean tests/InductiveBinderMetadata.lean`.

`Verify.InductiveAnnotationSemantics` proves the canonical unary and binary
annotation applications definitionally equal their carriers at the same sort.
The abstract environment explicitly contains the four identity definitions
and the `Lean.Syntax` constant. Binary reduction also uses environment
orderedness to weaken carrier typing beneath the payload binder. The proofs
use existing delta, beta, application and same-type equality rules, without
typing uniqueness, projection translation or a new oracle.

`Verify.InductiveAnnotationTyping` tracks the actual supported annotation
spine with explicit translation witnesses and local typing premises. Recursive
peeling preserves translation to a definitionally equal semantic type,
carrier-sort typing, and typing of existing inhabitants by conversion. Its
base case requires the actual consumer to leave the native expression
unchanged: metadata, lets, lambdas, projections and unrecognized heads are
barriers, not silently traversed semantic annotations. Supported wrappers have
exactly one source and semantic universe argument; the executable consumer
remains total on arbitrary malformed universe lists.

`Verify.InductiveBinderTyping` transports these per-position typed spines to
raw-domain, peeled-index-domain and actual stored-index-type judgments on the
same binder history. Actual declaration typing uses uniqueness of the same
native `find?` result, not a separately selected lookup witness. Semantic
contexts, universe levels and translations are explicit per-position inputs;
their correspondence with the native reader is not inferred. Stored-type
claims remain index-role only and do not identify reused parameter types with
raw source domains. Deriving typed spines from successful source checking,
general WHNF translation and full inductive soundness remain separate.

The semantic annotation boundary is deliberately stronger than constructor
fit, native closure or free-variable support. The canonical definitions of
`outParam`, `semiOutParam`, `optParam` and `autoParam` must be represented by
explicit equations in the abstract environment. Carrier-sort typing and
payload typing remain explicit: `optParam` takes a default inhabiting the
carrier, while `autoParam` takes a `Lean.Syntax` tactic. Successful metadata
checks do not establish these semantic premises.

The existing `TrExprS` relation itself inherits `sorryAx`, because its
projection constructor mentions the admitted `TrProj` definition. Avoiding
its transport lemmas alone does not remove that dependency. The annotation
semantic core therefore uses primitive `VEnv.IsDefEq` rules, and its source
spine is parameterized by an explicit translation relation. Instantiating
that relation with `TrExprS` retains the existing projection admission; this
boundary is not a new admission or a claim of complete checker soundness.

`tests/InductiveAnnotationTyping.lean` adds thirty-four proof controls,
107 strict audits and five axiom-print checks. Whole-module census includes
seventy-three production declarations / thirty-eight theorems, including
private/generated helpers, and allows only standard logical axioms. A separate
translation specialization explicitly confirms the inherited `TrExprS`
admission instead of weakening the clean-core allowlist. Concrete canonical
definition membership, correctly typed optional/tactic payloads, nested
spines, consumer barriers, malformed arities/universe lists, same-lookup
declarations and parameter-role exclusion are covered. Binary and nested
fixtures retain an explicit ordered-environment premise; the tests do not
claim to construct that premise. All three new modules replay through
lean4lean. Run `lake env lean tests/InductiveAnnotationTyping.lean`.

`Verify.InductiveTelescopeTranslation` derives raw-domain structural
translations and semantic sort typing from an actual translated `forallE`
header, following the same supplied `OpenedTelescope` history. Each opening
uses its actual fresh FVar and constructs the evolving virtual context with
empty dependency lists. Virtual context well-formedness, initial context
identity and per-position domain translations share the same chosen witness.
Freshness relative to the starting virtual context and earlier values remains
explicit: values already present in that virtual context and arbitrary untyped
opening values are outside this bounded theorem. Native allocation freshness
is not asserted; a native reused parameter can still be a newly represented
virtual binder when it is absent from the starting virtual context. The virtual
context stores raw semantic domains; it is not identified with the native
reader storing peeled domains.

`Verify.InductiveAnnotationTranslation` recovers typed annotation spines from
actual `TrExprS` domain translations and raw-domain sort typing. Exact canonical
constant types, abstract environment well-formedness and semantic context
typing remain explicit. A syntax-only uniform-universe premise follows just
the actual erased annotation chain. It is needed because the clean spine
relation records one literal semantic level: distinct but equivalent universe
expressions cannot silently be replaced by that literal level. Constant type
uniqueness and Pi-domain injectivity recover carrier and binary payload typing;
the desired typed spine is not supplied as a premise.

`Verify.InductiveBinderTranslation` composes these bridges with the existing
raw/peeled/actual stored index typing transport. The uniformity obligation stays
inside the same existential context/level schedule extracted from the actual
header. These are conditional structural-translation theorems, not semantic
soundness of successful source checking, general WHNF normalization, reused
parameter opening or full inductive declarations.

All new structural-translation bridges inherit the existing `TrProj`
admission; annotation argument recovery also inherits the existing typing
uniqueness and Pi-injectivity foundations. These dependencies are audited
separately from the logical-only semantic annotation core. No new admission,
module-owned axiom, native oracle or runtime path is introduced. Native FVar
opening retains the existing `Expr.instantiate1_eq` implementation interface.

`tests/InductiveAnnotationTranslation.lean` adds fifty-three proof controls,
207 audits and five axiom-print checks. Actual optional/auto translations,
nested annotations, metadata barriers, and distinct-but-equivalent universe
expressions exercise extraction without supplying a typed spine. A concrete
plain-Nat header discharges uniformity for its extracted schedule and reaches
raw/peeled/actual stored index typing on the same history; annotated header
receipts retain their uniformity implication. Virtual-name freshness controls
exclude existing and repeated names without claiming native allocation
freshness. Clean-core census remains seventy-three declarations / thirty-eight
theorems with logical-only dependencies; separate bridge census covers
seventy-seven / thirty-four, including private/generated helpers, with pinned
inherited foundation roots and native-instantiation provenance. All three
bridge modules replay through lean4lean. Run
`lake env lean tests/InductiveAnnotationTranslation.lean`.

`Verify.InductiveAnnotationDomainPeeling` removes literal universe uniformity
from semantic domain peeling. `TrExprS.peeledDomain` derives a strict translation
of the actual total peeling result and definitional equality at the input's
requested sort from its actual strict translation and sort typing. It needs
canonical annotation signatures and definition equations, environment
well-formedness and context typing, but no annotation spine or uniform-universe
premise. Constant arity and level translation determine each annotation's own
well-formed universe. Type uniqueness and Pi-domain injectivity recover the
carrier and binary payload typing at that universe; recursion may use a
different literal universe at each nested wrapper. Sorted equality conversion
then returns the result at the caller's requested sort without assuming literal
level equality. Unsupported shapes and metadata barriers remain unchanged.

`TrExprS.peeledDomainHasType` supplies the peeled-domain typing receipt.
`TrExprS.peeledAnonymousBodyTranslation` converts an actual anonymous body to
the peeled binder context with the same peeled witness and definitionally
preserved semantic body. The additive
`BinderRawDomainTranslations.peeledTypingReceipt` and
`OpenedTelescope.peeledTypingReceipt` derive raw, peeled and actual stored index
typing on the existing extracted context/level schedule without a uniformity
implication. Legacy spine APIs and their explicit uniformity premises remain
available; the native index-allocation bridges are not automatically generalized
by these new theorems. The later `Verify.InductiveIndexCheckerClosure` applies them
directly to actual recursor index traces in genuine reached checker models.

The annotation translation fixture adds twenty-four proof controls and
twenty-three runtime controls. All four wrappers support distinct but equivalent
universe expressions. A mixed nested chain cannot satisfy the old uniformity
predicate at any level, yet peels and transports an actual dependent body and
header's stored-domain receipts. Runtime controls check native acceptance,
carrier conversion, malformed arity/universe vectors, ill-typed carriers and
payloads, unsupported shapes, and fresh first-header parameter/index allocation
for both safety flags. Seven new production declarations, including generated
helpers, have exhaustive exact dependency manifests; both additive binder
providers and all twenty-four new proof controls also have exact manifests.
The semantic peeling/body providers retain four inherited dependencies,
including the existing typing/projection/context-conversion admissions; the
opened-telescope provider additionally retains `Expr.instantiate1_eq`. No new
admission, axiom, checker call or runtime behavior is introduced. This removes a
verification-premise restriction, not a kernel discrepancy or the remaining
first-header checker-model construction obligation.

`Verify.InductiveAnnotationContext` converts an actual anonymous body
translation from the raw annotation-domain binder to a definitionally equal
peeled-domain binder, retaining the same peeled witness. The old semantic body
is preserved through `TrExpr`; structural conversion may instead return a new
semantic expression related by definitional equality. A generic fresh-FVar
opening theorem preserves that semantic translation and its supplied
dependency list, without requiring native allocation interfaces.

`Verify.InductiveIndexContextTranslation` connects this conversion to the
actual native index push. Starting `TrLCtx` correspondence and native generator
reservation supply well-formedness and freshness. The next virtual context
uses the exact stored peeled type's `fvarsList`, as required by `TrLCtx`; the
old fresh-only histories' empty dependency lists are not silently reused.
One peeled witness carries the translated stored domain, same-sort semantic
equality, exact pushed native/virtual correspondence, semantically preserved
opened body, declaration position/lookup/name/binder-info/value and operational
reader frame. No literal equality between raw and peeled semantic domains or
between converted structural bodies is asserted.

`Verify.InductiveIndexOpeningTranslation` derives that receipt from an actual
translated `forallE` header rather than a supplied annotation spine. Canonical
constant types and definition equations, the chosen domain sort typing and
syntax-only universe uniformity remain explicit. The `ofIsType` bridge instead
extracts the sort witness from the actual header and retains uniformity as an
implication on that same witness. The actual `withLocalDecl` continuation
receives the receipt for its exact native FVar and pushed reader. This is a
one-step partial-correctness bridge, not repeated telescope transport,
structural translation of arbitrary WHNF results, reuse of existing semantic
binders, or full inductive soundness.

The new context bridges inherit the existing structural translation,
projection and context-conversion foundations. Native push/lookup also retains
the existing instantiation and persistent map/array interfaces. Whole-module
audits keep these dependencies separate from the logical-only annotation core;
no new admission, axiom, oracle, checker path or allocation behavior is added.

`tests/InductiveIndexContextTranslation.lean` adds twenty-five proof controls,
117 audits, six axiom-print checks and sixteen actual allocation callbacks.
Optional FVar domains retain the concrete nonempty carrier dependency while
discarded defaults disappear; metadata barriers retain both original
dependencies. Tests distinguish definitional body preservation from literal
structural equality, and a concrete callback returns the same peeled receipt
with its actual value, reader and opened body. Runtime checks cover four binder
infos, opt/auto/nested/barrier domains, prior local declarations and prior let
values; these allocation experiments do not claim semantic header acceptance.
The clean-core census stays seventy-three declarations / thirty-eight
theorems with logical-only dependencies. The new context census covers
thirteen / ten, including private/generated helpers, with separately pinned
inherited foundations and four existing native interfaces. Runtime helper
audits reject admissions; all three context modules replay through lean4lean.
Run `lake env lean tests/InductiveIndexContextTranslation.lean`.

`Verify.InductiveIndexTraceTranslation` carries the peeled-domain opening
receipt through the same actual `RecursorIndexTrace`, restricted to
`stats.params.size ≤ index`. This excludes reused-parameter steps; index steps
leave that counter unchanged. Each translated node keeps its actual native
reader, pushed virtual context, chosen peeled-domain witness, successful WHNF
result, normalized strong translation and definitional equality to the old
opened-body semantics, together with the translated original tail. It does
not select an independent allocation or semantic history.

Annotation and normalization support are indexed by the supplied actual trace.
Each annotation node requires a compatible existing domain sort witness and
literal universe uniformity, not a supplied typed annotation spine. This is
node-local: distinct valid annotations need not share one semantic universe.
Each normalization node requires structural translation of its exact recorded
WHNF result and definitional equality to the previously opened semantic body.
General WHNF soundness alone is not claimed to recover that strong translation,
nor to make the converted semantic expressions literally equal.

`Verify.InductiveIndexTraceTranslationFacts` derives final native/virtual
correspondence, terminal strong translation, the unchanged index counter and
composed native reader scope from that semantic history. Its allocation suffix
is constructed in the same history induction and retains the initial index
array prefix and every actual final native declaration position. For literal
`SortTelescope` sources, the actual successful WHNF leaves the opened body
unchanged; this discharges normalization support by source equality and
unpacking `TrExpr`. Annotation support remains explicit. Generic reducing
traces are not asserted to form literal `OpenedTelescope` histories.

`Verify.InductiveIndexTraceTranslationCPS` applies transport to the trace
observed by the actual `mkRecInfos.loopArgs1.scopedTrace` continuation, passing
that same history, final correspondence, terminal translation and reader scope
to its caller. The literal-telescope variant discharges only normalization
support. A getter returns the actual index array and observed native reader
with that same receipt. These are index-only partial-correctness bridges, not
reused-parameter semantic correspondence, generic strong-normalization
soundness, source-header acceptance or complete inductive verification.

Whole-module audits retain the inherited structural/projection/context
conversion foundations and existing native instantiation/storage interfaces;
literal-telescope normalization additionally uses the existing instantiation
interface. No new axiom, admission, oracle, global loose-bound-variable-range
dependency, runtime checker path or allocation behavior is introduced.
`tests/InductiveIndexTraceTranslation.lean` checks same-trace projections,
prefix allocations, mixed annotation universes, explicit normalization and
parameter boundaries, native dependencies, actual continuations and module
axiom provenance. Runtime allocation experiments do not establish semantic
header acceptance. A concrete two-index plain-Nat getter instead constructs
the source strong translation and local annotation support from the actual
Nat type lookup, discharging normalization from the literal source telescope.
The fixture covers twenty-seven proof controls, 162 audits and six axiom-print
checks, plus thirty-six actual suffix callbacks with ninety dependent
allocations and a reused-parameter boundary control. The clean annotation-core
census stays seventy-three declarations / thirty-eight theorems; all three
trace modules cover fifty-four / fifteen, including private/generated helpers.
All three trace modules replay through lean4lean. Run
`lake env lean tests/InductiveIndexTraceTranslation.lean`.

`Verify.InductiveRecursorIndexTranslation` lifts those index-only receipts into
the actual per-parent `RecursorInfoIndexSource`. The source's index traversal
always starts at counter zero, so this bridge explicitly requires an empty
parameter array. It does not silently replace that operational counter with
the parameter count. The receipt retains the same entry reader, exact initial
header WHNF result, supplied index trace, chosen semantic/virtual witnesses,
actual index array, major/motive allocation equations and final native reader
scope. Transport destructures the operational source and translates its own
trace, rather than combining independently chosen semantic and allocation
histories.

Starting correspondence and structural translation of that exact normalized
header remain guarded support premises, together with the actual trace's local
annotation and normalization support. Each callback is fixed to the observed
recursor info and continuation reader, and guarded by the complete same source
witness, including major/motive equations and the final native frame. It does
not require correspondence for arbitrary native scope extensions, which can
contain untyped declarations. Nor does it assume the terminal history, terminal
typing or typed annotation spines. Compatible existential source witnesses can
still remain; the callback is conditional starting support, not a proved phase
invariant or uniqueness theorem. Pointwise batch receipts preserve parent
bounds and actual recursor-info array size; native scope extension and minor
updates retain the chosen history.

`Verify.InductiveRecursorIndexTranslationFacts` recovers terminal strong
translation and native/virtual correspondence at the index reader. It derives
the exact index allocation suffix from that same semantic history and retains
its actual declarations and positions through major/motive pushes and the
observed continuation reader. The major domain and native lookup come from the
same per-parent source.

`Verify.InductiveRecursorIndexTranslationCPS` passes these pointwise receipts
through the actual batch continuation, observed-reader getter and registration
wrapper while retaining their operational scope and existing metadata. The
support premise holds only at successful results of the actual observed-reader
capture; the generic continuation is connected to that capture by the existing
`mkRecInfos.morphism`. No uniform semantic-typing premise over arbitrary native
reader extensions is used. The
semantic correspondence is deliberately at each index reader, not asserted at
the final continuation reader: native scope extension alone does not supply
semantic typing for added major, motive or minor declarations. Parameter reuse,
typed correspondence for those additions, generic strong normalization
recovery, source-checker acceptance and full inductive soundness remain open.
No runtime checker behavior or new axiom, admission or oracle is introduced.

`tests/InductiveRecursorIndexTranslation.lean` adds twenty-six proof controls,
142 declaration audits and seven axiom-print checks. A native scope-preserving
metavariable-domain declaration explicitly has no possible `TrLCtx`; this
demonstrates why uniform correspondence over arbitrary native scopes is not a
valid support default. Fixed-source support requires the actual major/motive
and reader guards, and captured support requires actual successful execution.
Eight native callbacks/registrations cover ten parents and eleven indices,
dependent annotation domains, constructor/minor extensions and nonliteral
initial header normalization; these runtime tests do not establish semantic
header acceptance. The old clean annotation core remains seventy-three
declarations / thirty-eight theorems; the three new modules cover thirty-one /
twenty-three, including private/generated helpers, and replay through lean4lean.
Audits pin the four inherited trace-native interfaces separately from
registration's existing `PersistentHashMap.findAux_isSome` foundation and reject
runtime-helper admissions. Run
`lake env lean tests/InductiveRecursorIndexTranslation.lean`.

`Verify.InductiveIndexApplicationTranslation` carries an actual accumulated
head application through the supplied translated index history. The initial
strong application translation and its typing at the same initial header are
explicit; final application typing is derived, not assumed. Each fresh index
weakens the previous semantic application, translates the actual native FVar
as `bvar 0`, and converts its type using that opening's same raw-to-peeled
domain equality. Lifting the Pi body and substituting that variable recovers
the old body semantics. The recorded node's normalization equality then
converts application typing to its exact normalized semantic type. The final
native expression is `mkAppN head finalIndices`, retaining any initial prefix,
with no independently selected history or literal semantic-body equality.

`Verify.InductiveMajorContextTranslation` specializes this transport to the
actual parameter-free recursor major application. The same source/history
guards supply starting datatype-head translation/typing, exact terminal-sort
equality and universe uniformity for this actual raw major expression. Those
are conditional support obligations, not assumptions of final application
typing or an already typed major reader. Canonical annotation constants and
definitions recover the raw major's typed annotation spine and its peeled
semantic domain. One witness retains raw/peeled translations, same-sort
equality, both typings, exact native dependency lists, positioned declaration
and semantic correspondence at the actual pushed major reader. Recognized
annotation heads are handled by the existing generic consumer, not a special
datatype-name path or a claim that peeling always leaves the major unchanged.

`Verify.InductiveMajorContextTranslationCPS` derives constant-head translation
and initial typing from the actual lookup, mapped universe arguments and
arity, retaining explicit definitional alignment of the stored constant type
with the same normalized header. Its constant-application bridge derives the
final application from those facts and the same history. The actual
`withLocalDecl` continuation receives exact pushed-major correspondence;
batch getter/CPS receipts retain the same per-parent histories and require
support only on successful actual observed-reader captures. Empty parameters,
terminal-sort equality, raw-major annotation uniformity and recorded
normalization remain explicit. This is not semantic correspondence at the
motive/current reader, motive or minor typing, source-checker acceptance,
registered-recursion soundness or complete inductive verification.

The application proofs retain inherited projection-weakening and typing
uniqueness/conversion foundations. Native major pushes retain existing
persistent-container interfaces; annotation recovery also retains the prior
structural/context foundations. Audits keep those dependencies separate from
the logical-only annotation core. No new admission, axiom, oracle, checker
path, allocation behavior, cache or fast path is introduced.

`tests/InductiveMajorContextTranslation.lean` adds thirty-four proof controls,
150 audits and nine axiom-print checks. It checks exact prefix application,
semantic lifting, same recorded normalization, constant/header alignment,
local major annotation uniformity, successful-result-only support and the
actual pushed-major correspondence. Eighteen allocation-only opening callbacks
and three actual parent callbacks cover dependent/metadata/nonuniform domains,
annotation-name heads, stored dependency/value retention and separation of
major readers from motive/current readers. Nonempty-parameter runtime controls
do not claim semantic major support. The new census is twenty-six declarations /
sixteen theorems, including private/generated helpers; the old clean core stays
seventy-three / thirty-eight. Audits pin projection weakening and typing
conversion provenance, reject runtime admissions and forbidden global-range
dependencies, and keep native-interface boundaries separate. All three modules
replay through lean4lean. Run
`lake env lean tests/InductiveMajorContextTranslation.lean`.

`Verify.InductiveMotiveBindingFacts` extends an explicitly supplied initial
mixed context along the same translated index history. Every appended model
declaration retains the actual fresh FVar, binder metadata, peeled native type
and its exact semantic domain. The receipt records the selected identifiers,
their reverse abstraction order, the dropped initial context and the same
suffix weakening. The major extension uses that history's existing typed
major opening. Its native binding equation proves that the actual nested
`mkForall indices (mkForall #[major] (.sort elimLevel))`, including native
annotation peeling, is precisely the combined index-plus-major model
abstraction. Lookup congruence handles the major declaration left in the
reader while indices are selected; no independently chosen telescope or
assumed native/model abstraction equality is supplied.

`Verify.InductiveMotiveContextTranslation` types that exact motive domain.
The elimination level must map under the actual universe-name list. Generic
mixed-context abstraction first translates and types the domain at the
initial context, then weakens both back across the very same index-plus-major
suffix. The semantic result includes that lift; simply reusing the initial
semantic expression at the major reader would be incorrect. Final motive
typing is derived, not a support premise.

`Verify.InductiveMotiveContextTranslationCPS` opens this typed domain at the
actual pushed-major reader. It preserves the motive declaration's exact
native `fvarsList` dependencies, fresh identifier, binder position, semantic
domain and pushed-reader `TrLCtx`. Per-parent and batch receipts retain all
prior header, normalization, index-history and typed-major witnesses, and
project back to the original major sources. Getter support is required only
at successful actual observed-reader capture results; the generic CPS bridge
resumes through the existing morphism. Its new support obligation supplies
only a well-formed initial mixed context with exact native/virtual alignment,
under the complete same-source guards. Representability of arbitrary initial
native contexts is not silently assumed or asserted as a phase invariant.

The empty-parameter parent boundary and prior constant/header alignment,
terminal-sort, normalization and actual-major annotation obligations remain
explicit. Motive-reader correspondence is proved, but correspondence at a
later parent/minor/current continuation reader is not. Discharging actual
phase support, parameter reuse, minor typing, general strong normalization
and full inductive verification remain separate. This transport inherits the
existing mixed-context abstraction/context foundations and native expression
abstraction and persistent-container interfaces; audits keep these separate
from the clean logical-only annotation core. No new admission, axiom, oracle,
runtime checker change, allocation behavior, cache or fast path is introduced.

`tests/InductiveMotiveContextTranslation.lean` adds thirty-one proof controls,
181 axiom audits and eleven axiom prints. The tests cover exact native/model
abstraction, mapped elimination levels, same-history typing, exact stored
motive dependencies and reader position, successful-result-local model
support, getter/CPS transport and source projections. A metavariable-domain
countercontrol shows why arbitrary native scope cannot supply a typed initial
mixed context. Fifteen allocation-only motive callbacks and three actual
parent cross-checks cover selected binder order and prefixes, dependent and
metadata/nonuniform domains, external base dependencies, retained declaration
values, major/motive reader separation and used/unused native-let boundaries.
They do not claim semantic header acceptance. The new whole-module census is
fifty-seven declarations / thirty-two theorems, including private/generated
helpers (binding facts 34/21, domain translation 3/2, CPS 20/9). The old clean
logical core stays seventy-three / thirty-eight. Audits pin inherited
abstraction/context foundations and eight existing native interfaces, reject
module-owned axioms and runtime admissions, and forbid the global native
loose-bound-variable-range axiom. All three modules replay through lean4lean.
Run `lake env lean tests/InductiveMotiveContextTranslation.lean`.

`Verify.InductiveParentPassTrace` records the actual first recursor parent
pass, `mkRecInfos.loopInd1`, separately from the later minor pass. Each step
retains the successful initial header normalization, exact native index
trace, actual appended `RecInfo` with empty minors, and its exact pushed-motive
reader. The stop preserves the original prefix/reader. Scope, count and prefix
receipts preserve old infos and record empty minors only for newly appended
parents. The getter captures the actual parent-phase endpoint; its morphism
exposes the existing CPS law, not a modeled or rerun native computation.

`Verify.InductiveParentContextTranslation` extends the mixed context through
one parent. It extracts the index model from the supplied translated history
once, derives the actual typed major and motive openings, then builds the
exact motive model using its stored native domain and dependencies. The
receipt retains both openings, final model WF/native/virtual alignment and
one shared extension whose allocated identifiers are precisely the actual
index suffix, major and motive. A later base model or final motive typing is
not a premise.

`Verify.InductiveParentContextTranslationCPS` threads that model through the
entire actual parent-pass trace. The initial WF model/native alignment is
supplied once; each derived endpoint is the next parent's starting model.
The typed trace retains the same native pass, normalized index history and
single-parent receipt at every node. Extension composition follows those
exact model terms, and the final WF model yields `TrLCtx` at the actual parent
reader. It discharges the repeated per-parent mixed-context representation
obligation rather than independently selecting representations or allocation
histories. Existing normalized-header, index annotation/normalization,
head/header typing, terminal-sort and raw-major universe support remain
explicit, conditional on WF models of each actual trace node's fixed native
reader. These are not claimed as discharged phase invariants.

Getter support is consumed only at successful actual `loopInd1` capture
results and their exact trace endpoints. The scoped CPS theorem receives the
typed parent-phase reader. `mkRecInfos.fromTypedParentPass` reconnects this
receipt to the actual checker: proving the later `loopInd2` minor continuation
is an explicit remaining obligation. Correspondence at its eventual current
reader is not claimed. Empty parameters and actual elimination-level mapping
remain explicit; the initial native context's typed mixed representation,
general normalization, minor typing, parameter reuse and full inductive
verification remain separate. The native trace/morphism are logical-only;
native scope/getter depend on the existing persistent-container interfaces,
and typed transport retains the previous abstraction/context foundations.
No new admission, axiom, oracle, runtime checker change, cache or fast path is
introduced.

`tests/InductiveParentContextTranslation.lean` adds twenty-eight proof
controls, 192 axiom audits and nine axiom prints. It checks whole-pass trace
shape, exact model extension and reader correspondence, same-node index
support, success-local getter/CPS transport and the explicit minor-phase
obligation. Twelve allocation-only actual `loopInd1` captures cover zero,
one and multiple parents, retained info prefixes, nonzero starting counters,
dependent/metadata/alias/base-dependent headers and retained declaration
values. One checked recursive parent/minor boundary compares the actual
parent-only capture with full `mkRecInfos` and checks additional native minor
allocations, without claiming semantic minor correctness. The new census is
sixty-five declarations / twenty-eight theorems, including private/generated
helpers (native trace 22/10, parent model 10/8, typed CPS 33/10). The old clean
logical core stays seventy-three / thirty-eight. Native-module audits allow
only logical axioms and three existing container interfaces, with trace,
counts, prefix and morphism pinned logical-only; typed transport keeps its
inherited abstraction/context boundaries separate. Audits reject new
module-owned axioms, runtime admissions and the global native bound-variable
range axiom. All three modules replay through lean4lean. Run
`lake env lean tests/InductiveParentContextTranslation.lean`.

`Verify.InductiveCtorFieldTrace` records the actual `mkRecInfos.loopCtorArgs`
constructor-field traversal. Parameter nodes retain the actual array lookup;
field nodes retain the fresh declaration, its peeled stored domain, and the
actual `isRecArg` result obtained in that pushed reader. Tails instantiate the
raw constructor body without adding normalization. Trace receipts derive the
exact allocation order and field suffix, native scope and declarations, the
ordered recursive-field subsequence, and a syntactically non-forall terminal.
The getter and CPS morphism refer to the actual computation, not a separately
modeled or replayed traversal. Recursive selection is an operational receipt,
not a proof of semantic recursive-argument classification.

`Verify.InductiveCtorFieldTranslation` opens those same fields semantically.
Domain annotation support remains explicit. Peeling converts the anonymous
body context, retaining a strong translation of the converted body and its
definitional equality to the original; fresh-variable instantiation then
opens that body without a normalization premise. The translated history
constructs the exact mixed-context suffix from one initial WF model, including
the stored native dependency lists, and preserves its actual selected order.
Parameter reuse is represented natively but remains excluded from this typed
transport. Constructor-header translation and phase invariants remain premises.

The shared mixed-context extension also abstracts an arbitrary translated,
typed body using the exact native field selection. Its semantic abstraction
first lives in the initial context; transport back to the field reader uses
the same extension and the required semantic lifting. Body typing is not
inferred from native scope or operational recursive classification.

`Verify.InductiveCtorFieldTranslationCPS` packages the same native history,
semantic history and derived final model in one endpoint receipt. Getter
annotation support is consumed only at successful actual captures. Its scoped
callback receives that exact field reader, not an assumed independently
chosen later model. Endpoint projections derive final reader correspondence,
terminal translation and typed native field abstraction. An initial WF
mixed-context representation is supplied once; a final one is constructed.
These APIs can consume the previously typed parent reader but do not yet
verify `loopUArgs`, recursive-hypothesis domains, motive/constructor application
alignment, minor-domain opening, or correspondence at the eventual minor/current
reader. Those intervening obligations remain explicit. No new admission,
axiom, oracle, runtime checker change, cache or fast path is introduced; the
transport inherits the existing abstraction/context foundations and native
container/expression interfaces, separate from the clean logical-only core.

`tests/InductiveCtorFieldTranslation.lean` adds twenty-seven proof controls,
214 axiom audits and ten axiom prints. Fifteen successful native captures cover
dependent, nonrecursive, recursive and higher-order fields, two datatype heads,
annotations and metadata, parameter reuse, raw alias/metadata/let terminals,
retained declarations, and exact identifiers, domains, dependencies and order.
Five failure controls cover constructor/classifier fuel exhaustion, actual
WHNF failure and callback error propagation. A concrete initial-local semantic
reference shows why transport back across the field suffix is not identity
weakening. Runtime captures check operational allocation/selection behavior,
not semantic recursive classification or minor-domain correctness.
The new whole-module census is ninety-four declarations / forty-four theorems,
including private/generated helpers (trace 36/18, translation 51/20, CPS 7/6).
The old clean logical core remains seventy-three / thirty-eight. Audits pin
inherited admissions and native interfaces separately, reject new module-owned
axioms and runtime admissions, and forbid the global native bound-variable
range axiom. All three new modules replay through lean4lean. Run
`lake env lean tests/InductiveCtorFieldTranslation.lean`.

`Verify.InductiveUArgTrace` captures the actual `mkRecInfos.loopUArgs`
higher-order recursive-argument opening. Its receipt retains the successful
inference of the supplied argument, initial WHNF of that inferred type, and
the exact subsequent telescope opening with per-body WHNF in each pushed
reader. A parameter-free adapter reuses `RecursorIndexTrace` without changing
the runtime computation or independently rerunning an index loop. This
adapter does not restrict the original inductive declaration's parameters:
`loopUArgs` has no parameter-skipping phase. The getter and scoped CPS expose
the actual terminal, ordered temporary arguments, reader and scope; the
morphism preserves inference, normalization and callback error behavior.

`Verify.InductiveUArgTranslation` connects that same receipt to the existing
normalized telescope translation. Source support explicitly supplies semantic
correspondence for the actual inferred/normalized type and the initial
argument, while annotation and body-normalization support remain indexed by
the exact native trace. The translated history derives reader correspondence
and the fully applied recursive argument's type along those same openings.
It constructs the temporary argument model and exact selected identifiers
from one initial WF/native-aligned mixed model. No independently assumed
final model or final reader correspondence is supplied.

Arbitrary-body abstraction over those temporary arguments returns its typed
semantic result to the initial reader, preserving earlier constructor fields
and parent/motive locals. Transport back to the temporary argument reader
uses semantic lifting across that same suffix rather than identity weakening.
This is the boundary needed to return a recursive-hypothesis domain outside
the scoped temporary arguments; its eventual motive application remains an
explicit translated/typed-body obligation, not a consequence of native scope.

`Verify.InductiveUArgTranslationCPS` packages the native opening, translated
history and derived model as one endpoint. Success-local support is consumed
only at actual `loopUArgs` captures; the callback receives that exact temporary
reader and may derive a typed native abstraction in the initial model's
context. Actual inference/WHNF semantic support, motive application,
`getIIndices` alignment, constructor/head alignment, recursive-hypothesis
allocation, minor-domain opening and eventual minor/current-reader
correspondence remain separate obligations. Inherited foundations and native
interfaces remain explicitly audited. No new admission, axiom, oracle,
runtime checker change, cache or fast path is introduced.

`tests/InductiveUArgTranslation.lean` adds thirty proof controls, 176 axiom
audits, ten axiom prints and eight native-interface provenance pins. Sixteen
successful native captures cover actual inference, initial/body WHNF,
dependent argument identifiers/domains/dependencies/order, aliases, metadata
and annotations, retained locals/lets, and discarding temporary arguments on
return to the base reader. A constructor-parameter reuse case connects actual
`loopCtorArgs` and `loopUArgs` without imposing an original-parameter bound.
Eight failure controls cover inference, normalization, fuel and callbacks.
Formal controls preserve the shared native terminal semantic when typing the
fully applied argument and conclude body-abstraction typing explicitly in the
initial model's context. An external-initial-local countercontrol distinguishes
semantic lifting from identity weakening. Native base-reader inferability and
scope checks do not establish generated motive/IH/minor correctness.
The new whole-module census is fifty-one declarations / twenty-nine theorems,
including private/generated helpers (trace 23/13, semantic transport 21/10,
CPS 7/6); the old clean logical core stays seventy-three / thirty-eight.
Audits pin inherited admissions/interfaces separately, reject new module-owned
axioms and runtime admissions, and explicitly forbid the global native
bound-variable-range axiom even if accidentally whitelisted. All three
modules replay through lean4lean. Run
`lake env lean tests/InductiveUArgTranslation.lean`.

`Verify.InductiveIHTrace` records the actual `mkRecInfos.loopU` recursive-
hypothesis pass. Each node retains the successful `loopUArgs` opening and the
exact temporary-reader abstraction of the selected motive applied to native
indices and the fully applied recursive field. IH names come from the stored
field metadata. Allocation occurs after the temporary reader has been
discarded, with the original reader's generator and annotation-peeled domain.
The trace proves ordered allocation, seeded-prefix preservation, persistent
allocation counts and structural reader scope, without asserting domain typing
or valid parent/head alignment from `getIIndices` or array defaulting.

`Verify.InductiveIHTranslation` derives actual motive-body typing from the
same UArg endpoint's application typing and explicit selected-motive arrow
support. It abstracts precisely those temporary arguments, obtaining strong
raw IH-domain translation and typehood in the initial constructor-field model.
Canonical annotation conversion and explicit annotation-universe support then
derive the stored domain and its exact pushed reader. The mixed model adds one
IH to that restored initial model, never to the discarded argument model.
Temporary argument IDs may legitimately be reused as IH IDs; only persistent
IH declarations and generator steps survive.

`Verify.InductiveIHTranslationCPS` retains the native source witness, its exact
UArg endpoint, derived IH opening and constructed model in each typed step.
The whole history threads those same models through the actual IH chronology;
its composed extension contains only the ordered IH suffix. Successful-result-
local support supplies inference/normalization translation, motive application
typing and annotation compatibility at that exact source. Neither whole IH-
domain typehood nor an independently aligned final model is a support premise.
Getter and scoped CPS reach the actual IH-pass endpoint before minor allocation.

With an empty initial hypothesis array, typed arbitrary-body abstraction over
the derived IH suffix returns to the initial constructor-field model, retaining
earlier fields and parent/motive locals. This is a minor-facing abstraction
boundary, not verification of the actual minor body or domain. Deriving the
source and selected-motive support from the checked parent/field histories,
constructor application typing, head/index alignment, outer field abstraction
and eventual minor/current-reader correspondence remain separate obligations.
Inherited foundations and existing native interfaces remain explicitly audited;
no new admission, axiom, oracle, runtime change, cache or fast path is introduced.

`tests/InductiveIHTranslation.lean` adds thirty proof controls, 214 declaration
audits, twelve axiom prints and eight existing native-interface provenance pins.
Eighteen successful whole-loop captures, one allocation-only untyped-motive
countercontrol and seven failure controls check actual IH IDs, names, domains,
dependencies and order; restoration and reuse of temporary IDs; retained
locals, fields, parameters and indices; seeded and skipped-prefix behavior;
and inference/normalization/fuel/callback failures. An allocation-only
untyped-motive countercontrol distinguishes native scope from semantic typing.
Formal controls expose actual body/domain typing, restored-reader allocation,
same-history model threading and abstraction back to the field model. Strict
whole-module audits reject new module-owned axioms and runtime admissions and
forbid the global native bound-variable-range axiom even if whitelisted.
The new whole-module census is eighty-eight declarations / thirty-nine theorems,
including private/generated helpers (native trace 31/14, semantic transport
22/14, CPS 35/11); the old clean logical core stays seventy-three / thirty-eight.
All three modules replay through lean4lean. Run
`lake env lean tests/InductiveIHTranslation.lean`.

`Verify.InductiveMinorTrace` captures the actual `mkRecInfos.loopCtors`
constructor/minor pass. Each source retains the exact constructor-field trace,
recursive-hypothesis trace, IH-reader endpoint and nested native abstraction.
Minor allocation uses that same current IH reader, then performs the actual
selected-parent record update before the recursive constructor tail. Earlier
constructor fields, IHs and minors remain in that tail reader; only the internal
UArg scopes were temporary. Getter and scoped traces preserve native errors and
defaulting. Record-prefix/count claims require a valid selected-parent index;
scope and record-size preservation do not assert semantic typing or alignment.

`Verify.InductiveMinorTranslation` derives constructor application typing through
the same translated constructor-field history, converting peeled argument
domains and annotation-adjusted bodies rather than assuming a fully applied
constructor type. Explicit constructor-head/header typing and selected-motive
arrow support then derive actual motive-body typing against the same translated
native terminal. After weakening into the actual IH model, it abstracts IHs
and then fields, obtaining strong raw minor-domain translation/typehood in the
initial constructor model.

The native outer field abstraction occurs at the later IH reader, not at that
initial model or the field reader. A selected-binding congruence proof uses exact
preserved declaration lookups, selected-ID membership/nodup, binding scope and
translated-body closure to reconcile those expressions. The resulting base
semantic type is then lifted across the same combined field+IH suffix back to
the actual IH model. Canonical annotation conversion and explicit annotation
support derive the stored minor domain and its allocation there. Neither reader
identity nor identity weakening replaces these lookup/lifting obligations.

`Verify.InductiveMinorTranslationCPS` retains each native source witness, derived
field endpoint, IH history, minor opening and exactly constructed allocation
model. Its whole-pass history derives every later model and the actual final
reader correspondence from one initial WF/native-aligned model. The composed
extension contains all persistent fields, IHs and minors in native chronology.
Successful-result-local support supplies actual constructor-head/header
alignment, source/annotation translation, selected-motive typing and IH support;
whole minor-body/domain typehood and independently aligned final models are not
premises. Typed transport currently requires `stats.params.size = 0`, a real
original-parameter restriction inherited from field transport, not the
parameter-free UArg proof adapter. Native traces remain unrestricted.

This verifies conditional domain typing and current-reader correspondence for
the actual supported constructor/minor pass, not complete recursor soundness.
Deriving support from the checked declarations, transporting nonzero constructor
parameters, validating parent/head/index alignment and verifying recursor
types/rules remain separate.
Inherited foundations and native interfaces remain explicitly audited. No new
admission, axiom, oracle, runtime checker change, cache or fast path is introduced.

`tests/InductiveMinorTranslation.lean` adds thirty proof controls, 222 declaration
audits, twelve axiom prints and eight existing native-interface provenance pins.
Fourteen successful whole-loop captures, two allocation-only untyped controls
and five failure controls check actual constructor/minor allocation,
record updates, nested abstraction and retained-reader chronology, including
dependent and higher-order fields, parameters/indices, multiple constructors,
seeded prefixes, operational defaulting and failure controls. Formal controls
expose same-terminal constructor application, selected-binding congruence,
base/current semantic lifting, exact minor allocation and whole-pass model
threading. Strict module audits pin inherited foundations/interfaces separately
and forbid the global native bound-variable-range axiom even if whitelisted.
Positive minor domains pass full native `TypeChecker.checkType`, not inference
alone. The new whole-module census is ninety-five declarations / forty-six
theorems, including private/generated helpers (native trace 32/14, semantic
transport 28/21, CPS 35/11); the old clean core stays seventy-three / thirty-eight.
All three modules replay through lean4lean. Run
`lake env lean tests/InductiveMinorTranslation.lean`.

`Verify.InductiveMinorPassTrace` captures the actual `mkRecInfos.loopInd2`
parent traversal. Each step records the selected parent's complete constructor
trace and passes its exact resulting records and current reader to the next
parent. The stop case uses the native parent bound, including an initial parent
already beyond the type array. Scope and record-size preservation concern the
actual native history, not a separately reconstructed final context. Earlier
constructor fields, IHs and minors remain present across parent boundaries.
Selected-record prefix/count facts retain explicit type/record bounds;
records before the starting parent or beyond the type array remain unchanged.

`Verify.InductiveMinorPassTranslationCPS` translates that same complete history
from one initial well-formed, native-aligned mixed model. Every constructor pass
derives the model used by the following parent; final well-formedness, native
correspondence and an ordered model extension follow from the history rather
than appearing as independent premises. Getter and arbitrary-continuation
contracts retain the native traces and propagate native failures. The full
getter also pairs `RecursorInfoCounts` with the same successful native result;
these size/count facts do not establish head or index alignment.

The full `mkRecInfos` contracts compose the actual typed `loopInd1` parent pass
with this typed `loopInd2` history. The final model of parent construction is
exactly the initial model of minor construction, not a freshly assumed model
aligned with the same reader. This accounts for the allocation chronology of
indices, majors and motives, followed by constructor fields, IHs and minors
across every parent. Outer reader restoration does not discard declarations
inside the recursor-building continuation.

These are conditional allocation/domain-typing and reader-correspondence
contracts, not complete recursor soundness. Parent and minor source support
still supplies the head/header and terminal/index alignment, normalization,
annotation, selected-motive and IH obligations of the component passes. Typed
transport retains the genuine zero-original-parameter restriction; native
traces and operational tests are not restricted to that fragment. Checked-source
provenance, deriving support from checked inductive declarations, transporting
nonzero parameters and verifying complete recursor types/rules remain separate
obligations.
No runtime checker, cache, fast path, axiom or admission is added.

`tests/InductiveMinorPassTranslation.lean` adds twenty-four proof controls,
185 declaration audits, twelve axiom prints and eight existing native-interface
provenance pins. Sixteen successful `loopInd2` captures and eight composed
`mkRecInfos` captures check exact records, allocation order, prior-parent local
retention and outer-reader restoration. Thirty-one minor domains and twenty
parent/index/major/motive domains pass full native `TypeChecker.checkType`.
Cases include genuine mutual/cross-parent recursion, dependent/higher-order
fields, multiple IHs, indexed and original-parameter native families, seeded
prefixes and oversized records, empty/end/beyond-end starts and skipped invalid
sources. Two allocation-only untyped controls and seven failure controls remain
operational boundaries, not typing claims or kernel discrepancies.

Strict whole-module audits forbid module-owned axioms and the global native
bound-variable-range axiom, even if whitelisted. Inherited foundations/interfaces
are pinned separately. The new census is sixty-three declarations / twenty-nine
theorems, including private/generated helpers (native trace 28/17, semantic/CPS
35/12); the old clean core stays seventy-three / thirty-eight. Both modules replay
through lean4lean. Run `lake env lean tests/InductiveMinorPassTranslation.lean`.

`Verify.InductiveRecursorTypeNative` identifies the actual recursor body,
selected binder arrays and nested raw type used by `declareRecursors`.
The stored metadata type is exactly that raw type's `inferImplicit 1000 false`.
Flattening the parameter/motive/minor/index/major groups is proved from native
binding folds, selected cdecl lookups, distinctness and binding scope; it is not
an assumed equality in semantic support. Selected-binding congruence preserves
the original identifiers, names, domains and binder information while allowing
different physical indices and declaration kinds. This accounts for sparse or
reordered selections without pretending that the full reader contains only the
selected declarations.

`Verify.InductiveRecursorTypeTranslation` constructs a selected telescope from
one initial mixed model. Every step requires an actual full-reader cdecl lookup,
freshness and translation/typehood of that original domain in the preceding
constructed model. Projected well-formedness, extension, distinctness and native
binding agreement are derived from this history, not independently supplied.
Component support types the major and the already index-applied motive at the
same projected model with their arrow aligned, deriving the actual body
application and then typed abstraction back to the initial model. No support
premise asserts whole-body or whole-raw-type typehood. This earlier interface
keeps the selected array and projected-domain/body-component support explicit.
The stronger actual-source adapter below derives the body-component obligations;
deriving selected-domain support from checked declarations remains open.

The actual complete `RecursorInfoModelEndpoint` supplies the full reader's
binding scope and ordered model extension. Translation/typehood at its final
model uses the genuine semantic lift by `final.length - initial.length`, which
is derived from that complete extension, including residual constructor
fields/IHs/minors and other-parent declarations. Neither the selected-binder
count nor identity weakening replaces the actual allocation chronology.
The complete-construction adapters retain the zero-original-parameter
restriction of the preceding typed parent/minor passes.

`Verify.InductiveRecursorImplicitTranslation` proves strong and ordinary
translation preservation for the actual `Expr.inferImplicit` definition, for
every count and both range policies. Its binder annotations do not change the
semantic expression, and traversal respects the native non-forall barriers.
These theorems inherit `sorryAx` through the existing `TrExprS`/`TrProj`
foundation; they are not admission-free foundations. No new admission is added.

`Verify.InductiveRecursorTypeTranslationCPS` pairs the raw and inferred-stored
types with the same semantic type at the initial model and the genuinely lifted
type at the actual final model. Receipt facts derive raw/stored loose-bound
variable closure and restrict their free variables to the initial model;
metadata receipts refer to the actual `declareRecursors.metadataVal` type.
Getter and arbitrary-continuation contracts use the same successful full
`mkRecInfos` construction endpoint and return type receipts for every bounded
parent. Support is local to that successful result and endpoint, not an
independently aligned final context. An initial model may still contain base
locals, so these facts do not establish globally closed declarations without
empty-base and universe alignment. Recursor rules, safe registration,
checked-source support derivation, nonzero-parameter semantic transport and
complete inductive soundness remain separate obligations. No runtime checker,
cache, fast path, axiom or admission is added.

`tests/InductiveRecursorTypeTranslation.lean` adds twenty-four proof controls,
200 declaration audits, twelve axiom prints and eight existing native-interface
provenance pins. Seven actual full construction captures and nine selected-parent
checks rebuild sparse/reordered projections from the actual domains, checking
each copied domain and the raw selected body/base/final/stored types with full
native `TypeChecker.checkType`. Cases include mutual and indexed/dependent
families, a seeded local/let base, residual fields/IHs and other-parent locals,
and original-parameter native controls that do not extend the typed fragment.
Twenty-one invalid forward-order/omitted-major/duplicate-ID projection controls,
one allocation-only untyped field and three propagated failures remain explicit
boundaries. Implicit-inference controls cover zero/limited/full counts, both
range policies and metadata/non-forall barriers. Strict whole-module audits
forbid module-owned axioms and the global native bound-variable-range axiom,
even if whitelisted, while separately pinning inherited foundations/interfaces.
The new census is eighty-one declarations / fifty-seven theorems, including
private/generated helpers (native 41/32, implicit 2/2, semantic 31/17, CPS 7/6);
the old clean core stays seventy-three / thirty-eight. All four new modules
replay through lean4lean. Run
`lake env lean tests/InductiveRecursorTypeTranslation.lean`.

`Verify.InductiveRecursorApplicationFacts` proves that abstracting a free variable
and instantiating it back cancels, including under arbitrary pre-existing bound
variables and at every depth. It also identifies the first forall of an actual
selected native cdecl telescope. No global native bound-variable-range axiom is
used. `Verify.InductiveRecursorApplicationNative` recovers the actual motive's
cdecl lookup from `RecursorInfoIndexSource` at the current reader. Its stored
domain is proved equal to that reader's nested abstraction of the same original
indices and major over the elimination sort. Original allocation provenance,
lookup preservation, selected binding congruence and distinctness derive this
equality; it is not an assumed motive-domain alignment.

`Verify.InductiveRecursorApplicationTranslation` derives local/domain translation
and local typing from an actual cdecl lookup in a well-formed mixed model. Its
generic application theorem consumes a typed head and translation of its actual
native selected-forall domain, then applies the head to those same original
locals. Each argument's domain is recovered from the model and aligned with the
translated forall using semantic definitional equality. Instantiation cancels
native abstraction rather than relying on physical-to-projected semantic
identity. Terminal typing and terminal native-type translation are derived;
no premise supplies the already-applied head's typing. Partial motive
application leaves the actual major-to-sort arrow, and the major's lookup
derives its matching typing. A selected telescope plus the actual source
therefore derives the earlier body-application support.

`Verify.InductiveRecursorApplicationTranslationCPS` reduces recursor type support
to the selected array and a telescope built from actual original domain lookups,
freshness and per-step translation/typehood. The getter recovers native index
sources from the same successful `mkRecInfos` result used by the typed complete
parent/minor endpoint; it does not assume an independently aligned source or
final model. Actual motive provenance and the constructed projection discharge
major/applied-motive alignment for every bounded parent. Raw and inferred-stored
type receipts still refer to the same initial model and the genuinely lifted
full construction suffix. Arbitrary continuations receive the same receipts.
The full typed adapters retain zero original parameters; indexed and mutual
cases are not replaced by a special zero-index path.

This strengthens the conditional recursor-type result, not complete inductive
soundness. Selected-array/domain support, checked-source provenance for the
semantic component passes, nonzero-parameter transport, empty-base/universe
alignment, recursor rules and safe registration remain open. Semantic uniqueness,
instantiation and translation foundations retain their existing inherited
admissions, separately audited; no new runtime code, axiom or admission is added.

`tests/InductiveRecursorApplicationTranslation.lean` adds cancellation controls
under arbitrary pre-existing bound-variable depths, ordered original-fvar array
controls, seven complete `mkRecInfos` captures and nine selected-parent
applications. It checks actual motive/major/index cdecl lookups, exact nested
motive domains, each instantiated argument domain, the partial major arrow and
the complete application sort, including seeded local/let bases, mutual and
indexed/dependent families, retained other-parent fields/IHs/minors, original-
parameter native-only controls and an allocation-only untyped boundary.
Omitted-major, duplicate-major, reordered-dependent, duplicate-index and
cross-parent applications are rejected. Every declaration in the four application
modules, including private/generated helpers, receives a transitive dependency
audit; no module-owned axiom is allowed. Facts/native exclude `sorryAx`, and
semantic/CPS modules explicitly allow existing inherited admissions. The clean
annotation/binder core and all fixture proof/runtime/audit helpers are checked
with their respective policies, excluding runtime admissions. Seven existing
translation/abstraction foundations have exact dependency-set and module-origin
pins; all eight allowed native interfaces must remain axioms from
`Lean4Lean.Verify.Axioms`. Eight negative audit controls exercise forbidden range
even when whitelisted, excluded admissions/interfaces, absent declarations/modules,
wrong existing foundation origin, whole-module transitive policy enforcement and
exact foundation dependency-set enforcement. `Expr.looseBVarRange_eq` is forbidden
under every policy. The inherited `sorryAx` allowance is not proof that semantic
foundations are admission-free or that new local admissions could be distinguished
from existing inherited ones; the unchanged source-admission census remains a
separate guard.
The application census is 46 declarations / 42 theorems (facts 8/7, native
18/17, translation 15/14, CPS 5/4), with no new admission. Run
`lake env lean tests/InductiveRecursorApplicationTranslation.lean`.

`Verify.InductiveIndexSelectedTranslation` derives the chronological index
block's selected telescope from the same actual translated native history.
`IndexMLCtxExtension.selectedTelescope` converts a chronological mixed-context
extension and its final well-formedness into selected-binder evidence, using
each actual prefix's freshness, stored-domain translation and typehood. It
retains exact native declaration identifiers, physical indices, names, peeled
domains, binder information and default declaration kinds. The initial model's
well-formedness follows by dropping the actual extension, rather than from an
independent projected-context premise.

`TranslatedRecursorIndexTrace.selectedTelescope` derives both the extension and
final well-formedness through the existing same-history `mixedContext` bridge.
Its inputs remain the actual translated history, initial model well-formedness,
exact native/virtual context matching and name-generator reservation; it does
not assume the desired selected telescope or an independently well-formed final
model. The returned index array keeps its original prefix and appends exactly
the selected newly allocated identifiers in chronological order. Stored peeled
domains and their semantic translations come from that history's annotation
opening receipts, not from syntactic identification with raw domains.

`SelectedRecursorTelescope.monoFull` transports only selected native lookup
evidence. `selectedTelescopeAt` uses a later actual scope frame to retain these
lookups while keeping the same chronological endpoint model and virtual
context. It does not extend that semantic model, perform identity weakening,
lift a body to the later reader, or move binders into recursor-selected order.
Parameters may already be present in the initial model of an index-only suffix;
this does not translate a reused-parameter prefix. Motives/minors-before-indices
reordering, whole `RecursorSelectedDomainSupport`, source-header acceptance,
general strong-normalization support, nonzero-parameter complete transport,
empty-base/universe alignment and rule/registration soundness remain separate.
Existing translation foundations retain their inherited admissions; no new
axiom, admission, runtime path, cache or native loose-bound-variable-range
dependency is introduced.
The whole-module census is nine declarations / eight theorems, including
private/generated helpers. Beyond standard logical axioms and the inherited
`sorryAx`, it uses only the three existing allocation/storage interfaces
`PersistentArray.toList'_push`, `PersistentHashMap.WF.find?_eq` and
`PersistentHashMap.WF.toList'_insert`. Even lookup-only `monoFull` inherits the
admission through the existing selected-telescope/translation types; it is not
an admission-free foundation.

`tests/InductiveIndexSelectedTranslation.lean` adds seven proof controls, twenty
native chronological captures and thirty-two fresh cdecl checks. These cover
dependent/indexed domains, annotation/default peeling, stored dependencies,
seeded local/let bases and empty/nonempty/duplicate preserved index prefixes.
The native duplicate-prefix controls do not supply semantic selected-domain
support. Exhaustive module/helper dependency audits retain three inherited
foundation provenance/admission pins and three existing native-interface pins;
the forbidden range control rejects it even when whitelisted. Run
`lake env lean tests/InductiveIndexSelectedTranslation.lean`.

`Verify.InductiveIndexBaseInsertion` transports this chronological selected
index telescope over a supplied larger typed base. `IndexMLCtxExtension.virtualFVars`
identifies the exact selected identifier prefix of a mixed extension.
`SelectedRecursorTelescope.insertBase` takes original and larger mixed-context
well-formedness, a genuine cutoff-zero semantic base weakening and selected-ID
freshness in the larger base. It constructs the transported telescope and its
well-formedness; it does not assume an independently well-formed projected
endpoint. After `j` selected binders, the next semantic domain is lifted by
`semantic.liftN inserted j`: prior selected references remain fixed while
references to the original base move past the inserted binders. The returned
endpoint weakening is `FVLift'` with lift
`.consN (.skipN .refl inserted) ids.length`, so translated endpoint expressions
can be lifted at the complete selected suffix cutoff as well. Each preserved
named binder's dependency premise comes from its actual translated domain.

`SelectedRecursorTelescope.insertExtension` specializes to an actual
`IndexMLCtxExtension initial insertedIds larger`, using `insertedIds.length`
as the insertion count and deriving original mixed-context well-formedness by
dropping the extension from the supplied larger model. Virtual-context
well-formedness from a generic semantic weakening does not alone establish
original mixed-context well-formedness; the generic theorem retains that
distinct premise. The generic weakening also does not prove native provenance
of the larger base, whereas this structural specialization supplies an actual
mixed extension.

`TranslatedRecursorIndexTrace.selectedTelescopeInserted` starts from the same
actual-history selected telescope, retaining its chronological mixed model,
native/virtual endpoint matching, extension and unchanged initial index-array
prefix. Its freshness premise concerns only the newly allocated suffix
`finalIndices.toList.drop indices.size`, not existing prefix indices that may
already inhabit the base. Exact full-reader lookup evidence, including physical
indices, identifiers, names, stored peeled domains, binder information and
declaration kinds, is retained. The transported projected model's physical
indices can change with the larger base; its native context is not claimed to
equal the actual reader. This is insertion only: it does not remove unused
earlier parents, reorder existing binders, prove inserted motive/minor typehood,
discharge collisions for a complete concrete recursor construction or derive
whole `RecursorSelectedDomainSupport`.

The whole-module census is eight declarations / eight theorems, including four
generated simp helpers. The identifier-prefix theorem and generated helpers use
only `propext`; the three transport theorems use the three standard logical
axioms, inherited `sorryAx` and the same three existing allocation/storage
interfaces. In particular, expression weakening still depends on the existing
admitted `TrExprS.weakFV'` and translation foundations; no new admission, axiom,
runtime path, cache or native loose-bound-variable-range dependency is added.
`tests/InductiveIndexBaseInsertion.lean` adds eleven proof controls, nine mixed
base/selected-reference and nine nested-binder cutoff controls, and six exact
selected native cdecl checks across insertion sizes zero, one and three with an
original local/let base. These arithmetic and native helper controls do not
claim independent semantic typing or frontend acceptance. Exhaustive module/helper
audits retain inherited/native provenance pins and reject the forbidden range
interface even when whitelisted. Identity and uniform-cutoff-zero semantic-model
mutations both fail at the intended semantic-domain sentinel. Run
`lake env lean tests/InductiveIndexBaseInsertion.lean`.

`Verify.InductiveIndexDomainStrengthening` proves
`TrExprS.strengthenIsType`: a type-valued source translation can be rebuilt in
a smaller virtual context from its source closedness and retained free-variable
support. Inputs retain a genuine structural weakening into an aligned context,
definitional equality between the original and aligned contexts, and original
typehood. Inverse expression translation constructs a reduced semantic domain;
translation uniqueness, context conversion and inverse typing weakening derive
its typehood at the same sort level. The original semantic domain is
definitionally equal to the lifted reduced domain, not asserted to be its
literal syntactic lift image.

The generalized `TrExprS.strengthenIsTypeAt` preserves this receipt under
anonymous binders, retaining independent native closure depth and protected
semantic lift depth. An anonymous lambda increases both depths; an anonymous
let increases only native closure depth. The original `strengthenIsType` API
remains the zero-depth specialization with the same premises and three outputs.

`Verify.InductiveSubstitutionStageBody` proves
`TrExprS.strengthenSubstitutionBodyIsType` for a type-valued native body under
one anonymous formal binder. It requires an explicit definitional equality
between the original actual domain and the lifted reduced actual domain,
structural base weakening into an aligned context, original/aligned context
agreement, original body translation and typing, `Closed body 1`, and body
free-variable support in the supplied smaller context. That support may include
both the retained base and chronological suffix; adding an anonymous binder
does not add a free-variable identifier.
The helper returns six separate receipts: extended weakening and context
agreement, actual reduced-domain typing at its specified sort, reduced-body
translation and typing under that domain, and original/lifted reduced-body
definitional equality. The body lift is `lift.cons`, protecting its formal
binder. Domain typing is recovered from the supplied equality and inverse
weakening, not assumed from an identifier or allocation. All three strengthening
helpers retain exactly the four inherited logical/typing dependencies
(`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`), with no native/container
interfaces or new admissions. This does not provide literal stage preimages,
argument equality, whole-chain strengthening, native telescope/`replaceParams`
reconstruction, chronology-to-target weakening, inserted motive/minor typehood
or checker/source acceptance.
The focused fixture has 20 proof controls and 24 runtime checks. It forwards
all six receipts, applies the helper to actual formal/base/suffix and nested
body translations, consumes a nonliteral actual-domain equality, and exercises
two protected lambda binders and an anonymous let with distinct native/semantic
depths. Closure, missing/dropped-fvar support and wrong-lift negatives enforce
the boundary. Exhaustive audits cover both production modules (two declarations
each, including generated helpers) and exact dependency manifests for all three
strengthening theorems.
Run `lake env lean tests/InductiveSubstitutionStageBody.lean`.

`Verify.InductiveSubstitutionStageRebase` connects that reduced-body receipt to
`SemanticSubstitutionChain`. Its
`TrExprS.strengthenSubstitutionStageRebased` theorem preserves all six body
receipts and appends four: a genuine one-stage reduced-context chain, target
body translation and typing, and the corresponding target-context chain.
The additional premises give argument definitional equality at the actual
reduced domain in the smaller context, explicit smaller-to-target insertion,
and target WF. Argument equality already supplies both argument typings;
smaller WF is recovered from the removal receipt and aligned-context WF.
The source stage is built with substitution congruence and `single`; the target
stage structurally weakens that same chain, not merely its endpoint equality.
All outputs share the same existential reduced body and result sort. Removal
and insertion remain independent: the original body comparison uses
`removalLift.cons`, target body/domain transport uses `insertionLift.cons` and
`insertionLift` respectively, and both target arguments use plain
`insertionLift`. Substitution/lift commutation identifies the target endpoints
with instantiations of the transported body while protecting its formal binder.
This receipt does not assume native-domain translation or infer original
argument preimages, whole-chain strengthening, chronology-to-target weakening,
native telescope/`replaceParams` reconstruction, inserted motive/minor typehood
or checker/source acceptance. Dependencies retain only the four inherited
logical/typing axioms, without native/container interfaces or new admissions.
The focused fixture has 26 proof controls and 26 runtime checks, forwards all
ten receipts, and instantiates a genuine one-declaration removal plus a distinct
two-declaration insertion beneath a retained suffix. Its nested body uses the
formal binder, suffix and retained base, with nonliteral beta domain and stage
argument equalities. Both chains project equality and endpoint typing in their
own well-formed contexts. Wrong body/argument lifts, suffix cutoffs, conflated
coordinates, support and closure negatives pin the boundary. An exhaustive
two-declaration module audit includes generated helpers and enforces the exact
four-axiom inherited manifest.
Run `lake env lean tests/InductiveSubstitutionStageRebase.lean`.

`Verify.InductiveSubstitutionStageEndpoint` proves
`TrExprS.strengthenSubstitutionStageEndpoint`, connecting an original
instantiated type to the removal-lifted reduced instantiated type. Its explicit
argument equality compares an arbitrary original semantic argument with the
plain removal lift of the reduced argument at the actual original domain, in
the original context. The original argument need not be a literal lift image,
a free-variable lookup, or the translation of a supplied native argument.
This accepts semantic argument agreement from actual histories once it has
been converted to the actual original domain; it does not reconstruct native
stage preimages.
The theorem preserves all six body-strengthening receipts and appends reduced
argument typing, reduced instantiated endpoint typing, and original-to-lifted
reduced endpoint definitional equality. All nine outputs share one existential
reduced body; the body and instantiated endpoint receipts preserve the same
result sort. Reduced argument typing is derived by
converting the equality's right-hand typing to the lifted reduced domain,
transporting it to the aligned context, and inverting the actual removal.
Substitution congruence consumes the body equality and argument equality at the
actual original domain. Substitution/lift commutation then identifies the
result with the plain removal lift of the reduced endpoint; only the body lift
protects the formal binder with `.cons`.
No direct chronological-to-target weakening is assumed or derived. Independent
target insertion, whole-chain strengthening, native telescope/`replaceParams`
reconstruction, inserted motive/minor typehood and checker/source acceptance
remain outside this bridge. It also does not turn simultaneous body and
argument agreement into a literal single-body substitution stage. Dependencies
retain the four inherited logical/typing axioms, without native/container
interfaces or new admissions.
The focused fixture has 29 proof controls and 22 runtime checks. It forwards
all nine receipts, projects original and reduced endpoint typing, and checks
conversion of a historical equality to the actual original domain. Its genuine
one-declaration removal preserves a suffix and base under nested body binders.
The original argument beta-reduces to the lifted reduced argument while its
erased argument mentions the removed coordinate; a proof shows that no literal
lifted stage preimage exists. Nonliteral domain and endpoint syntax, support,
closure, context length, suffix cutoff and plain-versus-protected lift controls
pin the semantic boundary. An exhaustive one-declaration module audit enforces
the exact inherited four-axiom manifest.
Run `lake env lean tests/InductiveSubstitutionStageEndpoint.lean`.

`Verify.InductiveSubstitutionStageEndpointRebase` proves
`TrExprS.strengthenSubstitutionStageEndpointRebased`, retaining the original
endpoint bridge while inserting its reduced endpoint into an independently
supplied target context. It preserves all nine endpoint receipts unchanged
and appends four: target body translation and typing under the lifted actual
domain, target argument typing at that domain, and target instantiated endpoint
typing. All thirteen outputs retain one existential reduced body; the body and
endpoint typing receipts preserve the result sort.
The extra premises are smaller-to-target `FVLift'` and target WF. Actual target
domain typing is obtained by weakening the reduced-domain receipt, and supports
the anonymous target-body context needed for native translation. The body is
transported with `insertionLift.cons`; domain and argument use plain
`insertionLift`. Target endpoint typing weakens the already-proved reduced
instantiated endpoint, then uses substitution/lift commutation to express it
as substitution into the protected target body.
Original endpoint equality remains in the original context with its actual
removal lift. Target typing remains in the target context with its independent
insertion lift. No original-to-target context weakening or endpoint equality
is inferred, and no literal original-argument preimage or single-body
substitution chain is manufactured. This does not reconstruct native
telescopes/`replaceParams`, strengthen arbitrary whole chains, prove inserted
motive/minor typehood, construct an actual history, or establish checker/source
acceptance. Dependencies retain the four inherited logical/typing axioms,
without native/container interfaces or new admissions.
The focused fixture has 37 proof controls and 32 runtime checks, forwarding all
thirteen receipts. A genuine one-declaration removal and independent
two-declaration insertion protect the same suffix under a nested body using its
formal, suffix and retained base. Original endpoint equality remains in a
three-declaration context, while target body/argument/endpoint typing uses a
distinct four-declaration context. The historical beta argument retains its
universal no-literal-preimage proof. Target endpoint normalization, independent
coordinate maps, structural domain/argument/endpoint plain-lift negatives,
formal/suffix protection, support and closure controls enforce the boundary.
An exhaustive two-declaration audit includes the generated helper and pins the
exact inherited four-axiom manifest.
Run `lake env lean tests/InductiveSubstitutionStageEndpointRebase.lean`.

`Verify.InductiveParameterSubstitutionStage` connects that body-level endpoint
receipt to one selected `RetainedFVarPrefixAgreement.lookups` receipt. Its
`instantiateStageIsTypeRebasedCore` and `instantiateStageIsTypeRebased`
theorems take the supplied selection and actual original lookup, a type-valued
body translated under that lookup's actual domain, `Closed body 1`, support in
the exact source context, and independent removal/insertion receipts. Domain
and argument equalities are recovered from the actual prefix agreement, not
added as premises. The lookup is reconciled with both the supplied original
argument and its supplied type; the original domain's sort comes from that
same lookup receipt and is independent of the body's result sort.
The twenty-three outputs share one reduced argument, actual reduced domain,
domain sort and existential reduced body. Four lookup/actual-domain agreement
receipts precede the thirteen endpoint-rebase receipts unchanged; six native
receipts follow. These establish closedness and source support after native
fvar substitution, original and source substituted-body translations, target
fvar translation, and target substituted-body translation. The semantic source
endpoint is explicitly `reducedBody.inst reducedArgument`, rather than an
unrelated existential interpretation of an already-substituted native type.
Every substitution translation uses the corresponding actual argument typing.
Target argument translation is weakened from the source receipt through the
independent insertion; original endpoint equality stays in the original
context through removal. The core uses structural `instantiate1'` and the four
inherited logical/typing axioms. The native `instantiate1` specialization adds
only the existing `Expr.instantiate1_eq` interface, without new admissions.
This does not construct an actual translated index history, strengthen a whole
chain, infer original-to-target context weakening, require literal original
argument preimages, reconstruct native telescopes/`replaceParams`, prove
inserted motive/minor typehood, or establish checker/source acceptance.
The focused fixture has 30 proof controls and 24 runtime checks. Both APIs
forward all twenty-three receipts, and a genuine transported prefix constructs
the selected lookup agreement. The original selected declaration has a beta
domain, while the distinct aligned/source declarations have its reduced
domain. One-declaration removal and independent two-declaration insertion
preserve the nested body's formal/suffix/base coordinates. Three substituted
native translations, target selected-fvar translation, source/target endpoint
typing and original endpoint agreement are projected. Position, missing lookup,
original value/type mismatch, support, closure and wrong-lift controls pin the
boundary. This concrete selected lookup is a genuine `vlam` lookup; it does not
claim a nonliteral argument or no-preimage counterexample. Exhaustive audits
cover both module declarations and exact structural-four/native-five manifests.
Run `lake env lean tests/InductiveParameterSubstitutionStage.lean`.

`Verify.InductiveIndexSubstitutionStageRebase` lifts the selected-stage receipt
through an actual `TranslatedRecursorIndexTrace`.
`selectedTelescopeRebasedSubstitutionStageOfStoredDomains` takes the same
premises as the existing actual-history substituted-type adapter: mixed-model
alignment and WF, reservation/frame receipts, stored-domain support, retained
parameters and old index prefix, explicit base removal, independent insertion
and target freshness, an actual selected final lookup, and a translated typed
body with one formal binder and exact endpoint support. No new premises are
needed for the stronger body-level substitution receipt.
The result preserves fifteen chronological-history/rebase receipts and all
twenty-three selected-stage receipts. The chronological model remains equal to
the actual final reader and virtual context. New suffix IDs remain in history
order, while endpoint support uses their reversal followed by the smaller base.
The original lookup and body context are rewritten through that exact
chronological endpoint before consuming the retained-parameter agreement.
One existential reduced argument, actual reduced domain, domain sort and
pre-instantiation reduced body then account for all stage translations and
typing. The reduced instantiated interpretation is explicitly
`reducedBody.inst reducedArgument`, rather than an independently strengthened
interpretation of a substituted native type.
Original body and endpoint equality use removal
`.consN baseLift ids.length`; independent target translation/typehood uses
insertion `.consN (.skipN .refl inserted) ids.length`. Only body lifts add a
further `.cons` protecting the substitution formal. No direct chronological
to target context weakening or endpoint equality is inferred. Stored-domain
support and the supplied type-valued body remain explicit conditions; this
does not strengthen arbitrary whole histories, reconstruct literal native
stage preimages or telescope/`replaceParams` recipes, prove inserted motive/minor
typehood, or establish checker/source acceptance.
The exact inherited eight-axiom boundary matches the prior actual-history
adapters: four logical/typing dependencies, three persistent-container
interfaces, and the existing native `Expr.instantiate1_eq` interface. No new
axioms or admitted proofs are added.
The focused fixture has 19 proof controls and 20 runtime checks. It forwards
all thirty-eight outputs and applies the adapter to an actual empty translated
history with one formal used beneath two nested binders. That application
projects a shared reduced body, source/target native instantiated translations,
target instantiated typing, chronological endpoint equality, closure and
support. Nonempty retained-prefix/two-suffix tests are structural controls for
history order and support reversal, parameter selection, unsupported domains,
independent coordinate maps and body-versus-context lifting; they do not claim
construction or acceptance of a nonempty history. An exhaustive one-declaration
module audit enforces the exact inherited eight-axiom manifest.
Run `lake env lean tests/InductiveIndexSubstitutionStageRebase.lean`.

`tests/InductiveIndexSubstitutionStageOneStep.lean` additionally constructs a
nonempty translated history: a native forall over `Sort 0` allocates one fresh
index and terminates at `Sort 0`, with an actual `.index` followed by `.stop`.
The opening is built directly from sort translation/typehood, the pushed
mixed-context correspondence, the allocated binder's positioned declaration
and the native scope frame. Stored-domain support is proved for that actual
singleton declaration, rather than discharged by an empty list of binder steps.
Native sort normalization is derived from positive recursion depth, not assumed as
an arbitrary checker result. The native parameter list is empty, while the
retained selection remains an actual base membership and sort-zero lookup.
The separate type-valued stage body uses its protected substitution formal,
the allocated index and a selected retained parameter. The adapter's actual
array suffix and selected telescope determine the endpoint support and lift
cutoff; native instantiated translations and source/target typing share the
same existential reduced body. The original control invocation uses identity
base removal and insertion. Separate removal-one/insertion-two probes derive
their protected index cutoff from the actual pushed-ID receipt; they are not
applications over distinct removed/inserted mixed bases. Missing-index and
missing-parameter support negatives also pin the boundary. The twenty-one
one-step proof controls and twenty-one runtime checks remain, retaining
the original identity-base controls. Exact audits pin four dependencies for
native normalization and the inherited eight for both actual-history
applications, without new interfaces or admissions.
An additional actual invocation constructs a retained parameter over a supplied
well-formed reserved seed, an original mixed base with one removable declaration,
and an independently inserted mixed base with two declarations. All added
domains are native and virtual `Sort 0`. Their WF, native alignment and
freshness receipts are derived from allocation; mixed-context extensions derive
the nonzero base removal and insertion, rather than assuming either weakening.
Exact free-variable lists and different context widths distinguish the
constructed bases. The actual index is allocated after these names have
been reserved, so it remains fresh in the inserted base as well as in the
chronological original context.
The shared reduced body yields source and independently lifted target native
instantiated translations and endpoint typing. Target typing is also projected
in the commuting whole-endpoint-lift form; original endpoint equality keeps
the distinct one-declaration removal lift. Both protect the actual singleton
index suffix, and only body lifts protect the additional substitution formal.
The original selected argument has coordinate two; separate syntactic controls
pin the corresponding source/target argument and nested body coordinates,
without identifying the existential reduced body with a literal stage preimage.
A two-index application additionally constructs a genuine `.index`, `.index`,
`.stop` translated history from a nested native forall with two sort-zero
domains. Its first normalization is the inner native forall, and its second
is `Sort 0`; both are proved at positive recursion depth. Direct peeled
openings and the first positioned declaration transported through the second
native scope frame support both actual stored declarations. The exact two
suffix IDs are recovered in chronological order from the twice-pushed array.
Selected telescope support reverses them at the endpoint, before the retained
base; this is not just a two-suffix structural probe.
The type-valued stage body has three nested foralls and mentions its formal,
both allocated indices and the selected retained parameter. The actual
application reuses the constructed removal-one/insertion-two mixed bases,
with context cutoff two and one additional protected formal for body lifts.
Source/target native instantiated translations and endpoint typing share one
existential reduced body, while original endpoint equality uses the distinct
removal lift. No literal reduced-body identification is inferred from the
separate expected-coordinate controls.
The dependent two-index application additionally constructs a genuine
`.index`, `.index`, `.stop` history from `(first : Sort 0) → first → Sort 0`.
Its first opening substitutes the actual first allocated identifier into the
second native domain; the second stored declaration has precisely that free
variable as its type, not another closed sort. Native normalization of the
opened dependent forall and terminal sort is proved at positive recursion
depth. Both successful stored lookups are recovered through the actual scope
frames. Raw domain support allows the earlier chronological index, while
retained-base-only and reversed-history controls cannot supply that dependency.
The virtual endpoint distinguishes the first type-valued index from the second
proof-valued index, whose type is the shifted first index.
The dependent stage body uses its formal as a forall domain and the second
index as a well-typed native let value, with the first index as the let's type
and the retained parameter as its body. Translation checks the proof's actual
type; the let is erased and does not add a semantic binder. This application
preserves the constructed removal-one/insertion-two bases, cutoff-two context
maps, protected-formal body maps, shared existential reduced body, source/target
native instantiated translations and typing, and original endpoint agreement.
An empty mixed-context seed, empty semantic/native environments, empty native
parameter array and positive-depth reader instantiate the adapter without
fixture premises. This proves the test premises are jointly inhabited; it
does not establish kernel acceptance of an inductive declaration or retention
of the let-bound proof in the erased semantic body.
The full fixture now has fifty-eight proof controls and 115 runtime
checks, including all prior one-step and closed-domain two-step controls.
Exact audits pin four dependencies for the new forall normalization and the inherited eight for
the actual two-step and dependent two-step adapter applications, including the
premise-free empty-seed instantiation. Runtime checks also exercise actual
dependent allocation, both native normalizations and zero-depth rejection.
All fixture-namespace declarations, including generated helpers, are audited
for unexpected axioms. Order/reversal and missing-either-index/parameter
negatives pin the nonempty suffix and support boundary.
These proof fixtures exercise the existing adapter, not
inductive-checker/source acceptance, arbitrary whole-history strengthening or
a literal original-stage preimage claim.
Run `lake env lean tests/InductiveIndexSubstitutionStageOneStep.lean`.

`Verify.InductiveIndexSubstitutionStageBinding` connects these stage endpoints
to actual scoped native forall reconstruction. `IndexMLCtxExtension.typedBodyAbstractionS`
strengthens the existing abstraction bridge to strict translation into the
exact `MLCtx.mkForall'` semantic expression. Its selected-telescope corollary
also equates the full reader's native binding with the selected mixed model's
binding. Both derive body range-zero scope from translation and projected
context scope from mixed-context WF, using the extension's proved suffix bound,
reversed `fvarRevList` selection and exact dropped base. The selected bridge
keeps arbitrary full-reader scope explicit; the actual-history wrapper below
discharges it from the chronological WF receipt. They use the scoped
`MLCtx.WF.mkForall_eq` interface, not unrestricted native abstraction.
`TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutionStageNativeForall`
composes the actual-history stage adapter with these bridges at the actual
history endpoint. It derives endpoint reservation and scope from the translated
history, full-reader binding scope from the chronological model, and source and
target binding scope from their existing WF receipts. The same native expression
is equated with both reduced and independently inserted native telescope
bindings, strictly translated in all three original/reduced/target base contexts,
and proved type-valued there. Each semantic result is precisely its own model's
`mkForall'` application to the appropriate original or shared reduced endpoint;
the independent insertion retains its protected-index lift inside the endpoint.
After binding, translation weakening and strict translation uniqueness derive
abstracted-type agreement in the original and target base contexts using their
distinct base-only removal/insertion maps. These maps no longer protect an
extra context-level index suffix; the semantic forall binders protect their
own bound variables structurally. The existing original endpoint equality
remains available. No literal reduced-body identification or independent
chronological-to-target weakening is inferred.
Only newly allocated suffix identifiers are bound. Existing initial-array
identifiers stay in the supplied retained base. The wrapper deliberately uses
stored-domain receipts at `finalReader`; it does not infer global binding scope
for an arbitrary later native scope frame.
The genuine dependent two-step fixture instantiates the full native binding
wrapper without fixture premises, retaining the derived removal-one/insertion-two
bases and proof-valued let. A separate actual empty history has a nonempty
retained initial array and proves the new suffix binds nothing; binding the
whole initial array would not be the same operation. Runtime checks compare the
full, contracted and inserted native/model telescopes, check different physical
context widths, and reject reversed dependency order, omitted binders, binding
the retained parameter as part of the selected suffix, or retaining phantom
context suffix cutoffs after abstraction. Expected-coordinate controls are not
literal identifications of the existential reduced body. Exact axiom audits pin
eleven inherited dependencies for each strict abstraction helper and twelve for
the actual-history wrapper and its concrete applications: the existing logical
axioms, `sorryAx`, three container interfaces, four scoped abstraction/binding
interfaces, and native instantiation only for the history wrapper. All three
module-owned declarations, including generated helpers, are audited. The global
native range axiom is absent; no new axiom, admission or runtime code is added.
This establishes scoped type-valued native telescope reconstruction, not
inductive frontend acceptance, positivity, recursor reduction soundness or
complete parameter substitution through arbitrary telescopes.

`Verify.InductiveSingletonParameterReplacement` connects a type-valued native
body to executable `ElimNestedInductive.replaceParams` with genuinely nonempty
singleton source/replacement arrays. `replaceParams.singleton_eq` proves exact
agreement with structural `abstract1` followed by `instantiate1'`, preserving
the entire native state. Range-zero source scope is essential: native raw
abstraction preserves existing loose bvars whereas structural abstraction
shifts them. A loose-body negative control demonstrates this known model
boundary; it is not a kernel discrepancy.
`replaceParams.singleton_typed` takes a well-formed named source parameter at
the head of a mixed context, strict body translation and typehood, and strict
translation/typing of the replacement in the remaining base. It derives source
scope from translation, then proves strict translation to semantic singleton
instantiation and preserves the result sort. It also derives structural
closedness/range zero, remaining-base fvar support and exclusion of the source
identifier from that base. The replacement need not be a literal fvar.
`replaceParams.singleton_typedRebased` preserves these receipts and transports
the same native result's strict translation and typing through an independently
supplied well-formed base insertion, with its own semantic lift.

The actual dependent-history fixture supplies the scoped bound telescope and
its strict translation/typing, with an old source parameter declared over a
distinct declared target-parameter seed. Concrete applications replace the old
parameter with either the target fvar or a well-typed nonliteral beta-valued
argument, without fixture premises. Both preserve the dependent second binder
and proof-valued let, state, result sort and support in the target seed and its
independent two-declaration insertion. Twenty additional runtime controls
exercise actual nonempty replacement arrays, native/structural agreement,
source-ID removal, nontrivial state metadata, native type checking in the seed
and inserted context, unsupported/wrong-domain arguments, and the source-scope
boundary. Together with the preceding controls, the fixture has fifty-eight
proof controls and 115 runtime checks. All 155 fixture-namespace declarations,
including generated helpers, are audited.
Exact axiom audits pin six dependencies for singleton structural equality
(three logical axioms and the existing raw abstraction, reverse instantiation
and general instantiation interfaces), without `sorryAx`. The typed contracts
have ten dependencies, adding inherited `sorryAx` and three persistent-container
interfaces. The dependent-history fixture applications have fourteen inherited
dependencies, also retaining the previous scoped binding interfaces. All three
module-owned declarations are audited; no new axiom, admission or production
runtime change is introduced. The underlying history still uses empty native
parameter statistics: these receipts do not verify arbitrary nonempty parameter
histories, whole-prefix typed reverse substitution, nested frontend acceptance,
positivity or recursor reduction soundness.

`Verify.InductiveParameterPrefixReplacement` supplies the whole-prefix typing
bridge for an arbitrary-length ordinary-parameter suffix over a retained mixed
base. `ParameterPrefix` records the actual named cdecl construction and exact
chronological identifiers. It derives the suffix bound, exact dropped base,
reversed native `fvarRevList`, support decomposition and identifier distinctness
from source mixed-context WF. Its `lambdaBody` proof identifies the complete
abstracted body of the mixed model's native lambda telescope; it does not assume
that the selected array has the right order or that a let is a parameter.
`TypedParameterArguments` checks chronological arguments at each actual
dependent forall domain after earlier arguments have been instantiated. Each
argument is strictly translated and typed in the retained base, and its native
closure is derived from translation and the base's no-bvar property. This avoids
the invalid shortcut of typing a latest argument at an unsubstituted source
domain in a context still containing earlier source parameters.

`replaceParams.prefix_eq` proves exact native/structural reverse substitution
and state identity for equal-length arrays, distinct source IDs, a range-zero
body and closed replacements. `replaceParams.prefix_typed` derives these scope
receipts, constructs and types the full native/semantic lambda telescope,
applies the dependent argument trace, then uses structural beta reduction to
establish typehood of the executable substitution result. It supplies strict
translation to an existential output semantic expression, typing at the
unchanged result sort, and typed definitional equality to the original semantic
lambda applied to the chronological arguments. Structural closure/range zero
and remaining-base native support are retained. The existential strict output
semantics is not identified with a fabricated syntactic inverse or an unproved
literal simultaneous-substitution formula. `prefix_typedRebased` transports
that same witness, its sort typing and the functional-meaning equation through
an independently supplied well-formed base insertion. No intermediate native
parameter context is required to type a replacement at an unchanged dependent
source domain.

Concrete fixtures instantiate the contracts without fixture premises for empty,
singleton, two-parameter and three-parameter prefixes. The second parameter
really depends on the first; the third also has the first parameter's type.
Distinct target type/value declarations and a nonliteral beta-valued replacement
supply the dependent argument trace. Forall/let bodies retain native proof-use
domains/values, and results are actually type-checked in the retained base and
an independent two-declaration insertion. Twenty-one fixture proof controls and
22 runtime controls cover exact suffix/base/order, native/structural agreement,
source-ID removal, state metadata and invalid order/domain boundaries. Exact
audits pin six dependencies for raw scoped equality and ten for both typed
contracts and all five concrete typed applications. All 45 module-owned and 69
fixture-namespace declarations, including generated helpers, are audited. The
typed dependencies are the existing logical axioms, inherited `sorryAx`, three
persistent-container interfaces, raw abstraction, reverse instantiation and
general instantiation; no global native range axiom or new axiom/admission is
introduced.

Testing the replacement-scope boundary exposed a defect in the previous
trusted-interface specification: native instantiation is simultaneous whereas
the former unrestricted `Expr.instantiate_eq` identified it with sequential
substitution, which is false for loose replacement arguments. That existing
axiom now relates native instantiation to `Expr.instantiateMany`, a faithful
simultaneous structural model. It protects existing binder coordinates, inserts
each selected argument with the binder-depth lift without subsequently
substituting through that inserted value, and decrements indices beyond the
replacement prefix. Domains/let values and binder bodies have their exact
respective traversal depths. No new axiom is introduced, and the native bridge
remains trusted rather than formally proving the C++ routine.

Admission-free structural proofs establish empty/scalar instantiation, scope
cutoff preservation, general range bounds and closed-argument agreement with
sequential substitution. Native forward/reverse scoped corollaries use only
the existing corrected general/reverse instantiation interfaces. The native
push identity now requires the pushed argument to be closed; its earlier array
entries remain unrestricted. General nested-rewrite range propagation uses the
simultaneous range theorem, not an incorrect unscoped sequential equation.
Type-checker inference and comparison clients derive closure from fresh fvars
or actual translated application arguments. The internal lambda/forall helper
contracts expose the previously missing closure receipt, discharged by their
empty/fresh-fvar/default-value callers without changing the public checked
comparison contract.

`tests/NativeInstantiation.lean` retains the three historical negatives and 72
closed-argument sequential comparisons, and checks the corrected model on raw
loose/mixed/wide arrays, large representable indices, every constructor and
depths 0/1/2/5/33: 2640 raw native/model comparisons and 3960 closed-push
comparisons with arbitrary earlier arrays. A loose-push negative pins the
closed-push premise. Nine structural proof controls, the model definition and
four existing-native bridge controls are audited without `sorryAx`.
`divergences.md` records the counterexample and completed model repair.
The typed prefix contracts now inherit the corrected native implementation
specification, not its false retired sequential formulation. Existing typing
admissions remain; this is not unconditional kernel soundness, nested frontend
acceptance, positivity or recursor-reduction correctness. Discharging the actual
frontend's prefix/argument typing receipts is advanced by the independent-target
adapter below, but the complete frontend obligation remains open.

`Verify.InductiveParameterPrefixTyping` derives typed chronological parameter
contexts from the actual `ElimNestedInductive.withParams` traversal. The CPS and
collector contracts construct one well-formed `MLCtx` and `ParameterPrefix`,
identify its native local context and exact fvar array with the callback's
actual values, type the opened remainder, and reconstruct the original semantic
input by binding that remainder over the selected prefix. Freshness comes from
the live generator reservation; callers do not supply the resulting context or
its declaration typing.

`ParameterPrefix.arguments` derives all dependent chronological argument-typing
receipts for that context's own fvars, for an arbitrary semantic codomain. Each
later argument is checked at the domain after earlier arguments have been
instantiated. `replaceParams.prefix_typedInto` moves the abstracted source lambda
into an independent target before applying its target-scoped arguments. The
body and result types need not be sorts: partially applied indexed families have
residual forall types. This fixes two practical gaps in the retained-base-only,
sort-valued contract. Target-only fvars need not exist in the removed source
base. `prefix_rename_typed` supplies the argument receipts automatically for
well-formed source/target prefixes with a common retained base, equal selected
lengths and equal semantic domain contexts. It retains the exact native
substitution equation, strict existential target translation and typing at the
source semantic type, together with state, closure and target-support receipts.

`isNestedInductiveApp?.typedPrefix` extracts the actual `mkAppRange` selected by
the successful classifier from the complete source application's strict
translation and typing in an arbitrary `VLCtx`, including ambient raw binders.
Its bound comes from that same classifier receipt; residual indices are not
included in the prefix. `typedRebinding` composes this
actual classifier/first-`replaceParams` call boundary, deriving argument typing
from the declared target prefix rather than accepting it as an extra premise.
The original selected prefix and its rebound result share one semantic type;
the result retains the exact substitution equation, classifier scope, native
state and target support. This is a typed preprocessing-call contract, not just
range propagation, but it is not yet the complete `replaceIfNested` contract.

`tests/InductiveParameterPrefixTyping.lean` checks 13 fixture proof controls and
12 public production contracts. Exact audits pin seven dependencies for
argument derivation/weakening, ten for independent typed replacement, eight for
actual typed opening, five for typed prefix extraction, and eleven for the
classifier/rebinding composition. All 22 module-owned and 58 fixture-namespace
declarations, including generated helpers, are exhaustively audited. The two
pure insertion/domain-agreement controls use only logical axioms; typed
contracts explicitly inherit projection/typing admissions and existing native
interfaces. No new axiom, admission or global native range interface is added.
The 55 runtime controls use real independent source/target `withParams` captures,
genuinely dependent second domains, a let-using non-sort family, an actual
indexed nested container with its index excluded from the selected prefix,
full `TypeChecker.checkType`, ambient-bound index/closed-prefix separation,
state/order checks, short prefixes and overrun rejection. A strict application
fixture extracts a non-sort prefix in an actual bound-variable semantic context.
A proof negative shows target-only fvars are not translated in the
removed empty base. The low-level infer-only path is not used to establish
rejection of malformed dependent arguments.

`Verify.InductiveParameterOpeningAgreement` discharges semantic-domain equality
for independently opened copies of one strict semantic telescope, without
assuming equality of the resulting contexts or reading it from structural
`ParamValidity`. `ParameterPrefix.forall_eq_iff` recovers both the full semantic
domain context and the residual body from equality of two reconstructions with
the same selected parameter count and retained base. Native names, binder
information, annotations and fvar identities need not agree. Its inverse
direction also characterizes precisely when the reconstructions agree.

`TypedParameterOpening.agreement` uses the original-semantic reconstruction
receipts from two actual openings to construct a `TypedParameterAgreement`.
The result identifies both actual native contexts and chronological parameter
arrays, proves well-formedness and domain-context equality, and translates both
remainders to the same residual semantic type. `withParams.getTypedAgreement`
collects those receipts through two real sequential `withParams` traversals,
each allocating its own parameters from the current generator.
`TypedParameterAgreement.rebindRemainder` then supplies the previously explicit
domain agreement to typed parameter replacement. The composed
`withParams.rebindTypedRemainder` proves strict translation, typehood, closure
and target support for the actual open/open/replace program. Callers supply
strict closed input translations to a shared semantic telescope and its
typehood, not the opened contexts, semantic domain equality or dependent
argument-typing receipts.

`tests/InductiveParameterOpeningAgreement.lean` exercises 12 proof controls and
41 runtime controls. The native inputs deliberately differ in binder names,
binder information and metadata annotations, and contain a dependent second
domain. Zero-, one- and two-parameter openings use two generator offsets;
nonempty source/target arrays contain genuinely distinct IDs. Full
`TypeChecker.checkType` checks both native remainders and the rebound remainder.
Exact audits pin three logical dependencies for reconstruction injectivity,
four inherited dependencies for opening agreement, eight for actual paired
opening, ten for receipt-based rebinding and eleven for the composed program.
All ten module-owned and 33 fixture-namespace declarations are exhaustively
audited. Unequal semantic-domain and unequal-reconstruction negatives prevent
treating arbitrary structurally valid prefixes as equal. No new axiom,
admission or production runtime change is introduced.

`Verify.InductiveParameterDomainTransport` separately handles parameter domains
that are definitionally equivalent but not literally equal. Its
`ParameterPrefix.forall_defeq` reconstructs equivalent forall telescopes from
`VEnv.IsDefEqCtx` and a typed equality of their residual bodies. The numeric
semantic contexts permit independent native fvar IDs, and the retained base is
shared rather than silently discarded. `replaceParams.prefix_typedInto_defeq`
converts the abstracted source lambda's function type before applying typed
target arguments, preserving the exact native substitution equation, closure,
target support, strict translation, typing and beta equality.
`replaceParams.prefix_rename_defeq_typed` constructs the dependent target
argument receipts itself; its result type need not be a sort.
`isNestedInductiveApp?.defeqTypedRebinding` composes that transport with actual
classifier-selected parameter-prefix rebinding, without requiring literal
domain-context equality.

`TypeChecker.isDefEq.acceptedParameterDomain` obtains sorted semantic domain
equality from a successful checker call, strict translations, source-domain
typehood and a well-formed checker context/state.
`TypeChecker.isDefEq.acceptedParameterContextStep` extends an existing
`IsDefEqCtx` with that equality. These are accepted-check adapters, not a theorem
deriving aggregate parameter-domain agreement from an arbitrary accepted
`checkInductiveTypes` or `checkConstructors` trace.

`tests/InductiveParameterDomainTransport.lean` proves literal inequality of
contexts whose first domains are `Prop` and `(fun type : Type => type) Prop`,
then derives their semantic equivalence and typed replacement of a non-sort
lambda family across independently allocated dependent parameters. Additional
proof controls cover simultaneous domain/body conversion, a retained-base
zero prefix, and the checker adapter at an actual empty-context `M.run`
boundary. Its 55 runtime controls include independent opening offsets, native
replacement equations, full source/target family typing, an indexed nested
prefix, rejected reversed dependent arguments and incompatible universes.
Actual header/declaration/constructor checks accept nonliteral matching domains
and reject incompatible header domains. These runtime checks are distinct from
the semantic proof contracts. Exact audits pin one dependency for context
length, three logical dependencies for forall conversion, ten for converted
replacement and renaming, eleven for classifier/rebinding composition and the
same 28 inherited dependencies as `TypeChecker.isDefEq.WF` for the accepted
checker adapters. All 13 module-owned and 71 fixture-namespace declarations are
exhaustively audited; no new axiom, admission or production runtime change is
introduced.

`Verify.InductiveHeaderDomainAgreement` collects this equality along an actual
secondary-header `CheckedHeaderTrace`. A `ReducedParameterDomainReceipt`
aligns the real reader with a well-formed checker and empty initial state, and
supplies strict translations and canonical stored-domain typehood in the
chronological smaller parameter prefix, together with its insertion into the
full checker context. `ReducedParameterDomainReceipt.accepted` consumes the
trace's actual successful candidate/stored checker call, obtains sorted
equality in the full context, then strengthens it through that insertion. It
does not assume domain equality or treat a full-context judgment as a
prefix-context judgment without transport.

`CheckedHeaderDomainReceipts` follows the concrete reused-parameter and index
steps of the native trace. Its `agreement` theorem constructs aggregate
`IsDefEqCtx`, and `growth` proves the exact `nparams - index` extension on both
sides. Index allocation changes the native reader but does not add a parameter
domain. Fresh first-header allocation is intentionally not a constructor of
this receipt family. `checkInductiveTypes.loopInd.loop.scopedDomainAgreement`
passes the aggregate equality, exact lengths and actual scope frame to the
real loop continuation when its per-step receipt provider is supplied.
`CheckedHeaderDomainReceipts.rebindPrefix` uses the aggregate result for typed
replacement into an independently named equivalent parameter context; it
derives parameter-array length agreement rather than requiring it separately.

`tests/InductiveHeaderDomainAgreement.lean` builds genuine reduced-prefix
receipts inside a full two-parameter checker context. The first candidate
domain is beta-equivalent, not literally equal, to `Prop`; the second depends
on the first parameter. Its conditional accepted native trace constructs the
aggregate receipt without an assumed domain equality, then obtains equivalent
independently named contexts and non-sort family rebinding. Zero-prefix and
index controls retain arbitrary supplied parameter bases. Its 27 runtime
controls check the actual reused-header loop, exact normalization endpoints,
incompatible-domain rejection, index counting, fuel rejection, replacement
syntax/state/closure, full source/target family typing and result-type
conversion. Exact audits pin the same 28 dependencies as
`TypeChecker.isDefEq.WF` for strengthened accepted equality, aggregation, the
scoped loop contract and composed replacement. Concrete prefix receipts have
11 dependencies; the growth and zero/index receipt controls have four
inherited dependencies, including the existing `sorryAx` dependency encoded
in the receipt types. All 22 module-owned and 69 fixture-namespace declarations
are audited. There is no new axiom, admission or production runtime change.

`Verify.InductiveConstructorDomainTrace` retains the corresponding actual
constructor checks instead of reading equality from the older
`SafeConstructorTrace.parameter`, which omits their results.
`AcceptedConstructorTrace` records every selected parameter, actual stored-type
lookup and successful candidate/stored `isDefEq` call. Field steps retain the
actual `ensureType` result and universe guard, plus native positivity evidence
when the declaration is safe. Both safe and unsafe traversals retain their
final reader and binder index. Its `safe` projection recovers the original
positivity trace, and `scope` derives the native scope frame from original
well-formedness/freshness. `checkConstructors.loop.acceptedTrace` obtains this
trace from the real loop without a semantic receipt premise.
`checkConstructors.acceptedTraces` retains that trace, the successful source
no-metavariable/no-free-variable guard and the initial full-source `checkType`
call for every member of an accepted batch.

`CheckedConstructorDomainReceipts` consumes reduced-prefix receipts at the
recorded parameter checks and constructs aggregate `IsDefEqCtx`. Field
allocation changes the native reader but does not add a parameter domain. Its
exact growth is `min finalIndex numParams - min initialIndex numParams`, not
unconditionally all parameters: a raw loop can start partially checked or
accept an already-open terminal at index zero. `completeGrowth` gives
`numParams - initialIndex` only when the final index has reached the parameter
count. `rebindPrefix` derives equal independent parameter-array lengths from
the resulting domain agreement and provides typed non-sort rebinding.
`checkConstructors.domainAgreement` composes the actual accepted batch with a
per-constructor receipt provider, preserving initial source-check acceptance,
native traces, aggregate equality and exact checked-prefix lengths.

The constructor section of `tests/InductiveHeaderDomainAgreement.lean` reuses
the genuine full-reader/reduced-prefix semantic model from its header section.
It constructs accepted dependent nonliteral-domain traces and models for both
safety flags, typed independent family rebinding, retained partial bases,
field allocation without domain growth and the zero-check raw terminal case.
Its 33 runtime controls exercise real loops and full batches, safe positivity
rejection versus unsafe bypass, positive fields, duplicate-name rejection,
partial prefixes, fuel rejection, incompatible domains and exact retained
lookup/check pairs. An open terminal is accepted by the raw loop but rejected
by the outer source guard; this is a boundary control, not a kernel discrepancy
or evidence of complete parameter checking. Exact audits pin three logical
dependencies for native trace/batch extraction and safe projection, six for
native scope transport, four inherited dependencies for count/zero-prefix
controls, and the existing 28 checker dependencies for domain aggregation,
batch composition and typed replacement. Concrete native/semantic prefix
models use the inherited `Expr.instantiate1_eq` boundary, with exact manifests
of eight, twelve and five dependencies. All 51 production declarations and 26
constructor-fixture declarations are audited in addition to the header audits.
There is no new axiom, admission or production runtime change.

`Verify.InductiveConstructorDomainReceipts` derives the first reduced domain
receipt from these recorded native checks and a canonical parameter history,
instead of requiring a semantic receipt provider for that checkpoint.
`ParameterPrefix.selectedDomain` selects the actual stored native declaration
at any parameter position. It reconstructs its preceding `identifiers.take
index` prefix, the prefix's well-formedness, its insertion into the full reader,
and the stored domain's strict translation and sort typing from the canonical
model. It does not assume a reduced stored-domain translation or typing judgment.
`acceptedSourceTranslation` uses the successful source `checkType` call to
obtain its strict translation through the existing checker correctness theorem.
`ReducedParameterDomainReceipt.ofCheckedForall` then derives the candidate
domain's strict reduced translation from that accepted forall source and its
prefix support. No candidate translation, domain typing or semantic domain
equality is assumed as an additional receipt.

`AcceptedConstructorTrace.firstDomainAgreement` consumes the recorded source
guard and source check, the canonical parameter history, and the actual first
parameter lookup/equality check in the native trace. The source guard supplies
the empty-prefix candidate support, so this boundary needs no separate support
premise. `checkConstructors.firstDomainAgreement` derives the same receipt and
sorted domain equality for every member of a genuinely accepted batch, for
either safety flag. The existing accepted-source arity theorem supplies the
initial forall shape when the canonical parameter array is nonempty; that
shape is not assumed. Reader/checker alignment, the semantic checker model,
the reset checker's state well-formedness, and the canonical parameter history
remain explicit inputs. The theorem does not reconstruct those frontend models
from bare native acceptance.

The additional constructor receipt fixture constructs first and dependent
domain receipts directly from source-check acceptance, including a retained
nonempty base, without importing the old assumed candidate translations.
It also proves that a candidate depending on an absent free variable has no
strict empty-prefix translation: a successful full-reader check alone does
not license prefix strengthening. Runtime controls exercise native source
checks, canonical lookups, nonliteral equality, safe/unsafe accepted batches
and rejected ill-scoped or ill-typed candidate domains. All 13 production and
10 receipt-fixture declarations are audited, with 13 runtime controls. Exact
manifests pin seven inherited dependencies for canonical domain selection,
the existing 28 checker dependencies for accepted source translation and
receipt construction, and those 28 plus the three existing source-guard
expression axioms for accepted first-domain trace/batch agreement. The missing
prefix-dependency control has four inherited dependencies. Retaining the raw
source guard does not enlarge the native batch extractor's three logical
dependencies. There is no new axiom, admission or runtime change. This module
alone handles only the first checkpoint; the complete constructor propagation
is supplied by the following module, rather than by inventing source checks
for opened tails that the native loop never performs.

`Verify.InductiveConstructorPrefixReceipts` constructs the whole constructor
parameter receipt chain from the original accepted source check and a canonical
well-formed parameter history. `ParameterPrefix.uncons` exposes the next actual
canonical binder; `baseWF` and `retainsLookup` derive its typing and unchanged
native lookup from the full model. At each native parameter check the proof
constructs the reduced receipt directly from the current source translation,
canonical stored-domain typing and the recorded accepted `isDefEq` call.
`TrExprS.openCanonicalParameter` transports the raw body from its candidate
binder domain to the checker-approved stored domain, then instantiates the
actual selected free variable. The recursive proof propagates that strict
translation to the next dependent domain. It assumes neither a fresh checker
call on the opened tail nor an independently supplied semantic receipt.

The recursion retains an unprocessed canonical suffix, including its exact
length relative to the final native binder index. `completeParameters` proves
that accepted guarded sources consume every parameter: it propagates the
original source's remaining-parameter absence through actual substitutions
and uses the validated return application. A raw terminal without that source
absence cannot obtain this completion theorem. Fields are handled only after
the parameter array is exhausted; their recorded checks/positivity trace are
preserved while parameter-domain contexts remain unchanged.
`AcceptedConstructorTrace.domainReceipts` identifies the final stored context
with the full canonical checker context and derives aggregate candidate-domain
agreement and complete parameter growth. `checkConstructors.domainReceipts`
obtains this for every member of an accepted safe or unsafe batch without a
receipt-provider callback or an assumed complete-prefix equality judgment.

`ParameterPrefix.contextAgreement` separately records the semantic agreement
between a canonical prefix base and its full source context. The new
`AcceptedConstructorTrace.domainReceiptsAtParameterModel` and
`checkConstructors.domainReceiptsAtParameterModel` providers use that split
explicitly: constructor receipts end at the parameter-only semantic model,
while the indexed ambient reader remains an explicit `ambient` suffix with a
`dropN`/`parameterBase` alignment premise. This prevents the full native
`indices :: parameters :: base` reader from being identified with the
`parameters :: base` constructor prefix.

The split provider still requires the canonical parameter history, the ambient
prefix model, and their explicit `parameterBase` alignment. Native indexed
header checking retains its allocated index binders in the reader passed to
constructor checking; the provider preserves that suffix rather than claiming
full-reader equality. The new first-header adapter closes the history-to-receipt
composition only; it does not extend the semantic environment with inductive
headers or prove family/cache/registration obligations. General
annotation-domain peeling removes the old literal-universe restriction, not
those remaining environment and registration obligations.

The constructor prefix fixture derives a genuine checker environment from the
verified native registration of a safe family axiom, constructs its canonical
dependent local context and reset-state model, and applies the complete batch
provider. The family is a typed checker fixture, not a proof of inductive
family registration. Native controls include both safety flags, a dependent
second parameter, nonliteral first domains, fields, retained partial loops,
rejected incompatible domains and raw zero-check terminals excluded by the
source guard. The semantic opening control changes a candidate beta-equivalent
binder to its canonical stored domain before checking the dependent tail.
All 29 production and 17 prefix-fixture declarations are audited, with 25 new
runtime controls. Exact manifests pin four inherited dependencies for prefix
well-formedness and the field-only receipt chain, one logical dependency for
canonical prefix decomposition, seven for native lookup retention, four for
prefix context agreement, and eight for semantic binder conversion/opening.
Native source-absence completion has five dependencies and no inherited
admission. Both parameter-model receipt providers have the existing 28/31
checker dependencies (with the latter including the three source-guard
expression interfaces), matching the original full-context providers. There
is no new axiom, admission or runtime change.
The initial reader/checker alignment, semantic environment/local-context model,
reset-state well-formedness and canonical parameter history remain explicit
production inputs. Constructing those models from the actual first header,
semantic generated-family/cache/constructor registration, and the larger
independent rebinding traversal remain open. This is a complete conditional
constructor parameter-domain provider, not unconditional frontend soundness.

The original `typedRebinding` literal semantic-domain agreement premise remains
explicit outside its shared-semantic-input case. The new definitional transport
is an alternative boundary, not a proof that accepted original headers and
constructors have literally equal strict translations. Constructing first-header
semantic typing/checker models and the complete header receipt providers from
accepted original inputs remain open. Constructor receipts are now derived
from accepted source checks once the canonical checker model is supplied;
the frontend integration is still conditional, not unconditional soundness.
Rebinding callbacks below unopened raw binders also need to strengthen the
selected closed prefix from
its ambient bound-variable context into the parameter-only source context;
the classifier permits loose residual indices, while the current rebinding
adapter assumes a strict full-application receipt in that parameter context.
Initial strict source
translation/typing, semantic typing of cached auxiliaries and newly generated
families/constructors, full replacement traversal and frontend acceptance,
positivity and recursor-reduction correctness remain separate obligations.

`Verify.InductiveIndexBaseStrengthening` uses this domain lemma to contract a
chronological selected telescope over a supplied smaller mixed base.
`SelectedRecursorDomainFVars` constrains only actual full-reader stored cdecl
domains: each domain's native free variables must lie in the smaller base or
earlier selected identifiers. Its prefix and final-domain projections do not
assume reduced-context translations or typing. Existing translation receipts
supply closedness and metavariable exclusion independently.
`SelectedRecursorTelescope.strengthenBase` takes original and smaller mixed-base
well-formedness, this source support and a base `FVLift'`. It constructs the
reduced telescope, its endpoint well-formedness, and a virtual aligned endpoint.
Freshness follows from the original native freshness and virtual fvar inclusion;
there is no new collision premise. The final weakening is from the reduced
endpoint into the aligned endpoint with `.consN baseLift ids.length`, together
with `VLCtx.IsDefEq` from the actual chronological endpoint to that aligned
context. This is genuine contraction, not identity transport or a claim of
exact semantic-context equality.

`SelectedRecursorTelescope.strengthenExtension` specializes to a concrete omitted
cdecl suffix and derives smaller mixed-base well-formedness by dropping its
actual `IndexMLCtxExtension` from the original well-formed base. The generic
weakening can represent interspersed omissions, but does not itself prove a
native selection algorithm or mixed-context well-formedness.
`TranslatedRecursorIndexTrace.selectedTelescopeStrengthened` starts from the
same actual translated history and later native scope frame, retaining the
chronological endpoint's well-formedness, native/virtual matching, extension and
unchanged initial index-array prefix. Source support applies only to identifiers
extracted from the newly allocated suffix; the history proves these are exactly
the selected identifiers. Full-reader lookup indices, IDs, names, stored peeled
domains, binder information and declaration kinds remain unchanged, while
projected indices may change after contraction.

The domain module census is one declaration / one theorem; the base module is
eight declarations / seven theorems, including two generated simp helpers.
The domain lemma uses only the standard logical axioms and inherited `sorryAx`;
the base module additionally uses the three existing allocation/storage
interfaces. Inverse translation/uniqueness still inherit projection admissions,
and inverse typing weakening inherits the existing `IsDefEqU.weakN_iff`
admission. No new admission, axiom, runtime path, cache or native range dependency
is introduced. Constructing a concrete smaller base, proving its structural
selection, and discharging stored-domain support from checked/generated header
receipts remain caller obligations. Complete recursor reordering, motive/minor
typehood and whole `RecursorSelectedDomainSupport` are not derived here.
`tests/InductiveIndexBaseStrengthening.lean` adds thirteen proof controls covering
the domain lemma, generic and actual-extension contraction, native binding
agreement and actual-history suffix transport. Eighteen cutoff-inverse controls,
six selected-cdecl and nine retained dependent/let-base checks cover removal
sizes zero, one and three; three source-support failures distinguish dropped,
current and future dependencies. The numerical/native models do not provide
independent semantic typing. Identity and wrong-cutoff model mutations fail at
the intended semantic-reference sentinel. Exhaustive module/helper audits use
separate domain/base policies, retain translation, inverse-typing and native
provenance pins, and reject the forbidden range interface even when whitelisted. Run
`lake env lean tests/InductiveIndexBaseStrengthening.lean`.

`Verify.InductiveIndexBinderOrder` proves `BinderStep.indexIds_split`: a split
of the filtered chronological index-ID list identifies an actual index step and
exactly the same earlier filtered prefix at its raw binder position. Parameter
steps can be arbitrarily interleaved; no nodup, all-index, declaration or typing
premise is needed. The result preserves position and order rather than merely
set membership, and does not turn duplicate native IDs into typed binders.

`Verify.InductiveIndexDomainSupport` derives the contraction theorem's ordered
native support premise from existing generated-header dependency receipts.
`BinderStoredIndexTypeFVarsIn.selectedDomains` applies the filtered-order witness
to the exact actual cdecl lookup, obtaining stored-domain free-variable support
in parameters and earlier selected IDs. Parameter inclusion in the retained
base yields `SelectedRecursorDomainFVars`; there is no assumed projected typing
or desired ordered-domain support. The raw-domain convenience theorem reuses
the existing `storedIndexTypeFVarsIn` bridge and its actual declaration receipts,
so annotation peeling and stored-type alignment are not bypassed.
`SelectedRecursorDomainFVars.dropPrefix` moves only a retained earlier index
prefix and the old base into the supplied new base, preserving the selected
suffix's own chronological ordering. Earlier indices remain legitimate domain
dependencies; membership in a complete index array does not license current or
future dependencies.

`ParentBinderIntegrity.selectedIndexDomains` extracts the actual generated
steps' stored-type receipt and their exact equality with `info.indices`.
`RecursorBinderIntegrity.selectedIndexDomains` applies this to each bounded
parent. Both retain explicit parameter inclusion in the chosen base; neither
infers the receipt from allocation alone nor substitutes checked-side support
for generated-side lookup evidence.
`TranslatedRecursorIndexTrace.selectedTelescopeStrengthenedOfStoredDomains`
combines stored receipts matching the full actual index array with the same
translated history. It derives the preserved initial-array prefix/suffix split
from actual allocations, moves retained parameters and preexisting indices into
the smaller typed base, and discharges suffix support internally before calling
semantic contraction. The result keeps chronological endpoint well-formedness,
native/virtual matching, extension, unchanged index-array prefix, exact native
lookup evidence, reduced endpoint well-formedness and the honest aligned virtual
endpoint. It does not require callers to supply `SelectedRecursorDomainFVars`.

This closes the ordered stored-domain support adapter, conditional on existing
generated-header receipts, their equality with the actual trace's full index
array and retention of parameters/preexisting indices. A concrete smaller mixed
base and its structural semantic weakening remain explicit; complete parameter
translation, motive/minor typehood, recursor reordering and whole
`RecursorSelectedDomainSupport` remain separate obligations. Semantic contraction
still inherits its existing inverse-translation/typing admissions; no new
admission, axiom, runtime path, cache or native range dependency is introduced.
The binder-order module census is one declaration / one theorem, using only
`propext`. The support module is six declarations / six theorems with no extra
private/generated declarations. Its stored/raw support, prefix contraction and
parent/recursor wrappers use only the three standard logical axioms, without
`sorryAx` or native interfaces. Only the final actual-history semantic adapter
uses the inherited seven-axiom policy: logical axioms, `sorryAx` and the three
existing allocation/storage interfaces. No abstraction/instantiation interface
is needed by either module.
`tests/InductiveIndexDomainSupport.lean` adds fifteen proof controls exercising
all seven new APIs. Three shifted mixed-role fixtures include six exact cdecl
provenance checks and three structural duplicate-ID controls; four missing
parameter/omitted/current/future dependency failures and positive/negative
initial-prefix retention controls enforce the source-support boundary. Annotation
controls distinguish raw default dependencies, peeled stored types and metadata
barriers. These native/structural controls do not prove semantic typing or
frontend acceptance. Raw-versus-stored and prefix-omission fixture-model mutants
fail at their intended sentinels. Separate module and pure/semantic API audits
retain inherited provenance pins and reject the forbidden range interface even
when whitelisted.
Run `lake env lean tests/InductiveIndexDomainSupport.lean`.

`Verify.InductiveIndexRebase` composes the selected-telescope contraction and
larger-base insertion receipts through one shared reduced endpoint.
`SelectedRecursorTelescope.rebase` returns the reduced telescope, its explicit
contraction weakening and aligned old endpoint, plus the independently
well-formed larger-base telescope and its insertion weakening. It requires
the smaller mixed-base well-formedness derivable from the removal extension,
larger-base well-formedness, and freshness of every selected identifier in the
new base; it does not identify the old and new endpoints or infer freshness
across an arbitrary replacement base. `TrExprS.rebaseIsType` transports a
supported closed domain/type through the same reduced semantic expression,
preserving the old definitional equality and deriving the larger-base strict
translation/typehood by weakening. Neither helper types inserted motives or
minors, proves a concrete smaller-base construction, or establishes complete
recursor-body/source acceptance. `SelectedRecursorTelescope.rebaseBodyIsType`
adds a supported body/type receipt over the exact reduced fvar list
`ids.reverse ++ smaller.vlctx.fvars`; it reuses the explicit common endpoint
and never assumes a separately translated common body. The rebase modules add
five composition/transport theorems and no new admissions, axioms, runtime
paths or caches; their inherited
typing receipt retains the existing inverse-translation `sorryAx` boundary.
Run `lake env lean tests/InductiveIndexRebase.lean`.

`Verify.InductiveParameterPrefixTransport` adds `RetainedFVarPrefix` and
`VLCtx.FVLift'.retainedPrefix`. For each position in the supplied retained
parameter-ID list, the receipt provides exact source and lifted-target virtual
lookups, strict fvar translations and semantic typing in both contexts. It
retains the same ordered IDs, without treating let-valued entries as bvars or
assuming that the supplied list is a contiguous native telescope prefix. The
proof uses an explicit weakening and environment/context well-formedness;
membership preservation alone would not establish these typed lookups.
It introduces no new admissions, axioms, runtime paths or caches and inherits
the existing `sorryAx` boundary from typing lemmas. Focused tests cover receipt
construction and projection, mixed lambda/let lookup lifting through selected
binders, and omitted-ID and wrong-position negative controls.
Thirty runtime checks exercise exact semantic/type positions; the exhaustive
ten-declaration bridge audit permits only inherited logical/typing axioms,
not container or expression-range interfaces.
Run `lake env lean tests/InductiveParameterPrefixTransport.lean`.

`Verify.InductiveParameterPrefixAgreement` adds
`RetainedFVarPrefixAgreement` and `RetainedFVarPrefix.agreesWithOriginal`.
It pairs each retained reduced-context lookup with the actual original-context
lookup through the explicit reduced-to-aligned transport and
`VLCtx.IsDefEq original aligned`. The receipt supplies strict source/original
fvar translations and typing, plus definitional equality of the original type
with the lifted reduced type at an explicit sort, and of the original value
with the lifted reduced value at the original type. Both equalities live in
the original context, not the reduced context. Sort typing is recovered from
the original lookup typing before converting the existing `IsDefEqU` lookup
comparison: its arbitrary type witness is not treated as a universe level.
The aligned transport remains a separate receipt. This is semantic lookup
agreement, not literal value equality, native declaration equality,
parameter-prefix contiguity/distinctness, telescope reconstruction/substitution,
checked-source/header acceptance or inserted motive/minor typehood.
No new admissions, axioms, runtime paths or caches are introduced; the proof
retains the existing typing/unique-typing `sorryAx` boundary.
Focused controls cover genuinely nonliteral beta-value agreement, distinct
but equivalent universe types, ordered duplicates and missing IDs, including
the selected-endpoint lift. Thirty exact runtime lookup checks and exhaustive
agreement-module audits exclude container and expression-range interfaces.
Run `lake env lean tests/InductiveParameterPrefixAgreement.lean`.

`Verify.InductiveParameterSubstitution` adds
`RetainedFVarPrefixAgreement.instantiateCore` and `.instantiate` for one
position-selected retained parameter. The supplied original lookup determines
the anonymous lambda binder's actual domain; the native body must have strict
translation and semantic typing under that binder, and fvar support over the
reduced context. The result preserves that support after substitution and
provides the reduced argument's actual lookup/translation/typing, strict
original-context translation of the substituted native body, typing with both
the original argument and the lifted reduced argument, and substitution
congruence for values and dependent result types. Result-type congruence is
typed at an explicit sort recovered from the body typing. Both comparisons
remain in the original context and use the same supplied alignment lift.
The structural helper uses `instantiate1'` and retains only inherited
logical/typing axioms including `sorryAx`; the actual native `instantiate1`
wrapper additionally uses the existing `Expr.instantiate1_eq` interface axiom.
No new admissions, axioms, runtime paths or caches are introduced.
This substitutes into an explicitly translated original body; it does not
construct a contracted reduced body, prove whole-prefix reverse substitution
or `replaceParams` correctness, reconstruct native parameter telescopes, or
discharge inserted motive/minor typehood or source/header acceptance.
Twenty-four focused proof controls exercise nonliteral beta parameters,
dependent result types and doubly nested lambda bodies under zero/one/three
insertions and the selected-endpoint cutoff. Thirty-six runtime checks cover
lookup shifts and native/core instantiation; omission/support/position
negatives and separate core/native axiom audits enforce the stated boundaries.
Run `lake env lean tests/InductiveParameterSubstitution.lean`.

`Verify.InductiveParameterSubstitutionRebase` adds
`RetainedFVarPrefixAgreement.instantiateIsTypeRebasedCore` and
`.instantiateIsTypeRebased`. A supported original-context type body under its
actual anonymous parameter domain must be closed at depth one. The proof uses
the existing structural `Closed.instantiate1_offset` to derive depth-zero
closure after substituting the retained fvar, then composes single-parameter
substitution with explicit source-to-aligned weakening, original/aligned
context agreement and independently supplied source-to-target weakening.
It returns the selected argument's exact source lookup/translation/typing,
substituted closure/support and original translation/typehood, source and
target translations/typehood through one existential reduced result, and
sort-correct original-context comparisons for both the actual original
argument and the removal-lifted source argument against that common result.
The agreement and old-context comparisons use only `removalLift`; target
translation/typehood use only `insertionLift`. The proof derives original
context well-formedness from the explicit context agreement, not from the
positionwise lookup receipt alone. Core dependencies remain inherited
logical/typing axioms including `sorryAx`; the native wrapper additionally
uses only the existing `Expr.instantiate1_eq` interface, with no native range
interface or new admission/axiom/runtime/cache changes.
The reduced result is not asserted to be substitution into an independently
contracted pre-substitution body. This does not prove full-prefix reverse
substitution, native parameter reconstruction, inserted motive/minor
typehood, complete binder reordering or checker/source acceptance.
The focused fixture has 27 proof controls and 28 runtime checks, including a
beta-valued retained type parameter, nested forall bodies, distinct one/three
removal/insertion lifts and selected `consN` cutoffs. Omitted/dropped parameters,
unsupported/unclosed bodies and wrong-position negatives enforce the premises;
separate core/native audits cover every module declaration and check the
structural closure helper's logical-only provenance.
Run `lake env lean tests/InductiveParameterSubstitutionRebase.lean`.

`Verify.InductiveParameterSubstitutionPair` adds
`RetainedFVarPrefixAgreement.instantiatePairIsTypeRebasedCore` and
`.instantiatePairIsTypeRebased`. A body translated and sort-typed under two
actual anonymous domains must be structurally closed at depth two and have
reduced-context fvar support. Both arguments are selected by supplied list
positions with exact original lookups. An explicit typing receipt for the
raised original inner argument at the actual inner domain is required while
the outer binder remains; the proof does not infer that domain from the
original inner lookup's lifted type or reconstruct dependent parameter types.
The first substitution eliminates the innermost anonymous binder, deriving
an intermediate translation, sort typing, depth-one closure and support. That
exact intermediate expression supplies the existing outer substitution/rebase
helper; final original semantics are
`(bodySemantic.inst originalInnerArgument.lift).inst originalOuterArgument`.
The result preserves both reduced argument lookups/translation/typing, the
inner argument's original-context agreement, all intermediate receipts,
depth-zero final closure/support and original/reduced/target translations
and sort typing. Outer-only and simultaneous two-argument congruence compare
against one existential reduced final type using the removal lift, independently
from target insertion. No distinctness of the supplied positions/IDs or header
validity is asserted. Core dependencies remain inherited logical/typing axioms
including `sorryAx`; the native wrapper adds only `Expr.instantiate1_eq` for
both ordered operations. This does not identify the reduced result with
substitution of both reduced arguments into a separately contracted body,
prove whole-prefix recursion/native `replaceParams`, reconstruct telescopes,
prove inserted motive/minor typehood or establish checker/source acceptance.
`RetainedFVarPrefixAgreement.instantiatePairIsDefEq` provides the pure semantic
simultaneous congruence without native expressions, closure/support or target
weakening premises. Explicit original context well-formedness and original
outer lookup typing establish well-formedness under the remaining anonymous
binder. The proof weakens the inner argument equality, retags it to the actual
inner domain via `IsDefEqU.of_l` and supplied raised-argument typing, then
composes two `instDF` steps at the common sort. Both substitution/rebase helpers
append typehood of
`(bodySemantic.inst (reducedInnerArgument.lift' removalLift).lift).inst (reducedOuterArgument.lift' removalLift)`
and original-context comparisons from the original interpretation to this
both-reduced interpretation and from it to the lifted common reduced final
type. The extra inner lift protects the still-present outer anonymous binder;
none of these equalities identifies a separately contracted body's syntax.
The focused fixture has 30 proof controls and 30 runtime checks. A genuine
two-formal body preserves its nested local binder; swapped substitution order
and an unraised original inner argument fail their controls. Concrete proofs
cover distinct one/three lifts, repeated selected positions, both original
arguments as nonliteral beta values and an equivalent but nonliteral inner
domain with explicit raised-argument typing. Core/native projections verify
both-reduced typing and comparison with the common lifted reduced result; the
pure semantic helper has a separate projection without expression premises.
Closure, support and selection negatives and exhaustive audits of all three
module declarations enforce the premises and dependency boundary.
Run `lake env lean tests/InductiveParameterSubstitutionPair.lean`.

`Verify.InductiveParameterSubstitutionChain` adds the bounded semantic
`SemanticSubstitutionChain` relation for any finite sequence of substitutions
at one shared result sort. Each `cons` stage stores the before/after
instantiations, body typing under the explicit actual domain, and argument
definitional equality in the shared context; the tail carries the remaining
stages. The `single` helper packages one such stage, while `append` composes
already-linked receipts. Its `isDefEq` theorem composes `VEnv.IsDefEq.instDF` stage by stage,
`cancelLeft` projects a residual equality from a direct endpoint equality
through one such chain, using only transitivity at the fixed context. The
`hasType` theorem projects both endpoints. The relation keeps native argument-list
order; `append` composes receipts only when their intermediate endpoints are
definitionally linked. Its `weak'` theorem transports the entire chain through
an explicit `Ctx.Lift'` receipt using only environment ordering. Each stage's
actual domain and arguments use the supplied lift, while its body uses the
lift's `cons` extension to protect the formal binder. Substitution/lift
commutation preserves both stage endpoints, and the shared result sort is
unchanged. This is structural stage transport, not just a weakened endpoint
equality. Target equality, typing and cancellation projections additionally
require the usual target-context WF premise. The theorem supports insertion
lifts with protected chronological suffixes but does not infer a direct
chronological-to-target weakening from unrelated removal/insertion receipts.
The weakening helper's exact dependency audit contains only `propext` and
`Quot.sound`, not inherited `sorryAx` or `Classical.choice`.
It does not reconstruct retained positions, dependent domains, native
telescopes or `replaceParams` output. It also does not identify a chain with
an inductive trace or claim inserted motive/minor typing or checker/source
acceptance. The semantic module has no native expression or persistent
container interfaces beyond the inherited logical/typing axioms.
The focused fixture has 31 proof controls and 21 runtime checks, covering
empty, single, two- and three-stage construction, explicit per-stage domains,
shared sort, native order, nonliteral arguments and length/position negatives.
It also covers arbitrary context weakening, empty/single/two-stage transport,
append and equality/type/cancellation projections in an explicitly well-formed
target, and insertion with two protected suffix binders and three new base
binders. Cutoff and missing-formal-binder controls distinguish incorrect stage
transport, including beta-valued arguments. The module census audits all 19
declarations; the weakening and retained-pair helpers keep their separate exact
two-axiom and four-axiom manifests.
Run `lake env lean tests/InductiveParameterSubstitutionChain.lean`.

`RetainedFVarPrefixAgreement.instantiatePairOuterChain` connects the retained
pair receipt to the fixed-context chain. It preserves both exact source
argument lookups, the raised inner equality at its explicit actual domain,
and the simultaneous pair equality. It derives typing of the original-inner
intermediate body, reconciles the selected outer lookup witnesses, and returns
a one-stage chain replacing only the outer argument in `original.toCtx`.
Cancelling that chain against the simultaneous equality additionally proves
the residual inner equality with the reduced outer argument held fixed. This
is not a chain removing both formal binders across their different contexts.
No native expression, closure, support or target insertion premise is needed;
the module audit pins exactly the four inherited logical/typing dependencies
(`propext`, `Classical.choice`, `Quot.sound`, `sorryAx`) and excludes native and
container interfaces. The beta-valued pair fixture also cancels the returned
chain against its existing rebase equality, retaining the same existential
common reduced result and independent removal/insertion lifts. Three runtime
controls distinguish the outer-only intermediate from both endpoints. Native
telescopes, dependent-domain reconstruction, `replaceParams`, inserted
motive/minor typehood and checker/source acceptance remain separate.

`TranslatedRecursorIndexTrace.selectedTelescopeRebasedOfStoredDomains` adapts
that composition to an actual translated index history. It invokes the
stored-domain contraction bridge, preserves chronological/native/virtual and
full-index-array receipts, and inserts the reduced selected telescope into a
larger base. Its freshness premise ranges only over newly allocated suffix
IDs, never retained parameters or the original index prefix. The adapter still
leaves concrete smaller-base construction, inserted motive/minor typehood,
complete binder reordering and source acceptance explicit.
It additionally returns separate typed retained-parameter receipts for the
smaller-to-larger base insertion and the reduced-to-target endpoint weakening;
their lifts are respectively `skipN refl inserted` and
`consN (skipN refl inserted) ids.length`. Neither receipt identifies the old
chronological endpoint with the new endpoint or proves native parameter
telescope reconstruction/substitution.
The adapter also derives a reduced-to-aligned transport at
`consN baseLift ids.length` and returns its retained-parameter agreement with
the chronological endpoint. This historical agreement uses the contraction
lift, never the different reduced-to-target insertion lift.
The returned chronological agreement supports the single-parameter
substitution helpers when their original-body typing/support premises are
supplied; this does not infer those premises from the index trace.
`TranslatedRecursorIndexTrace.selectedTelescopeRebasedBodyOfStoredDomains`
extends the adapter with an explicit old body translation/typehood and
suffix-ID fvar support. It rewrites the final-array suffix to the actual
allocated IDs, derives support in the reduced telescope's exact fvar list,
and returns reduced/new body translations and sort typing together with the
same two retained-parameter transports and chronological agreement; it does
not infer body support from allocation alone.

`TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutedTypeOfStoredDomains`
selects one retained parameter by its supplied list position and composes the
actual-history adapter with native single-parameter type substitution/rebasing.
It requires the exact final-virtual-context argument lookup, original body
translation and sort typing under that argument's actual anonymous domain,
depth-one structural closure and explicit final-array-suffix fvar support.
The proof converts suffix support to the reduced selected telescope's exact
fvar list and rewrites the lookup/body premises through the chronological
endpoint equality. All history, telescope, weakening, context agreement and
retained-parameter receipts remain available. It additionally returns the
selected reduced argument's lookup/translation/typing, substituted closure
and support, original/reduced/target type translations and sort typing, and
three chronological-context comparisons through one existential reduced type.
Old-context comparisons use `consN baseLift ids.length`; target transport uses
the independent `consN (skipN refl inserted) ids.length`. Dependencies retain
the existing logical/typing axioms, persistent-container interfaces and
`Expr.instantiate1_eq`; no new admission/axiom or runtime change is introduced.
This does not reconstruct native parameter telescopes, prove whole-prefix
`replaceParams`, identify a pre-contracted body, prove inserted motive/minor
typehood or establish complete binder ordering/checker/source acceptance.
The focused fixture has 13 proof controls and 14 runtime checks. It pins all
15 history/parameter receipts and 14 substituted-type receipts, applies the
adapter to an actual empty translated history, and separately checks a retained
old prefix with two new chronological suffix IDs, reversed endpoint support,
closure, nested binder protection, selection negatives and distinct lift
cutoffs. An exact eight-axiom manifest audit enforces the stated inherited and
native dependency boundary.
Run `lake env lean tests/InductiveIndexSubstitutionRebase.lean`.

`TranslatedRecursorIndexTrace.selectedTelescopeRebasedSubstitutedPairTypeOfStoredDomains`
applies the strengthened ordered two-parameter proof to the actual history
endpoint. Both selections refer to the supplied retained-parameter list, not
the allocated index suffix. Exact final-virtual argument lookups, raised-inner
typing at the actual inner domain, two-anonymous-binder body translation/sort
typing, depth-two structural closure and explicit suffix-plus-base fvar
support remain premises. The adapter rewrites all lookup/typing/translation
receipts through the chronological endpoint equality and derives support in
the recovered reduced telescope's exact fvar list.
All 15 history/parameter receipts and 25 pair-substitution receipts remain
available, including the actual intermediate body, both reduced arguments,
depth-zero final closure, original/reduced/target type translations and typing,
and outer-only/simultaneous agreements with the common reduced result.
Two appended receipts now expose the actual outer-only semantic chain and
the residual inner equality with the reduced outer argument held fixed, both
in `chronological.vlctx.toCtx`. They are composed from the pure retained-pair
helper after rewriting through the actual chronological endpoint and matching
both reduced argument/type witnesses by exact source lookup uniqueness.
Cancelling the outer chain against the existing rebase equality reconstructs
the existing outer-only comparison with the same existential common reduced
result. All previous 40 receipts retain their positions; the total is now 42.
The changed-context inner substitution is not asserted to be a fixed-context
chain stage, nor is the reduced result identified with contracted syntax.
Both-reduced interpretation typing and agreements stay in chronological
coordinates under `consN baseLift ids.length`; target transport independently
uses `consN (skipN refl inserted) ids.length`. Inner arguments are raised only
after being placed in the chronological context. The supplied body is not
asserted to equal the trace terminal or have its semantic interpretation.
Dependencies retain only the existing logical/typing axioms, three persistent
container interfaces and `Expr.instantiate1_eq`; no new admission/axiom or
runtime change is introduced. This does not reconstruct dependent parameter
domains/native telescopes, prove arbitrary typed-list recursion or native
`replaceParams`, identify separately contracted syntax, prove inserted
motive/minor typehood or establish checker/source acceptance.
Run `lake env lean tests/InductiveIndexPairSubstitutionRebase.lean`.

The focused history fixture has 15 proof controls and 29 runtime checks. It
forwards all 15 history/parameter and 27 strengthened pair receipts, applies
the adapter to an actual empty translated history whose body uses both formal
binders and consumes the new outer chain and residual equality, deriving the
outer-only comparison with the common reduced result by cancellation. It
separately checks a retained prefix with two chronological suffix
IDs, reversed support, intermediate/final closure, discarded-fvar rejection,
nonzero parameter positions, nested-binder protection, swapped order, missing
inner lifting, distinct removal/insertion cutoffs and nonliteral beta arguments
distinguishing original, outer-only and both-reduced endpoints. Its exact eight-axiom
adapter manifest matches the prior actual-history boundary.

`tests/RecursorFieldScope.lean` adds eighteen proof regressions and seventeen
axiom audits for structural context validity/reservation, ordered declaration
extensions, old native lookup preservation, actual field and selected-field
declarations, traversal continuations, coupled RHS scope receipts, sequence
compatibility/position projections, and conditional parent-local receipt
composition. Eight direct helper fixtures cover empty/recursive fields, mixed
visibility and higher-order selection, dependent domains, skipped parameters,
unchecked forall-valued parameter substitution, repeated binder names, and
thirty-three fields under a seeded generator. The seeded reader retains both a
previous local declaration and an unrelated let declaration. Every fixture checks
native declaration shape, ordered recursive selection, and exact context/generator
advancement. Ten rule replays cover empty, recursive, mixed higher-order,
dependent, and thirty-three-field constructors at zero/shifted minor offsets;
they check native field/selection declarations, count bounds, exact RHS recipes,
and rule/minor advancement. Two helper-boundary controls distinguish the retained
reader from the original reader and show native overwrite when reservation is
absent. Zero-fuel and partially allocated traversal failures propagate. These
unchecked helper fixtures do not claim full frontend acceptance or semantic
typing. Audits admit only the existing persistent-array list-push and two map
interfaces where required; all exclude `sorryAx` and expression interfaces.

`tests/InductiveHeaderContinuation.lean` checks derived parameter support, full
parameter/ambient histories, exact parameter-base recovery and WF, shadow-reader
alignment, the typed continuation endpoint, actual accepted constructor/stage
receipts, complete runner projection, and direct compatibility with the existing
shadow constructor-domain receipt theorem. Its exhaustive module audit rejects
module-owned axioms and dependencies outside the inherited header checker,
registration, prefix, constructor-trace, and reset-state footprints. Six native-accepted
fixtures cover shared zero/one/two parameters, aliased reused domains, dependent
second parameters, and accumulated/differing index counts with nonempty
constructor lists under both safety modes. The exact continuation local count,
every parameter lookup, source signature, exact old definition, constructor arity, and complete
recursor registration are checked. Empty batches preserve the empty local model;
invalid constructor returns, captured headers, later parameter-domain mismatch,
duplicate headers, and zero fuel reject. Runtime fixtures use the imported
prelude and do not construct its missing semantic translation. Run
`lake env lean tests/InductiveHeaderContinuation.lean`.

`tests/InductiveConstructorFreshness.lean` checks backwards absence, shadow
absence, registration freshness/distinctness, installed-header exclusions,
native-only and typed-shadow complete-run receipts, and the native projection,
structure-eta, and unit-like barriers. Its exhaustive production-module audit
rejects module-owned axioms, unexpected inherited dependencies, and `sorryAx` outside the two typed shadow
receipts. Seven native-accepted fixtures cover single/multiple constructors,
mutual parents, zero/one/two shared parameters, dependent parameters, and
indices under both safeties. They inspect the actual pre-constructor checkpoint,
confirm every constructor name absent in both stages and globally distinct,
then validate exact old definitions, actual registration, exact constructor
metadata, and full recursor registration. Existing-name, own-header,
other-mutual-header, and repeated-name
controls, including repetition across parents, distinguish successful checking
from rejected registration. Repetition within one parent already rejects during
constructor checking. Empty registration preserves the base.
A local-variable projection fails in both
header stages but succeeds after actual constructor registration; the separate
header-only structure predicate and unit-like helper controls expose remaining
metadata distinctions. Structure-eta and unit-like helpers become available only
after actual constructor registration in their positive controls. These staging
differences are not kernel discrepancies.
Runtime fixtures use the imported prelude without its missing semantic
translation. Run `lake env lean tests/InductiveConstructorFreshness.lean`.

`tests/InductiveHeaderCheckerTransport.lean` checks the derived source-indexed
lookup bridge, changed-header constructor exclusions, untouched-record and
delta equality, public constant checking/inference transport, and complete
unfolding transport. Its exhaustive production-module audit rejects every
module-owned axiom, unexpected inherited dependency, and `sorryAx`. Five
native-accepted batches cover singleton/mutual headers, zero/one/two parameters,
indices, and universe parameters under both safeties and primitive flags. Every
empty checkpoint preserves the same lookup bridge and checker behavior. Every
non-header record is compared exactly, every changed record is its precise axiom
view, and all future constructors are absent before accepted actual checking and
eventual registration. Default and seeded native states cover both inference
caches, normalization caches, the generator, equivalence manager, failure set,
and universe-unfolding cache; every result state component is compared. Constant
queries cover source headers, old inductive/constructor rows, safe/universe/
partial/unsafe definitions, missing names, and universe-count mismatches.
Core/application unfolding tests positive universe instantiation, cache hits,
misses, and unchanged cache data; zero fuel rejects even seeded inference hits.
Runtime fixtures use the imported prelude without its missing semantic
translation. These are base-case transport regressions, not unrestricted
constructor-check or inductive soundness tests. Run
`lake env lean tests/InductiveHeaderCheckerTransport.lean`.

`tests/InductiveHeaderNormalizationTransport.lean` checks accepted-prefix bind
composition with distinct error types, direct guards without WHNF premises,
and native proposition testing with the returned inference state. Its exhaustive
audits cover both new production modules, including generated declarations, and
reject module-owned axioms, unexpected dependencies, and `sorryAx`. Native-accepted
singleton/mutual header batches and the empty checkpoint cover both safety and
primitive flags before future constructors are registered. Default/seeded states
exercise every cache bank, the name generator, equivalence-manager map/union-find
data, failure set, and unfolding cache; complete states are compared. Stateful
callbacks exercise normalized sort/forall guards, wrong forms, recursion errors,
two-stage proposition testing, true/false equivalence-manager updates, and the
string-expansion projection branch across different readers. Actual native
callbacks cover aliases, old constructors and parameter offsets, out-of-range
fields, nonconstant heads, changed headers, missing future constructors, string
literals, and both cheap flags. Full normalization of `Nat.succ Nat.zero` produces
a literal while cheap core normalization retains the constructor application;
the projection tests preserve that intentional difference. Imported-prelude
fixtures do not supply its missing semantic translation or prove general callback
transport. Run `lake env lean tests/InductiveHeaderNormalizationTransport.lean`.

`tests/InductiveHeaderRecursorTransport.lean` checks automatic original-parent
stability at the existing typed continuation, and exhaustively audits both raw
transport modules against their explicit logical/persistent-lookup footprints.
Native-accepted singleton/mutual batches exercise both safety and primitive flags
before constructor registration, with default and fully seeded checker states.
Stateful callbacks cover all K/structure early exits, matching/mismatching parents,
proposition rejection, constructor comparison success/failure, and metavariable
scans that reject indices but permit parameter-only metavariables. Actual native
methods convert a local equality proof through `Eq.rec` and eta-expand a local
product; complete result states are compared. A negative control manually injects
identical malformed recursor records with a newly staged parent into both native
environments. With identical raw callbacks, actual K/reduction results differ
from the shadow despite exact recursor-record preservation. This is evidence that
old-parent metadata closure remains a real obligation, not a kernel discrepancy
or a native-accepted malformed declaration. The fixture does not execute the
unreachable structure fallback, construct semantic prelude translation, or prove
unrestricted recursive transport. Run
`lake env lean tests/InductiveHeaderRecursorTransport.lean`.

`tests/InductiveHeaderReductionTransport.lean` exhaustively audits the new raw
module and checks native-accepted singleton/mutual header checkpoints across both
safety and primitive flags, before constructor registration. It derives the
quotient-gate equality from native registration and axiom-view preservation and
projects stable parents from original-parent closure and the existing value
frame. Stateful callbacks update every cache, generator, equivalence map/union
find, failure set and unfolding cache; default/seeded states and distinct readers
compare every final field. Raw synthetic recursor records exercise exact field
and universe guards, missing rules, level substitution, skipped parameter/index
arguments, trailing fields and overapplication, K true/false comparisons,
natural/string literals, structure expansion, proposition rejection and parent
mismatch. These deliberately raw records and manually varied quotient gates are
control-flow fixtures, not claims of native-accepted malformed declarations or
kernel discrepancies. A deliberately mismatched quotient-gate control produces
different wrapper results despite unchanged constant lookups, and an actual
callback rejection can coexist with a successful shadow without violating the
directional contract. Quotient lift/ind fixtures cover saturation, constructor
arity, trailing arguments, exhausted callbacks and quotient-first dispatch;
distinguishable full/core callbacks verify cheap flags are forwarded and that
quotient normalization remains full. Actual `Methods.withFuel` reduces native
`Nat.rec`, local-proof `Eq.rec`, and local-product `Prod.rec`, both directly and
through the wrapper at all four cheap-flag combinations. The real native methods
first check each complete application with `inferOnly := false` in both views.
Subsequent normalization
checks their expected results. Imported-prelude fixtures do not supply semantic
prelude translation, and raw state equality is not semantic state WF. Run
`lake env lean tests/InductiveHeaderReductionTransport.lean`.

`tests/InductiveHeaderWHNFCoreTransport.lean` exhaustively audits the raw core
module and checks native-accepted singleton/mutual header batches across both
safety/primitive flags before future constructor registration. All four cheap
flag combinations run in default/seeded states and alternate readers, comparing
every inference/normalization cache, generator field, equivalence map/union-find,
failure set and unfolding cache. Scripted stateful callbacks cover every easy
expression tag, free-variable misses/parameters/local lets (including hidden
nondependent values), outer metadata, cache hits/misses, exact under/full/over-
applied beta inputs, every non-lambda rebuilt head, unchanged-head recursor
miss/success, zeta, projection success/out-of-range and string expansion.
Independent callback counts and outer-cache assertions enforce the actual
branch-specific policy, including cache hits under cheap flags and no save on
local-let free variables or successful unchanged-head recursor paths. Exhausted
callbacks test failures, and an actual rejection can coexist with a successful
shadow. Deliberately different local let values produce different results even
with agreeing environment classifications, showing that local-context equality
is a real premise; this is not a kernel discrepancy. Actual `Methods.withFuel`
first checks complete local-let, beta, zeta, product-projection, `Nat.rec`, local-
proof `Eq.rec` and local-product `Prod.rec` applications in both views, then
normalizes through the real core at all flag combinations and checks the full
normalization result. A bare `Nat.zero` retains its constructor form, unlike a
computed natural operation yielding a literal; the expectations preserve that
native distinction. Imported-prelude tests do not provide semantic prelude
translation, and equal raw state fields do not assert semantic state WF. Run
`lake env lean tests/InductiveHeaderWHNFCoreTransport.lean`.

`tests/InductiveHeaderWHNFTransport.lean` exhaustively audits all 105 owned
production declarations, including generated ones, allowing only `propext`,
`Classical.choice` and `Quot.sound`; it rejects admissions, module-owned axioms
and persistent-map interface axioms. Native-accepted singleton/mutual header
staging runs across both safety/primitive flags, before future constructor
registration, in default/seeded states. Distinct methods and readers compare
every cache, generator, equivalence-map/union-find, failure-set and unfolding
field. Stateful callback counts cover all ten binary natural operators,
successor, both Boolean outcomes, literal/`Nat.zero` operands, first/second
literal-extraction rejection, operand errors and the exponent-cap boundary.
Natural-miss controls remove the operator definitions in both raw views so that
native delta reduction cannot obscure the tested miss; they do not assert
semantic environment WF or native acceptance of malformed declarations.
Easy inputs and missing/ordinary local parameters ignore even seeded caches and
zero fuel; eligible cache hits, including local lets with hidden nondependent
values, bypass callbacks and budget checks. Nested metadata uses only the
peeled input's entry. Definition chains check both budget selections, larger
shadow budgets, insufficient-budget rejection, zero-universe cache bypass,
polymorphic unfolding-cache hits, wrong universe arity and unsafe-definition
misses. Callbacks deliberately insert a stale outer cache entry during an
unfolding chain: the next loop iteration must not reread it, and the native
final insertion must overwrite it. Actual `Methods.withFuel` at distinct
sufficient depths checks complete local-let, beta, zeta, natural-operation,
product-projection, `Nat.rec`, local-proof `Eq.rec` and local-product `Prod.rec`
applications in both views before full normalization. These imported-prelude
tests are not semantic prelude translation or a general recursive-method
transport proof. Run `lake env lean tests/InductiveHeaderWHNFTransport.lean`.

`tests/InductiveHeaderWHNFMethodTransport.lean` exhaustively audits the owned
recursor, reduction and normalization-method-step declarations. All new and
generalized declarations allow only `propext`, `Classical.choice` and
`Quot.sound`; the unchanged original-parent bridge retains its pre-existing
`Lean.PersistentHashMap.findAux_isSome` exception, which is not used by the new
raw module. Proof fixtures apply the literal
arbitrary-normalizer theorem, the successor step and its discharged depth-one
specialization. Native-accepted singleton/mutual header batches exercise both
safety modes and primitive policies, default/seeded complete states, different
eager flags, selected normalization budgets and recursion reader budgets.
State-mutating callback controls pin every K/non-K, true/false comparison and
cheap-rec/cheap-proj combination, exact callback counts and all ordered method
tags, including K type normalization; all state fields are compared. Further
controls cover beta, zeta, projections, successor/binary arithmetic, native recursive results,
depth-zero errors and shallow normalization. Actual header-stage recursor
records retain their native origins and old inductive parents; a raw inserted
new-parent recursor still has differing inductive/axiom parent tags. Synthetic
record/callback controls and imported native execution do not establish semantic
metadata or cache/state WF, prelude translation, or by themselves the simultaneous
inference/comparison successor steps supplied by the recursive module.
Run `lake env lean tests/InductiveHeaderWHNFMethodTransport.lean`.

`tests/InductiveHeaderRecursiveTransport.lean` exhaustively audits every owned
recursive-transport declaration, permitting only `propext`, `Classical.choice`
and `Quot.sound`. Proof fixtures apply the all-depth inference theorem, public
checked inference/type checking, reader opening followed by eager adjustment,
and the before-constructor environmental-frame derivation. Native-accepted
singleton/mutual/indexed batches exercise both safety modes, primitive policies
and eager policies with default/seeded complete states. Runtime gates check exact
entered-header constructor names, constructor freshness, old native constructor
membership/parent stability, recursor shadow parents and quotient alignment.
Depth-zero, shallow and
deeper methods exercise every native field, both inference modes, all cheap
flags, dependent lambda/forall/let telescopes, checked eager applications,
old structure projections, arithmetic, strings and binder comparisons. Public
checking/type formation and wrapper equality pin accepted native results; all
state fields are compared directionally. A registered singleton unit-like
family accepts the actual native comparison while its shared-constructor axiom
shadow returns false, retaining the environmental-frame barrier. Runtime
imported-prelude and deliberately seeded-cache controls do not establish
semantic prelude translation or cache/state WF, and do not discharge the
remaining actual staged native metadata premises.
Run `lake env lean tests/InductiveHeaderRecursiveTransport.lean`.

`tests/InductiveHeaderInferenceTransport.lean` exhaustively audits all 145 owned
production declarations, including generated declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. It rejects admissions, module-owned
axioms and expression/persistent-map interface axioms. Native-accepted singleton
and mutual header staging runs at both safety/primitive flags before future
constructor registration, in default/seeded states and distinct sufficient
method depths/fuel readers. Every cache, generator, equivalence-map/union-find,
failure-set and unfolding field is compared. Scripted application cases cover
empty/under/full application, dependent delayed substitution, normalized type
boundaries, reset pending indices, callback counts and asymmetric rejection.
Inference tests distinguish both caches, outer metadata hits, inner/wrapper
insertion, stale callback insertion overwritten only in the selected mode,
loose-variable rejection before seeded hits, closed metavariable/missing-local
hits and cold failures. Checked applications cover direct and normalized forall
types, accepted/false comparison, exact eager-head arity and outer-reader
restoration. Different local types, undefined universe readers and incompatible
safety readers demonstrate that header lookup agreement cannot replace the
explicit reader premises. Literal signature-presence controls remove the
native Nat/Char/String keys in both raw views, distinguishing inference-only
success from checked rejection; these modified contexts are not semantic WF or
native-accepted malformed declarations. Actual `Methods.withFuel` first checks
complete lambda/forall/let, beta, product construction/projection, natural and
eager-wrapper terms in both views, then tests cold and warm inference in both
modes. These runtime controls do not derive the telescope/projection receipts,
semantic prelude translation or a general mutually recursive transport theorem.
Run `lake env lean tests/InductiveHeaderInferenceTransport.lean`.

`tests/InductiveHeaderTelescopeTransport.lean` exhaustively audits all 125 owned
production declarations, including generated declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. Native-accepted singleton/mutual
header staging covers both safety/primitive flags before future constructor
registration, default/seeded states, existing outer local declarations,
distinct eager/fuel readers and sufficient method depths. Raw allocation checks
verify fresh IDs, binder/value metadata, the native let nondependent default and
outer-reader restoration. Scripted dependent telescopes compare all cache,
generator, equivalence-map/union-find, failure-set and unfolding fields. They
exercise post-check fresh names, both inference modes, direct/normalized sort
checks, empty telescopes, terminal reverse instantiation/beta reduction,
accumulated forall levels, used/unused let closure, comparison insertion,
deliberately failing unreached callbacks and rejected domain/comparison controls.
The forall terminal error retains its native uninstantiated source expression
and reached local reader. Complete
native methods and whole inference entries check implicit lambda, forall, let,
dependent let closure and newly staged parent domains/local witnesses in both
views. The runtime fixtures do not construct
semantic prelude translation, semantic state WF or automatic recursive method
receipts. Run `lake env lean tests/InductiveHeaderTelescopeTransport.lean`.

`tests/InductiveHeaderProjectionTransport.lean` exhaustively audits all 175 owned
production declaration, including generated declarations, permitting only
`propext`, `Classical.choice` and `Quot.sound`. Native-accepted singleton/mutual
staging, including a nonzero-index family and native-checked explicit projection
definitions, covers matching safe/unsafe declarations and both primitive flags,
default/seeded states and distinct eager/fuel readers and method depths. Scripted
Prod/Sigma projections exercise exact parameter inputs, both field-loop branches,
earlier-projection substitution, every complete state field, callback counts,
proposition gates and deliberately unusable checked-inference/comparison/core
methods. Wrong heads, arities, constructor counts and field indices reject.
Complete native methods and inference entries check Prod, Sigma, Subtype and And
projections in both modes; Exists projections reject the native propositional
dependent-field restriction. New-parent projections reject before constructors,
then succeed in helper and whole-inference entries only in the registered actual
view, not the axiom shadow. Isolated raw metadata controls show that constructor
signature equality suffices despite
different ignored record tags, whereas changing a parent's inductive tag blocks
projection even with identical retained constructor signatures. Those controls
are not native-accepted malformed environments or semantic-WF claims. These
fixtures do not construct semantic prelude translation or automatic recursive
method receipts. Run `lake env lean tests/InductiveHeaderProjectionTransport.lean`.

`tests/InductiveHeaderComparisonTransport.lean` exhaustively audits all 182 owned
production declarations, including generated and private declarations, permitting
only `propext`, `Classical.choice` and `Quot.sound`. Native-accepted singleton,
mutual and nonzero-index staging and explicit parent-typed identity definitions
cover safe/unsafe and primitive flags, default/seeded complete states, existing
outer locals and distinct eager/fuel readers and method depths. Stateful scripts
pin same/unequal domains, rejected domains, dependent and closed bodies, nested
dependent binder types, nonempty initial substitutions, mismatched binder tags
and reader restoration. Traces check exact instantiated inputs, fresh-local types,
scope and callback/allocation counts while comparing every state field. Quick
tests cover both hash modes, cache hits, stateful misses, hash-guard bypass of a
stored equivalence, sort/literal/undefined results and reached lambda/forall/
metadata callbacks. A same-ID metavariable hit avoids the retained panic fallback;
no distinct-metavariable panic path is evaluated or claimed impossible. Native
argument comparison runs right-to-left and omits head comparison, while native
application comparison checks heads then arguments left-to-right. False prefixes,
unequal arities, nonapplications, empty/exhausted native loops and deliberately
unusable unreached methods preserve their original branch policy. Actual recursive
methods compare beta-reduced dependent lambdas, forall-body let aliases,
applications, metadata and staged parent domains. These runtime fixtures do not
construct semantic prelude translation, semantic state WF or automatic recursive
method receipts. Run `lake env lean tests/InductiveHeaderComparisonTransport.lean`.

`tests/InductiveHeaderComparisonHelperTransport.lean` exhaustively audits all 199
owned production declaration, including generated/private declarations, permitting
only `propext`, `Classical.choice` and `Quot.sound`. Native-accepted singleton,
mutual and nonzero-index staging and explicit parent-typed identities cover both
safety/primitive flags, default/seeded complete states and distinct eager/fuel
readers and method depths. Scripts check exact eta-expanded lambdas, direct and
normalized forall types, false/missing eta paths and symmetric order; all five
proof-irrelevance callbacks and the nonproposition gate; zero/successor offset
inputs and the absence of wrapper equivalence insertion; empty/ASCII/Unicode
string expansion, false comparisons and exact head/universe/overapplication
rejection; structure metadata/arity gates, both projected fields, false prefixes,
nullary field loops and unit-like metadata rejection. Every cache, generator,
equivalence-map/union-find, failure and unfolding field is compared, with exact
callback counts and input/reader traces. Actual recursive methods exercise
function eta, product eta, proof irrelevance, unit-like comparison, natural offsets
and string constructors. Fresh unit-parent constructor absence rejects in the
actual view while its shadow may return false; indexed parents return false in
both views without demanding constructors. After registration, actual unit and
structure eta helpers accept where an axiom-shadow view with the same raw
constructors returns false. Sharing raw constructor records does not assert
semantic WF or native acceptance of that shadow. These fixtures do not construct
semantic prelude translation, semantic state/cache WF or automatic recursive
method receipts. Run `lake env lean tests/InductiveHeaderComparisonHelperTransport.lean`.

`tests/InductiveHeaderLazyDeltaTransport.lean` exhaustively audits all 213 owned
production declarations, including private/generated declarations, allowing only
standard logical axioms. Twelve native-accepted singleton/mutual/nonzero-index
header staging combinations cover both checker safety modes and primitive
authorization settings, each with default/seeded complete states and distinct
method-depth/lazy-delta readers. Seven native-accepted definition fixtures cover
regular hint order, equal-height distinct records, same-record application fast
paths, abbreviation/opaque regularity rejection and differing universe lists.
Scripts compare actual/shadow complete states and exact callback input, order,
cheap flags and local-reader traces; they also replay both proved factorizations.
Projection success takes priority without unfolding the delta side; projection
miss preserves the normalization callback's state before the opposite unfold.
Argument success skips all unfolding/failure insertion; rejection retains the
callback state before symmetric failure caching and ordered unfolding. Distinct
same-hint records reject the pointer guard without inserting a universe failure;
a cached quick hit across distinct expression hashes skips the body, pinning
`useHash := false`. Tests pin
quick true/false/undefined outcomes, `mdata` body core calls, native recursive
methods, zero/one/larger fuel, offset priority, both natural sides, open/closed
natural gates, reader-policy mismatch and unsupported native-reducer errors.
Directional failure controls allow shadow success where the actual callback or
budget rejects; error-action equality is not asserted. Malformed universe arity
can still reach the native `get!` fallback, whose unreachability is not assumed
or established by a panic-producing passing fixture. Runtime prelude imports do
not provide semantic prelude translation, semantic state/cache WF or automatic
recursive method receipts. Run `lake env lean tests/InductiveHeaderLazyDeltaTransport.lean`.

`tests/InductiveHeaderDefEqCoreTransport.lean` exhaustively audits all 229 owned
production declarations, including private/generated declarations, allowing only
standard logical axioms. Twelve native-accepted singleton/mutual/nonzero-index
header staging combinations cover safe/unsafe and primitive-policy modes with
default/seeded complete states and distinct reader recursion/lazy-delta budgets.
Scripts replay the actual complete core and its proved entry factorization,
checking exact callback inputs/order, cheap flags, local-reader traces and every
state field. Initial quick true/false results finish despite zero method/fuel
budgets; `mdata`/lambda/forall quick bodies retain wrapped core calls. Boolean
shortcut success/miss, closed/open eager gates, skipped unchanged-pointer recheck,
hash-guarded initial queries and non-hash normalized cached hits remain distinct.
Proof irrelevance, real delta unfolding, full-normalization restart, index-only
projection comparison, application head/argument order and false prefixes,
forward/backward function eta, product structure eta and PUnit unit-like results
are pinned. Changed full normalization calls the raw core without wrapper
equivalence insertion. Existing `String.ofList` delta unfolding precedes string
fallback; a raw no-value signature control exposes that fallback in both views.
The control is not a native declaration-history extension or semantic-WF claim.
Before constructors, actual nullary-parent unit metadata errors while its axiom
shadow returns false; indexed parents return false in both complete cores. After
registration, the actual core accepts unit metadata where an axiom shadow with
the same raw constructors rejects. Thus complete-core transport still needs its
reached metadata receipts; header lookup agreement alone is insufficient.
Directional callback rejection permits shadow success, and native recursive
methods independently check literal, delta and string Boolean outcomes and
complete states. No panic-producing fixture asserts unreachable control flow.
These runtime controls do not establish semantic prelude translation, semantic
cache/state/local-context WF or automatic recursive method receipts. Run
`lake env lean tests/InductiveHeaderDefEqCoreTransport.lean`.

`tests/InductiveHeaderAxiomView.lean` checks the exact header signature/value
bridge, absence and optional-value agreement, empty shadow history, strong
context/local-model preservation, reset-state WF, raw registration, all-header derived staging,
and complete runner projection. Its exhaustive production-module audit rejects
module-owned axioms and dependencies outside the inherited registration,
header-checking, and primitive-interface footprints. The nine tag/signature/view
contracts reject `sorryAx`; semantic replay and context-model extension retain
the existing semantic metatheory admissions, and the three checked stage
projections also inherit the checker admissions. Seven native-accepted fixtures
cover zero/one/two parameters,
mutual headers, indices, nonempty constructor lists, retained definition aliases,
and universe parameters under both safety and primitive-declaration flags. Every
lookup signature and every exact old record is compared in both directions;
ordinary constructor fixtures check in both stages and full actual runs reach
recursor registration. Empty batches preserve the base. Duplicate/colliding
names, later domain mismatch, and fuel controls reject. A native-accepted
one-field structure has equal type/value signatures in its actual and axiom
environments after constructor registration, but its projection checks only in
the actual environment. This is a negative transport control, not a kernel
discrepancy or an assertion that the header-only stage cannot be transported.
Run `lake env lean tests/InductiveHeaderAxiomView.lean`. Imported-prelude fixtures
do not construct the missing semantic prelude translation.

`tests/InductiveMutualHeaderTyping.lean` contains eight proof regressions for
accepted parameter equality, typed reused-body substitution/normalization,
general header reader models, closed-source strengthening, all-header WF,
whole-array checker registration, full runner projection, and rejection of a
missing parameter-support model. The exhaustive production-module audit rejects
module-owned axioms and dependencies outside the inherited checker, canonical
annotation/context bridge, source guard, strengthening, and registration
interfaces; inherited `sorryAx` is explicit. Seven native-accepted mutual
fixtures cover zero/one/two parameters, accumulated and differing index counts,
aliased/beta-equivalent reused domains, annotations, repeated binder names,
dependent second parameters, and differing binder visibility. Both safety modes
retain every exact source header and the checked seed definition through header
registration and full runs, which must reach recursor registration. Empty
header batches succeed without projecting a default first element. Later
parameter-domain mismatch, ill-shaped terminal, captured source-variable, and
fuel controls reject; native typed lookup rejects an absent unchecked parameter.
The imported-prelude fixtures do not construct a semantic `TrEnv` model. Run
`lake env lean tests/InductiveMutualHeaderTyping.lean`.

`tests/InductiveHeaderTyping.lean` contains six proof regressions for accepted
sort typing, the arbitrary-continuation first-header theorem, closed-context
source WF, singleton checker registration, final typed lookup/WF, and the actual
complete runner. Its exhaustive production-module audit rejects module-owned
axioms and dependencies outside the inherited checker, source-guard, type
conversion, and header-registration interfaces; inherited `sorryAx` is explicit.
Eleven native-accepted fixtures cover direct and aliased sorts, beta reduction,
metadata wrappers, a Pi-valued alias, parameter domains with aliases/reduction,
indices, dependent parameters/indices, and mutual headers. Both safety modes
retain the exact original header types and seed definitions through header
registration and complete runs, which must reach recursor registration.
Separate controls show that successful standalone expression checking is not
enough: terms and non-sort terminals reject as headers. Parameter-count, fuel,
and source-variable failures also reject. Runtime use of the imported prelude
does not construct its missing semantic `TrEnv` model. Run
`lake env lean tests/InductiveHeaderTyping.lean`.

`tests/InductiveValueFrame.lean` contains eight proof regressions and six axiom
audits for recursor registration, full runner composition, no-value restoration
traces, the safe public frontend, both dispatch flags, and final value-record
provenance. The audits exclude `sorryAx` and any new interface assumptions;
even the full public frontend uses only standard logical axioms and the three
existing persistent-map interfaces. Eight native-accepted direct/nested fixtures
cover empty, enumeration, recursive, mutual, parameterized nested families, and
an empty companion datatype. Each stages both runner safeties and exercises
both public dispatch flags plus the direct public API. Every result retains
all initial records, introduces no value-bearing records, and keeps a checked
safe definition's exact record and delta reduction. Nested cases additionally
test explicit restoration and assert that preprocessing generated auxiliaries.
Constructor-name and recursor-name collisions with existing safe definitions,
and zero preprocessing fuel, are rejected under both dispatch flags. Run
`lake env lean tests/InductiveValueFrame.lean`.

`tests/RecursorRegistration.lean` contains fifty-nine proof regressions and forty-three axiom
audits for suffix map validity, successful-result extraction, exact old lookup
preservation, preservation of a constructor-registration certificate's
header/constructor metadata, complete recursor records, source rule receipts,
conditional declared counters, successful rule-source name/order/count/state
shape, installed rule-shape projections, datatype-prefix equations, exact offset
receipts, compatibility with the prior metadata contract, arbitrary field-count
continuations, positional raw/registered field counts, generated minor-prefix
alignment, local/flattened bounds, optional/defaulting lookup agreement,
positional RHS formation, exact nested-lambda/application recipes, local-minor
source projections, ordered recursive-field selection, exact remaining-value
counts, counted-receipt compatibility/bounds, and free-variable field/selection
shape with coupled counted recipe witnesses.
An empty-array proof makes the vacuous
counter boundary explicit even with a nonzero declared parameter count.
Seven direct raw-field fixtures cover zero/one/two parameters, truncated short
inputs, mixed binder visibility, and thirty-three fields, with a zero-fuel
failure boundary. A non-free-variable parameter control demonstrates why the
explicit premise is necessary: substituting a forall expression into the terminal
parameter variable exposes one field, although raw arity minus parameter count
is zero. This unchecked internal statistics input is outside the theorem's
scope, not a public frontend divergence. The three new traversal/generator/
source audits use only the existing `Expr.instantiate1_eq` interface beyond
standard logical axioms; the positional projection uses only logical axioms.
Eight direct argument-count fixtures cover empty and fully recursive selections,
mixed ordinary/recursive/higher-order fields, skipped parameters, shifted
starting indices with prefilled values, terminal and beyond-terminal indices,
and thirty-three selected fields. Both constructor selection and recursive-value
generation retain their zero-fuel failures. Every runtime receipt checks the
ordered selected-field sublist, exactly one value per selected field, and the
bound by its corresponding rule's field count. The eight new traversal/receipt/
sequence/source audits use only standard logical axioms. Prefilled/shifted
iterator tests establish the general count equation, not the final generator's
zero-initialized argument bound for arbitrary preexisting values.
Eight direct field-shape fixtures cover empty and recursive fields, mixed binder
visibility with higher-order selections, skipped parameters, constant/forall
parameter substitutions outside the raw-arity theorem's free-variable premise,
repeated binder names, and thirty-three fields under a seeded name generator.
Two helper-boundary controls show why atom shape is not a scope theorem: a
generated field cannot be inferred in the original reader after its binding
continuation ends, and a generated recursive value need not be a free-variable
atom. These are intentional internal controls, not frontend divergences or
kernel discrepancies. Zero-fuel failure propagates. All argument-count and
installed-receipt replays now also check field and selected-field atom shape.
Nine new array/traversal/receipt/sequence/source audits use only standard logical
axioms. The audit batch is factored into a bounded helper to keep the enlarged
test within Lean's default elaboration recursion limit, without raising it.
Eight direct source-shape fixtures exercise zero and shifted initial minor
indices, a zero-fuel empty parent with zero/nonzero state, reversed constructor
order, and repeated constructor names. They check exact name sequences, rule
counts, state advancement, and zero-field RHS recipes at shifted minor counters
without assuming semantic typing or registration
acceptance of the low-level inputs. The four new shape/count/source-projection
audits use only standard logical axioms, excluding `sorryAx` and all expression,
map, or guarded-arity interfaces.
Eight direct minor-indexing fixtures cover empty and all-empty batches, reordered
parents, empty leading/middle/trailing parents, thirty-three constructors,
nonzero offsets around a large parent, and repeated non-free-variable minor
expressions. Every fixture checks saturated prefix lengths beyond the array
size. Two deliberate unchecked controls demonstrate that equal aggregate counts
cannot replace the per-parent count premise and that an out-of-range local
position may instead address the next parent's flattened entry. These are
mathematical contract boundaries, not frontend divergences. Four new indexing
audits use only standard logical axioms. All successful low-level and checked
generation fixtures now independently check local bounds, flattened bounds,
optional presence, and exact expression selection.
Thirty-one successful low-level traversals cover
empty input, an empty datatype, multi-datatype batches with an empty middle
parent, both K/safety flags and primitive-name policies, elimination levels,
and zero fuel with no rules. They check generated record fields, closure,
exact minor selection across datatype boundaries, imported constants including
existing recursors, and unchanged quotient state. Every exact record now checks
replayed starting/ending indices against its constructor-prefix offsets, and each
traversal checks the final offset against the aggregate constructor count. Five
new fixtures cover reordered batches, empty leading/middle/trailing parents,
consecutive empty parents, a zero-fuel all-empty batch, and thirty-three
constructors. The five new prefix/compatibility/source-projection audits use only
standard logical axioms; the new suffix audit uses the existing three map
interfaces. An unsafe-context/safe-record
control confirms that suffix record safety uses its explicit argument. Three
freshness rejections cover an imported recursor name, a late imported collision,
and repeated datatype names; one rule-generation fuel failure propagates before
insertion. The low-level fixtures supply explicit local binders and do not claim
semantic typing or complete declaration acceptance. Existing full-run fixtures
exercise the extracted suffix through the actual checking/generation path.
Every successful low-level record now also checks its full specification,
including the exact abstracted/inferred type, and replays the rule source with
the threaded minor index. Each installed rule independently replays the RHS
recipe through the field/recursive-value traversals using its parent-local minor,
not the generator's flattened selection. A deliberate swapped-local-minor
control verifies that abstraction does not hide an incorrect positional choice;
this is an oracle control, not a kernel discrepancy. Four new formation/source
audits use only standard logical axioms. Sixteen additional fixtures execute the actual checked
header/constructor prefix, information generation, and registration suffix;
they cover empty inputs/constructors, recursive/higher-order fields, one/two
parameters, mutual/indexed types, seeded contexts, universes, unsafe generation,
primitive policies, a tight fuel bound, a propositional singleton, and a
one-parameter constructor with thirty-three mixed-visibility fields, a mixed
five-field constructor with three selected recursive arguments, and thirty-three
fully recursive fields.
Each fixture also executes the complete runner from the same original context.
Every installed record from both executions is compared
field-for-field with its specification, including exact rule constructor/field/
RHS data and replayed minor advancement, counted free-variable local-minor RHS
receipts, ordered raw field counts, and
actual constructor-record field counts. Both outputs preserve constructor-stage
lookups. These generated parameter/motive/minor/
index alignments are runtime regressions; the separate count-generation proofs
below now discharge the conditional theorem's motive/minor premises, while
index-binder alignment remains unproved. Both suffix audits use the existing
three map interfaces; both metadata projections use only standard logical axioms, and all
audits exclude `sorryAx`.

`tests/InductiveRunPreservation.lean` adds sixteen proof regressions and twelve
axiom audits for arbitrary recursor-information continuations, returned frames,
complete-run registration, final map validity and old lookups, final exact
header/constructor metadata, parameter alignment, and preservation from the
unchanged positivity root, plus generated per-datatype and aggregate motive/minor
counts and composition with actual recursor registration. Thirty-six successful
information-generation count/frame fixtures
cover empty input, no constructors, recursive/higher-order fields, one/two
parameters, mutual/indexed types, default/seeded local contexts, both primitive
policies, universe parameters, nested-header metadata, and unsafe generation.
Five new fixtures add an empty middle datatype, a reordered mutual batch,
thirty-three constructors, empty input with zero fuel, and an empty constructor
list with one unit of fuel.
They inspect all five immutable frame fields, imported/datatype/constructor
lookups, quotient state, local-context/fresh-name growth, exact index/minor
counts, aggregate minor count, and availability of all generated local binders.
Two boundaries check
zero-fuel rejection and propagation of an arbitrary continuation failure. The
frame/count/getter audits and all certificate projections use only standard
logical axioms;
the generation/registration count audit uses the existing three map interfaces;
the two runner audits use the existing three map and six guarded-arity
interfaces. Every audit excludes `sorryAx`. Adjacent complete-run fixtures
remain the executable smoke checks for the final installed recursors and rules;
no semantic recursor or full frontend soundness claim is added.

`tests/ConstructorBatchArity.lean` adds four proof regressions and two axiom
audits for full-batch checking, successful-result projection, arbitrary
environment replacement, and checked-type/batch composition. Both audits
exclude `sorryAx` and use exactly the guarded inner loop's existing interfaces.
Thirty-eight executable batch outcomes follow checked types and datatype-header
registration in safe and unsafe contexts. They cover empty constructor/type
batches, zero/one/two parameters, dependent fields, indexed results, mutual
occurrences, and a middle datatype without constructors. Rejections include
duplicate names within a parent, too few or swapped parameters, missing indices,
ill-typed or open/metavariable source types, mismatched parameter domains, wrong
return parents in the last datatype, and exhausted constructor fuel. Constructor
names shared by distinct parents are deliberately accepted at the checker-only
stage; registration would reject their global collision. No constructor
registration or malformed field-count assertion is executed by these fixtures.
Eight additional outcomes exercise the exact checked-type/full-batch composition
against imported `Nat`/`Bool` headers and a universe-polymorphic `List`, including
duplicate-name rejection. This is runtime evidence against the imported prelude,
not its semantic environment translation.
Focused executable replay checks 58 declarations in `Verify.ConstructorParams`,
assuming its imported dependencies are correct.

`tests/ConstructorMetadata.lean` contains six proof regressions and three axiom
audits for standalone registration, checked-batch/register composition, the
checked-type continuation, preservation of arbitrary old entries, exact records,
and nontruncating field counts. Standalone registration uses only standard logical
axioms and the three existing persistent-map interfaces. Both compositions
additionally use the guarded arity theorem's equality, instantiation, and
free/metavariable-flag interfaces. All three audits exclude `sorryAx`.
Twenty-six executable staged outcomes cover empty batches, zero/one/two
parameters, dependent fields, indexed results, universe parameters, mixed binder
annotations, and per-parent counter resets through a mutual batch with an empty
middle parent. Every successful case checks all constructor metadata, the field
sum, and preservation of datatype headers and sampled imported constants.
Rejections cover within-parent duplicates, cross-parent collisions that reach
registration, existing imported-name collisions, and insufficient parameters.
Safe nonpositive occurrences are rejected and their unsafe versions register as
intended. Six further outcomes exercise the exact checked-type/check/register
composition against imported `Nat` and polymorphic `List` headers, including
duplicate rejection. No malformed constructor field-count assertion is executed,
and no kernel discrepancy is reported. Header registration in the staged runtime
fixtures does not establish that step's semantic translation prerequisites.
Focused executable replay checks 29 declarations in `Verify.ConstructorMetadata`,
assuming its imported dependencies are correct.

`tests/InductiveMetadata.lean` adds twelve proof regressions and four axiom audits for
standalone header registration, the fully composed prefix, exact header records,
old-entry preservation, numeric/name-list projections, and the conditional prefix
contract from an empty concrete environment. Additional proofs check declared
parameter alignment, extract equal counts from actual record lookups, and handle
nonempty prefixes and proof-only empty prefixes with arbitrary declared counts.
All audits exclude `sorryAx`.
Forty-two executable outcomes cover safe/unsafe contexts, empty batches,
zero/one/two parameters, dependent fields, direct recursive and reflexive
signatures, indexed results, universe parameters, and mutual batches with empty
middle parents. A mutual fixture records distinct index counts `[2, 0, 1]` and
another copies a nonzero nested count. Seeded contexts use a preexisting local,
nondefault fresh-name prefix/index, and primitive authorization. Accepted cases
check every final header and constructor field, alignment with the declared
parameter count, field-count sums, original-entry
preservation, and absence of recursors. Rejections include duplicate/existing
header names, duplicate constructors, constructor names colliding with newly
registered headers or imported entries, insufficient parameters, wrong returns,
and exhaustion in the header or constructor traversal. These are numeric
prefix tests; no malformed constructor field-count assertion is executed and no
kernel discrepancy is claimed.
Focused executable replay checks sixteen declarations in `Verify.InductiveMetadata`,
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
and first-argument implementations. It does not test a restored native modulo
path: that path is still disabled. It additionally evaluates the nested entry
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
The level soundness theorems
`Lean.Level.normalizeCore_eval`, `geq'_wf`, and `isEquiv'_wf` use the standard
logical axioms and the existing `Lean.Level.instLawfulBEqLevel` interface axiom,
without `sorryAx`. The frontend audit includes `sorryAx` and the existing
implementation-interface axioms, as noted above.

## Inhabited inverse weakening and the actual carrier check (2026-10-19)

`Ctx.LiftN.instN` and the six `weakN_inv_of_hasType` / `weak_inv_of_hasType`
lemmas for typed equality, untyped equality, and typing are ported from
[upstream PR #51](https://github.com/digama0/lean4lean/pull/51), head
`5ff580979f181a29c41cb358f542e0846756a0c6`. They are substitution lemmas:
the removed binder must have an actual typed inhabitant in the remaining
outer context. They require only environment orderedness, not the general
strengthening admission, and their transitive axioms are bounded by `propext`
and `Quot.sound`, with no admission or choice.

The local application factors primitive argument-domain recovery into
`tr_boundApp_domains`, retaining the comparison under the witness binder.
`tr_boundApp_arg_inhabited` then substitutes the supplied inhabitant.
The unchanged public `Reflection.ite_carrier` contract uses this helper with
`Prop : Type`. The concrete carrier result therefore no longer depends on
`IsDefEqU.weakN_iff`. No acceptance rule or caller premise is changed.

`tests/InhabitedStrengthening.lean` checks top and interior insertion, a
context-dependent inhabitant, all seven foundational lemmas, both private
helpers, and the actual public carrier theorem. Its dependency traversal
excludes `IsDefEqU.weakN_iff`, `NormalEq.parRed`, `NormalEq.parRedS`,
`IsDefEq.church_rosser`, and `IsDefEqU.quot_inj`. The primitive application
still inherits independent typing admissions; this is not an admission-free
primitive/frontend soundness claim. The two proof-binder callers of
`tr_boundApp_arg` remain on the old general strengthening path, explicitly
outside this repair.

Validation on Lean 4.29.0: all default targets and twelve focused fixtures
pass, including the new dependency audit, reflection/primitive and actual
non-inductive frontend controls, simultaneous substitution, and the existing
quotient reduction/obstruction fixtures. The source admission census remains
119 matching lines / 123 whole-word occurrences. The detached Lean 4.33.0-rc2
integration checkpoint separately passes its default build and five existing
trust-boundary fixtures; it does not yet incorporate this later fork work.

AI assistance: drafted and iterated with OpenAI Codex, compiled and tested
locally. Not yet human-reviewed. No PR or Zulip message has been submitted.
