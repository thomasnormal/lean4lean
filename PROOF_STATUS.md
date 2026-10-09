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
  This standalone structural refinement does not justify constructor arities,
  parent/index metadata,
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
  validity/reservation and environment-map validity remain explicit; deriving
  the root context premises through checked headers is still needed before a
  complete runner theorem. The eight audits exclude `sorryAx` and expression or
  guarded-arity interfaces, using only existing logical/map/list-push interfaces.
  No axiom, admission, executable kernel change, cache, or fast path is added.
  These are structural source-reader and generated-field declaration guarantees,
  not semantic typing, recursive-value scope, generated index-binder alignment,
  WHNF transport, RHS reduction, or preprocessing soundness.
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
