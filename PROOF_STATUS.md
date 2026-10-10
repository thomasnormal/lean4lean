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
premise asserts whole-body or whole-raw-type typehood. The selected array of
free-variable identifiers and the projected-domain/component support remain
explicit; deriving them from checked declarations and complete construction
histories is still open.

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
