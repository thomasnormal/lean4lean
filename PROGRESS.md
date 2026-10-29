# Progress and upstream comparison

## Constructive target-reduction ordinary consumers — 2026-10-29

The constructive checker target-reduction package now exposes ordinary `CheckerEnv` projections for direct checked-primitive, restoration-stage, direct source-typehood, and restoration-stage source-typehood routes. Reducer callbacks and exact target equations remain explicit alongside model/scope/registration/alignment/history and all source/value/map/recursor/generated-rule/iota premises.

## Constructive target-result ordinary consumers — 2026-10-29

The constructive checker target-result package now exposes ordinary `CheckerEnv` projections for direct checked-primitive, restoration-stage, direct source-typehood, and restoration-stage source-typehood routes. The target iota endpoint remains explicit alongside model/scope/registration/alignment/history and all source/value/map/recursor/generated-rule premises.

## Constructive checker restoration source-typehood ordinary consumers — 2026-10-29

The restoration-stage source-typehood constructive checker family now exposes ordinary `CheckerEnv` projections for base, iota-only, paired base/target iota, singular generated-rule-plus-iota, and plural generated-results-plus-iota forms. Source typehood still derives recursor model WF internally; the selected restoration metadata, executable scope, constructive registration, alignment/history, source/value/map/recursor obligations, generated-rule receipts, and paired iota witnesses remain explicit.

## Constructive checker source-typehood ordinary consumers — 2026-10-29

The direct checked-primitive constructive checker source-typehood family now exposes ordinary `CheckerEnv` projections for base, iota-only, paired base/target iota, singular generated-rule-plus-iota, and plural generated-results-plus-iota forms. Each derives recursor model WF from source typehood, preserves the existing model/scope/registration/alignment/history/source/value/map/generated-rule/iota premises, and projects only the checker component. These wrappers add no recursor or iota soundness theorem and are not upstream-ready without an official adaptation.

## Constructive checker ordinary consumers — 2026-10-29

The checked-primitive constructive checker package family now exposes ordinary `CheckerEnv` projections for direct and restoration-stage base, iota-only, singular generated-rule-plus-iota, and plural generated-results-plus-iota forms. The projections retain the Bool/Nat model, executable frontend scope, constructive registration evidence, alignment/history, source/value/map/recursor premises, generated-rule receipts, and paired iota witnesses while projecting `CheckerEnvInductive` through `toCheckerEnv`. They add no recursor or iota soundness theorem and are not upstream-ready without an official adaptation.

Last reviewed: **2026-10-29 (UTC)**. This is the readable overview of the
`poc-verified-noninductive` branch; [PROOF_STATUS.md](PROOF_STATUS.md) holds the
detailed theorem contracts, dependency audits, and regression evidence.

## Generic semantic-structural ordinary consumers — 2026-10-29

The generic restoration metadata semantic-structural packages now expose ordinary `CheckerEnv` projections for the base, iota-only, singular generated-rule-plus-iota, and plural generated-results-plus-iota forms. Alignment, declaration history, source/value/map/recursor premises, generated-rule and paired iota receipts, and constructor registration metadata remain explicit.

## Source semantic-structural ordinary consumers — 2026-10-29

The source semantic-structural `addDecl` packages now expose ordinary `CheckerEnv` projections for checked-primitive iota-only, singular generated-rule-plus-iota, plural generated-results-plus-iota, and the corresponding restoration-stage singular and plural forms. Alignment, declaration history, source/value/map/recursor premises, generated-rule and paired iota receipts, and constructor registration metadata remain explicit.

## AddDecl registration ordinary consumers — 2026-10-29

The checked-primitive and restoration-stage `addDecl.sourceRecursorRuleStagesGeneratedResultsAndRegistration...` packages now expose ordinary `CheckerEnv` projections for semantics, iota-only, singular generated-rule-plus-iota, and plural generated-results-plus-iota forms. The wrappers preserve the explicit executable stages, declaration history, source/value/map/recursor obligations, generated-rule receipts, paired iota witnesses, and registration metadata while projecting only the checker component.

## Generic restoration registration ordinary consumers — 2026-10-29

The generic restoration metadata registration packages now expose ordinary
`CheckerEnv` projections for semantics, iota-only, singular generated-rule-plus-
iota, and plural generated-results-plus-iota forms. Each projection retains
the executable restoration stages, final declaration history, generated-rule
and paired iota receipts, and all source/value/map obligations; only the
checker view is projected through `CheckerEnvInductive.toCheckerEnv`.

## Registration-semantics ordinary consumers — 2026-10-29

The checked-primitive registration-semantics model receipts now expose
ordinary `CheckerEnv` projections for singular generated-rule-plus-iota,
plural generated-results-plus-iota, and iota-only forms, for both the direct
checked-primitive stage and the restoration-stage choice. The wrappers retain
the Bool/Nat model facts, executable stage receipts, final declaration
history, generated-rule and paired base/target iota witnesses, and all source,
value, map, and recursor obligations. They only project
`CheckerEnvInductive` through `toCheckerEnv`; no recursor or iota soundness
theorem is added.

## Restoration-stage semantic structural ordinary consumers — 2026-10-29

The restoration-stage checked-primitive model semantic-structural packages
now expose ordinary `CheckerEnv` projections for singular
generated-rule-plus-iota, plural generated-results-plus-iota, and iota-only
forms. The selected primitive stage, model facts, executable stages,
alignment/history, generated-rule and paired iota receipts, and registration
metadata remain explicit. These consumer projections add no recursor or iota
soundness theorem.

## Checked-primitive semantic structural ordinary consumers — 2026-10-29

The checked-primitive model semantic-structural packages now expose ordinary
`CheckerEnv` projections for singular generated-rule-plus-iota, plural
generated-results-plus-iota, and iota-only forms. The projections preserve
model declaration facts, executable stage receipts, semantic alignment and
history, generated-rule and paired base/target iota witnesses, and
registration metadata. They are packaging consumers and add no recursor or
iota soundness theorem.

## Restoration-stage model structural ordinary consumers — 2026-10-29

The restoration-stage checked-primitive model structural packages now expose
ordinary `CheckerEnv` projections for singular generated-rule-plus-iota,
plural generated-results-plus-iota, and iota-only forms. They retain the
selected primitive stage, model declaration facts, executable preprocessing
and staging, alignment/history, constructor-indexed structural receipts,
paired iota endpoints, and registration metadata.

## Checked-primitive model structural ordinary consumers — 2026-10-29

The checked-primitive model structural packages now expose ordinary
`CheckerEnv` projections for their singular generated-rule-plus-iota,
plural generated-results-plus-iota, and iota-only forms. The model
declaration facts and executable structural stages remain unchanged, as do
constructor-indexed lookup/field-count facts, generated-rule/iota witnesses,
and registration metadata.

## Executable structural ordinary consumers — 2026-10-29

The checked-primitive and restoration-stage `addDecl` structural receipts now
also expose ordinary `CheckerEnv` projections, for both singular and plural
generated-rule package names. They preserve executable preprocessing/staging,
alignment and history, constructor-indexed lookup/field-count facts, complete
generated-rule receipts, paired base/target iota witnesses, and registration
metadata. These wrappers add no recursor/iota soundness claim.

## Restoration structural generated-rule ordinary consumers — 2026-10-29

The restoration structural packages now expose ordinary `CheckerEnv`
projections through
`SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv`
and its plural generated-results companion. Both retain constructor-indexed
source lookup/field-count facts, complete generated-rule receipts, paired
base/target iota witnesses, and registration/model-shape metadata.

## Restoration structural ordinary metadata consumer — 2026-10-29

`SafeInductiveRestorationMetadata.sourceRecursorRuleStagesAndCheckerStructuralIotaBaseAndTargetResults_toCheckerEnv`
projects the metadata restoration structural checker receipt through ordinary
`CheckerEnv`. It preserves the restored entry alignment, constructor-indexed
lookup and field-count facts, generated-rule/iota witnesses, and model-shape
registration metadata. This is a consumer packaging theorem; it adds no
recursor or iota soundness and does not close the executable inductive
frontend theorem.

## Restored structural rule/iota ordinary consumer — 2026-10-29

`NativeInductive.RestoredRecordEvidence.toCheckerEnv_and_sourceRecursorGeneratedRuleStructuralAndIotaBaseAndTargetResults`
projects the restored constructor-indexed structural receipt to ordinary
`CheckerEnv`. It retains recursor and constructor lookup facts, source
metadata/field counts, generated-rule results, model-shape/registration
receipts, and paired base/target iota endpoints.

## Restored constructive checker/map-WF ordinary consumer — 2026-10-29

`NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerAndMapWFGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv`
now exposes the restored constructive checker package through ordinary
`CheckerEnv` while retaining final constant-map WF, registration evidence,
alignment/history, generated-rule results, and paired base/target iota
receipts.

## Restored constructive checker ordinary consumer — 2026-10-29

`NativeInductive.RestoredRecordEvidence.registrationConstructiveCheckerGeneratedRuleResultAndIotaBaseAndTargetResults_toCheckerEnv`
projects the complete restored constructive checker package to ordinary
`CheckerEnv`. It retains the registration evidence, final alignment/history,
generated-rule results, and paired base/target iota receipts while exposing
the checker through the ordinary interface. No new recursor or iota
soundness claim is inferred.

## Restoration target-iota ordinary consumers — 2026-10-29

The general and checked-primitive restoration-stage target-iota packages now
have ordinary `CheckerEnv` projections:
`addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleIotaTargetResults_of_restorationStages`
and its checked-primitive counterpart. They retain final declaration history,
alignment, map equalities, generated-rule translation, and indexed target-iota
receipts; they add no general recursor or iota soundness claim.

## Restoration-stage generated-rule and iota ordinary consumer — 2026-10-29

`addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_restorationStages`
now projects the general restoration-stage package to ordinary `CheckerEnv`
callers while retaining existential primitive-stage selection, semantic
alignment, final declaration history, complete generated-rule receipts, and
paired base/target iota endpoints. The wrapper preserves the existing source,
value, map, and history obligations; it does not establish general recursor or
iota soundness or complete inductive frontend verification.

## Checked-primitive restoration generated-rule and iota ordinary consumer — 2026-10-29

`addDecl.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_checkedPrimitive_and_restorationStages`
now exposes the checked-primitive restoration package through ordinary
`CheckerEnv`, while retaining the primitive metadata, semantic alignment,
final declaration history, complete generated-rule receipts, and both iota
endpoints. The primitive frontend and recursor/iota soundness obligations stay
explicit.

## Restoration generated-rule and iota ordinary consumer — 2026-10-29

`SafeInductiveRestorationMetadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultAndIotaBaseAndTargetResults_of_sourceTypehood`
now carries the complete generated-rule receipt and both base/target iota
endpoint witnesses through ordinary `CheckerEnv`, alongside final declaration
history. The source-typehood premise derives only recursor model WF; general
generated-rule and iota soundness remain explicit obligations.

## Restoration registration semantics ordinary consumer — 2026-10-29

`SafeInductiveRestorationMetadata.toCheckerEnv_and_registrationHistory_and_generatedRuleResultSemantics_of_sourceTypehood`
now carries the restoration-stage checker, final `TrEnvInductive` history, and
per-recursion generated-rule result receipts through the ordinary `CheckerEnv`
interface. Source typehood derives only the existing recursor model-WF
witness; generated-rule and iota soundness remain explicit downstream
obligations.

## Restoration metadata ordinary checker consumer — 2026-10-29

`SafeInductiveRestorationMetadata.toCheckerEnv` now projects the conditional
restoration-stage `CheckerEnvInductive` receipt to ordinary `CheckerEnv`
callers. It preserves executable preprocessing/staging selection, restored
entry alignment, final declaration history, explicit recursor model WF, and
safe-value translation. Its source-typehood form derives only the existing
recursor-WF witness; generated-rule semantics, iota soundness, and complete
inductive frontend verification remain separate obligations.

## Restored native ordinary checker consumer — 2026-10-29

`NativeInductive.RestoredRecordEvidence.toCheckerEnv` now projects a restored
native registration receipt to the ordinary `CheckerEnv` interface when the
caller supplies the final declaration history, explicit recursor model-WF
receipt, and safe-value translation callback. The source-typehood convenience
form delegates through this explicit consumer, so it derives only the existing
recursor-WF witness. Registration-history construction, generated-rule
semantics, iota soundness, and complete executable inductive frontend
verification remain separate obligations.

## Primitive staged `VDecl.WF` receipt — 2026-10-26

`AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorVDeclWF`
now combines the successful primitive Bool/Nat preflight with the checked
header/constructor stage. Its result includes the canonical model declaration,
its `HeadersWF` and `WF` receipts, the semantic header and constructor maps,
and a `VDecl.WF` witness for the registered inductive declaration. The theorem
stops at the header/constructor boundary; generated recursor registration and
recursor/iota soundness remain explicit downstream obligations.
Its checker companion transports the safe-value facts through the native
header/constructor frame and returns the transported `CheckerEnv` together
with the same semantic `VDecl.WF` receipt. This remains a staged checker
boundary; it does not establish recursor registration or iota soundness.

The companion `refinesPrimitiveHeaderConstructorCheckerWithModelAndVDeclWF`
keeps the public declaration model facts beside that checker receipt, including
`HeadersWF`, declaration `WF`, and the registered `VDecl.WF`. It is a packaging
theorem for the same staged boundary and adds no recursor or iota result.

The checked-primitive constructive-history consumer now has a companion that
returns the producer's semantic `VDecl.WF` receipt alongside its registration
and `TrEnvInductive` history. Recursor model WF remains an explicit premise.

The corresponding checker-history consumer now retains that same producer
`VDecl.WF` beside aligned constants, final history, checker construction, and
generated-rule semantics. Its source/value and recursor obligations remain
explicit.

The restoration-stage checker-history companion preserves the same declaration
`VDecl.WF` across the existential stage selection, with source/value and
generated-rule obligations still visible.

The checked-primitive base/target-iota consumer now carries the same producer
`VDecl.WF` beside its retained iota endpoints; stored-RHS and target typing
obligations remain unchanged.

The restoration-stage base/target-iota consumer now carries the producer
`VDecl.WF` through stage selection, retaining both iota endpoints and their
existing source/value obligations.

`AddInductWithRecursorsEvidence.inductiveDeclWF` now projects the semantic
`VDecl.WF` declaration receipt from constructive header/constructor evidence
when the declaration model `WF` is supplied explicitly. Recursor registration
remains a separate evidence stage.

`AddInductWithRecursorsEvidence.result_wf` now consumes that staged declaration
receipt and the initial semantic environment WF to prove WF of the environment
after generated recursor signatures are inserted. `TrEnvInductive.wf` uses this
projection directly, keeping recursor model WF and declaration history explicit.
This remains a registration-stage result and does not establish recursor rule
semantics, iota soundness, or complete executable inductive frontend soundness.

`AddInductWithRecursorsEvidence.to_trEnvInductive` now packages the same staged
receipt into a `TrEnvInductive` history step when the prior history and staged
declaration WF are supplied explicitly. `RegistrationEvidence.to_trEnvInductive`
uses this generic consumer, so native registration no longer reconstructs the
history constructor's parameter plumbing. Recursor model WF and all rule/iota
obligations remain caller-visible.

`AddInductWithRecursorsEvidence.toCheckerEnvInductive` now consumes the
constructive generated-recursors receipt at the checker boundary. The prior
`TrEnvInductive` history, native/result constant-map equalities, staged
declaration `VDecl.WF`, and safe-value translation callback remain explicit.
`RegistrationEvidence.toCheckerEnvInductive` delegates to this generic
consumer, so the native bridge shares the same visible obligations. This is a
checker packaging result; recursor model WF, generated-rule semantics, iota
soundness, and executable inductive frontend soundness remain open.
The paired `toCheckerEnvInductive_and_wf` consumer returns the same checker
alongside final constant-map WF and semantic-environment WF. The native
registration wrapper and its source-typehood form delegate to it, retaining
the explicit map equalities, staged declaration WF, recursor/value premises,
and all generated-rule/iota boundaries.
The generic `toCheckerEnvInductive_and_aligned` consumer now pairs the checker
with final semantic alignment. The native aligned bridge delegates through this
receipt consumer and transports the explicit native/result map equality without
changing its declaration-WF, recursor, or safe-value obligations.
The combined `toCheckerEnvInductive_and_aligned_and_wf` consumer now returns
the checker, final alignment, constant-map WF, and semantic-environment WF in
one receipt. Native and source-typehood wrappers preserve the same explicit
declaration, recursor, map, alignment, and safe-value obligations.
The registration consumer now pairs that checker receipt with the executable
`addInductWithRecursors` equation, final semantic-environment WF, and result
map WF. Its native and source-typehood forms retain the same explicit
recursor and safe-value premises.
The checked frontend scope's source-typehood companion now derives the
recursor model-WF premise from translated source typing without changing the
registration or checker boundary.
The checked `SafeInductiveFrontendScope` now exposes the same executable
registration equation and WF receipts beside its checker environment, while
keeping the producer, history, map, recursor, and safe-value inputs explicit.
Its aligned registration companion now returns semantic alignment alongside
the checker, executable registration equation, semantic environment WF, and
result-map WF; the source-typehood form derives only the recursor model-WF
premise and keeps the initial alignment explicit.
`SafeInductiveRestorationMetadata` now lifts that aligned registration receipt
directly through its frontend scope, preserving the same explicit history,
alignment, map, and safe-value inputs for restoration callers.
The explicit-recursors companion exposes the same package when recursor model
WF has already been constructed, avoiding any hidden source-typehood step.
The scope now also projects `CheckerEnvInductive` to the existing `CheckerEnv`
consumer interface, with an explicit-recursors form and a source-typehood
convenience form.
Restoration metadata exposes the matching ordinary `CheckerEnv` projection
through its frontend source-typehood path.
Restored native record evidence now exposes the same ordinary checker
projection directly from its source-typehood receipt.
The executable restoration-stage wrappers now expose ordinary `CheckerEnv`
consumers directly, including the checked-primitive path, while preserving
the explicit producer, history, map, source-typehood, and safe-value inputs.
The direct executable frontend-scope path now exposes matching ordinary
`CheckerEnv` consumers, including its checked-primitive specialization.

## All-safety inductive checker boundary — 2026-10-26

`VEnvs.InductiveWF` now records an all-safety `TrEnvInductive` history together
with primitive invariants and safety monotonicity. Its `map_wf` and `venv_wf`
projections expose the map and per-safety environment obligations, and
`toCheckerEnvInductive` constructs the inductive checker environment when the
caller supplies the safe-value translation callback. This is a semantic
consumer boundary for inductive histories; the legacy `VEnvs.WF` relation still
rejects inductive families and is intentionally unchanged. The combined
checker/WF package and checker-side map/environment WF projections make those
facts available without reopening the history. The regression fixture checks
the new projections and construction. Inductive registration,
recursor/iota soundness, and executable frontend soundness remain open.

## Bottom line

The legacy `AddInduct` boundary now has a constructive producer: `RegistrationEvidence.to_legacyAddInduct`
packages the verified header/constructor stages, and its aligned companion exposes the corresponding
`Aligned` result. Generated recursors remain represented by the richer
`AddInductWithRecursorsEvidence`; this bridge does not claim recursor or iota soundness.
The boundary also exposes `AddInduct.map_wf` and `AddInduct.lookupReceipt` so
older consumers can use its constructive map and positive lookup facts without
reopening the evidence constructor.
`RegistrationEvidence.to_trEnvInductive_and_aligned` now pairs the explicit
declaration history with the aligned result map, with a source-typehood
convenience form that derives recursor WF from the same explicit obligations.
The checker bridge now has a generic `toCheckerEnvInductive_and_aligned` form
that retains explicit recursor WF and value-translation witnesses, while the
source-typehood form delegates to it.
`SafeInductiveFrontendScope.toCheckerEnvInductive_and_registrationHistory`
similarly combines generic checker construction with the explicit final
declaration history; its source-typehood form now delegates to that theorem.
The corresponding `toCheckerEnvInductive_and_registrationAlignmentHistory`
package returns checker construction, aligned result map, final map equality,
and declaration history from the same explicit recursor-WF witness.
The first generated-rule semantic package now has the same generic explicit-WF
form, with the source-typehood variant deriving WF and delegating to it.
Its paired generated-rule iota base/target package is also available with
explicit recursor WF; the source-typehood wrapper derives that witness.
The combined generated-result plus iota package now has the same generic
explicit-WF form and delegates its source-typehood wrapper.
The generic checker bridge also exposes a target-only generated-rule iota
package with the same explicit recursor-WF boundary.
It also exposes a paired generated-result plus target-iota package, retaining
the complete generated receipt alongside the target endpoint.
The ordinary `addDecl` frontend now lifts that target-only package through its
source-typehood path while retaining the frontend's `allowPrimitive` result.
The checked-primitive `addDecl` path exposes the same target-only package with
its primitive checker and source-typehood preconditions explicit.
Restoration metadata now lifts the target-only package through its
source-typehood frontend scope while retaining the restoration-stage boundary.
The ordinary restoration-stage `addDecl` wrapper now returns that metadata and
the target-only package together, including the explicit primitive bit.
The checked-primitive restoration-stage path exposes the target-only package
with its primitive checker and metadata obligations retained.
The restored-record checker bridge now also exposes a generic target-iota
alignment/history package with explicit recursor WF.

Our fork has substantial additional checker verification, primitive proofs,
inductive staging work, and regression coverage. It is **not a completed
verification of Lean's kernel**, and it is **not uniformly ahead of official
lean4lean**. Upstream has independently proved ordinary declaration checking
and added newer primitive and universe-level results that our branch has not
fully integrated into the published branch. Its admission-free simultaneous
substitution proof is narrowly ported here; that is foundation integration,
not completion of frontend soundness.

**Published versus upstream integration:** the review branch
`poc-verified-noninductive` retains its Lean **4.29.0** history. The current
candidate, `poc-verified-noninductive-upstream-20261021`, replays that history
on official `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` with Lean
**4.33.0-rc2**. Reconciliation reuses the validated October 20 integration
adaptations, preserving upstream mutual-definition behavior, the actual
quotient dispatcher proof, and the inhabited telescope and fuel replacement
repairs. It also retains the proved canonical non-inductive `addDecl.WF`,
the primitive inductive model-WF receipt, total elimination-universe name
selection, restored native record receipts, and the newest rule-result
registration continuation. The original review history and raw rebase are
preserved locally. Publication uses a separate integration branch while
permission to rewrite the review branch remains pending.

The rule-result continuation retains the explicit generated result relation
and closed rule translations. Its complete per-recursor rule-semantics
coverage is now derived from the paired indexed constructor callback and the
ordered recursor-rule length invariant; the continuation still exposes that
coverage alongside the indexed generated results for downstream consumers.
Inductive frontend soundness, rejection-consumer migration, and `AddInduct`
remain open.

The checked primitive registration boundary now also packages the exact final
native constant-map lookup for every ordered header, constructor, and recursor.
`addDecl.checkedPrimitiveRegistrationRealizationAndOrderedEntryLookup` composes
the executable checked-primitive scope and semantic registration receipt with
the constructive ordered lookup theorem. The native recursor model-WF premise
and map equality remain explicit; this does not construct `AddInduct` or prove
recursor/iota semantics.

The restored-record boundary now also packages the semantic registration
receipt, the explicit ordered map equation, and the native result-map WF proof
in `RestoredRecordEvidence.registrationReceiptAndMap`. Its installation
receipt comes directly from the restored registration trace, so its audited
dependencies remain the standard logic and retained translation admission; it
does not route through the persistent-map lookup interface.

`RestoredRecordEvidence.registrationReceiptAndMapAndAlignment` extends that
package with the producer's `Aligned` semantic map invariant. The alignment is
derived directly from the producer receipt, so this checker-facing extension
retains the same dependency-safe audit and leaves history/`AddInduct` and
recursor soundness obligations explicit.

`RestoredRecordEvidence.toCheckerEnvInductive_and_registrationReceiptAndMapAndAlignment`
now consumes an explicitly supplied final `TrEnvInductive` history and value
translation callback alongside that receipt. It returns the checker-facing
environment together with the restored map, installation, WF, and alignment
facts, keeping history construction as an explicit caller obligation.

`SafeInductiveFrontendScope.toCheckerEnvInductive_of_explicitHistory` exposes
the corresponding direct scope consumer: callers provide the final history,
map equality, and safe-value translation callback, and receive the checker
environment without invoking producer registration or persistent-map WF lemmas.

`SafeInductiveFrontendScope.toCheckerEnvInductive_of_explicitHistoryAndMapWF`
also returns the explicit final-map equality and the initial `ConstMap.WF`
proof obtained from the scope's original environment. This gives constructive
registration callers the map premise without deriving lookup receipts.

`RegistrationEvidence.orderedEntryReceiptAndMap` pairs the producer's ordered
semantic, model-shape, type-translation, and declaration-membership receipt
with its explicit `insertOrdered` map equation. It is a map-alignment package;
positive final-map lookup remains a separate audited interface.

`RegistrationEvidence.orderedEntryReceiptAndMapAndAlignment` adds the
producer's `Aligned` result-map invariant to that package without changing the
explicit map or recursor-WF obligations.

The explicit-history scope/map-WF bridge now also exposes that ordered receipt
and alignment while retaining `constants.WF` as a separate result.

`SafeInductiveFrontendScope.toCheckerEnvInductive_and_orderedEntryReceiptAndMapAndAlignment`
consumes an explicit final checker history and value-translation callback, then
pairs the checked scope with that producer receipt and alignment. It avoids the
older producer-based checker constructor and its persistent-map conversion.

`RestoredRecordEvidence.registrationReceiptAndMapAndOrderedEntryFindPrime`
re-expresses each restored installation lookup against the producer's explicit
`resultConstants` map using the kernel environment's staged-map (`find?'`)
view. It only transports the restored receipt across the supplied map equality
and does not invoke persistent-map lookup conversion.

`RestoredRecordEvidence.registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment`
packages that staged-map lookup receipt with the producer's `Aligned` semantic
map invariant for consumers needing both installation and model transport.

`RestoredRecordEvidence.toCheckerEnvInductive_and_registrationReceiptAndMapAndOrderedEntryFindPrimeAndAlignment`
now lifts that package through the explicit-history checker boundary. The final
declaration history and safe-value translation remain explicit caller inputs.

The reducer boundary now also accepts an exact equation whose result is the
stored rule RHS. This packages the generated target translation, typing, sort
arity, and native reducer success in one receipt, with a per-recursor
registration consumer. The non-K application, normalized constant, Nat-literal,
and string-literal branches of the native dispatcher now have proved equations
exposing their exact assembled RHS under explicit normalization, constructor
adaptation, rule lookup, arity, and universe-length premises. Connecting those
branch witnesses to generated replacement lists and covering the K application
adaptation path now have the same explicit equations; literal and nonliteral
structure-adaptation branches now have matching equations, while connecting
all branch outputs to generated replacement lists and proving the final
complete iota/recursor soundness theorem remain open. The target-result
consumer now packages a supplied exact `rule.rhs.mkAppList replacements`
equation alongside its translated, typed, and sort-arity endpoint; deriving
that equation from each assembled branch is still an explicit caller
obligation. The K-application endpoint now consumes its characterized
conditional RHS with that shape equality, leaving the same shape premises for
the other branches. The conditional bridge is now factored as a reusable
target-result consumer for every dispatcher branch, and both K-literal target
endpoints now use it with their constructor/expansion-specific shapes. The
non-K Nat and String literal endpoints now use the same bridge with their
canonical-constructor and String-expansion shapes. The non-K structure
endpoint now uses the same bridge with its nonliteral exclusions and adapted
constructor shape. The K structure endpoint now uses the same bridge with its
`toCtorWhenK` witness, nonliteral exclusions, and adapted-constructor shape.
The reusable `dispatcherConditionalShapeOfReplacementDecomposition` theorem
now proves the native three-slice assembly equals one generated replacement
list from explicit argument decompositions and level-instantiation equality.
The companion `instantiateLevelParams_eq_self_of_noLevelParam` helper derives
that level equality from the stored RHS's structural no-level-parameter flag.
The new `dispatcherArgumentSliceDecomposition` and
`dispatcherConstructorSliceDecomposition` lemmas construct the canonical
recursor and constructor list slices from the selected-major and field-count
metadata, and `dispatcherConditionalShapeOfCanonicalDecomposition` packages
those slices with the reusable RHS bridge. The generic frontend still leaves
the level-instantiation relation and the native field-count witness explicit;
this is a decomposition bridge, not complete iota or recursor soundness.
`dispatcherConditionalShapeOfCanonicalOutput` now hides the intermediate
slice witnesses for callers whose stored RHS carries the no-level-parameter
receipt, deriving the exact generated replacement-list equality directly.
`dispatcherFieldCountOfConstructorMetadata` now projects the stored
constructor metadata to the recursor rule's native field-count premise, given
the corresponding constructor-value argument bound. The actual constructor
normalization proof still has to supply that argument bound at a concrete
reducer call.
`dispatcherConditionalShapeOfMetadataOutput` composes the field-count
projection with the no-level canonical output theorem and returns a complete
registered-rule lookup package plus the exact generated replacement shape.
`dispatcherConstructorFieldBoundOfNativeEtaStructEntryReceipt` now turns the
native structure-normalization arity receipt into the reducer field-count
bound, retaining the explicit `getAppNumArgs = getAppArgs.size` representation
bridge.
`dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceipt` now
returns the receipt-derived field bound at the metadata-driven output
boundary, using explicit constructor-head and context/environment equalities
to align the native constructor value with stored metadata.
`dispatcherConditionalShapeOfMetadataOutputWithRuleLookup` now pairs that
shape with the executable `getRecRuleFor` equation, retaining rule-selection
as an explicit caller-supplied obligation.
`dispatcherConditionalShapeOfMetadataOutputWithRuleLookupAndFieldCount` now
keeps the metadata-derived `rule.nfields ≤ constructor.getAppArgs.size`
bound in that same package.
`dispatcherConditionalShapeOfMetadataOutputOfNormalizedNatLiteral` now
specializes that package to the reducer's canonical Nat-literal constructor,
while exposing the packaged reducer field bound alongside the exact shape and
executable rule selection.
`dispatcherConditionalShapeOfMetadataOutputOfStringLiteralExpansion` now pairs
the explicit `strLitToConstructor` expansion receipt with the metadata-derived
field bound, exact output shape, and executable rule selection.
`GeneratedRecursorRuleIotaTargetResult.of_normalizedNatLiteralMetadataExact`
now consumes that canonical Nat-literal package at the generated target
boundary, retaining literal dispatch and dependent target witness obligations.
`GeneratedRecursorRuleIotaTargetResult.of_normalizedStringLiteralMetadataExact`
adds the corresponding explicit string-expansion path for generated targets
and consumes that paired expansion package and metadata-derived reducer field
bound.
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedNatLiteralMetadataExact`
adds the K-normalized Nat-literal path with explicit K adaptation and consumes
the same canonical dispatcher package and metadata-derived field bound.
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStringLiteralMetadataExact`
adds the corresponding K-normalized String expansion path and consumes the
same paired expansion package and metadata-derived reducer field bound.
The receipt-backed companion
`dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookup`
packages native constructor alignment, the receipt-derived reducer field bound,
exact output shape, and executable rule selection at one existential boundary,
reusing the lower-level receipt endpoint.
`dispatcherConditionalShapeOfMetadataOutputOfNativeEtaStructEntryReceiptWithRuleLookupAndAdaptation`
now pairs that receipt package with the explicit `toCtorWhenStruct` result.
`GeneratedRecursorRuleIotaTargetResult.of_normalizedStructureMetadataExact`
now consumes that package at the ordinary structure reducer branch, with a
dependent family for generated translation, target typing, and sort arity.
The K-normalized companion
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedStructureMetadataExact`
preserves the same receipt/adaptation package for the explicit `toCtorWhenK`
path.
`GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationExact` now
provides the corresponding ordinary application endpoint, carrying the
normalized application, structure adaptation, rule lookup, field bound, exact
conditional output shape, and dependent target witnesses through the proved
non-K dispatcher equation.
`GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantExact` now carries
the ordinary nullary-constant dispatcher equation through the same generated
translation, typing, sort-arity, and conditional output-shape endpoint.
`dispatcherConditionalShapeOfMetadataOutputOfNormalizedConstant` and
`GeneratedRecursorRuleIotaTargetResult.of_normalizedConstantMetadataExact`
now provide the corresponding metadata-driven constant package and target
consumer, retaining explicit constructor adaptation, field bounds, rule
selection, and dependent target witnesses.
The ordinary normalized-constant exact endpoint now precedes its metadata
consumer, and that consumer reuses it after assembling the paired constant
adaptation package. Constant normalization, metadata alignment, output shape,
generated translation, target typing, and sort arity remain explicit.
`inductiveReduceRec.eq_some_of_kNormalizedConstant` and
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantMetadataExact`
now carry the corresponding K-normalized constant path, retaining explicit
`toCtorWhenK`, constant normalization, structure adaptation, metadata field
count, rule selection, and dependent target witnesses.
`dispatcherConditionalShapeOfMetadataOutputOfNormalizedApplication` and
`GeneratedRecursorRuleIotaTargetResult.of_normalizedApplicationMetadataExact`
now provide the ordinary normalized-application metadata package and target
consumer, preserving explicit application adaptation, field bounds, rule
selection, and generated target witnesses.
`dispatcherConditionalShapeOfMetadataOutputOfKNormalizedApplication` and
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedApplicationMetadataExact`
now carry the corresponding K-normalized application package, retaining both
`toCtorWhenK` and structure adaptation together with metadata field bounds,
rule selection, and dependent target witnesses.
`dispatcherConditionalShapeOfMetadataOutputOfKNormalizedConstant` now gives
the K constant branch the same paired adaptation package, so its target
consumer no longer combines an ordinary metadata package with a separate
K-conversion receipt.
`dispatcherConditionalShapeOfMetadataOutputOfKNormalizedStringLiteralExpansion`
now gives the K String branch a paired K-conversion and expansion package,
keeping its constructor metadata and rule witnesses aligned.
`dispatcherConditionalShapeOfMetadataOutputOfKNormalizedNatLiteral` now gives
the K Nat branch the analogous paired K-conversion and canonical-constructor
package, with its metadata field bound and rule lookup aligned.
`GeneratedRecursorRuleIotaTargetResult.of_kNormalizedConstantExact` now
provides the non-metadata K constant target endpoint, carrying the explicit K
conversion and structure adaptation through the proved K dispatcher equation.
The K constant metadata consumer now reuses that target endpoint after its
registered-rule package is assembled, so the K dispatcher transport is shared
without hiding metadata or generated-target obligations.
The non-metadata K Nat-literal endpoint is now placed before its metadata
consumer, and the metadata consumer reuses it after assembling the paired
canonical-constructor package. This removes duplicated K Nat dispatcher
transport while retaining explicit metadata alignment, output shape, generated
translation, target typing, and sort-arity witnesses.
The ordinary Nat-literal metadata consumer now reuses
`of_normalizedNatLiteralExact` after obtaining its canonical-constructor
metadata package, removing duplicated literal dispatcher transport while
retaining explicit metadata alignment, output shape, generated translation,
target typing, and sort-arity witnesses.
The ordinary String-literal metadata consumer now reuses
`of_normalizedStringLiteralExact` after obtaining its paired expansion package,
removing duplicated String dispatcher transport while retaining explicit
metadata alignment, output shape, generated translation, target typing, and
sort-arity witnesses.
The K-normalized String-literal exact endpoint now precedes its metadata
consumer, and the metadata consumer delegates final dispatcher-to-target
transport to it after assembling the paired K-conversion and String-expansion
package. Metadata alignment, output shape, generated translation, target
typing, and sort arity remain explicit.
The K-normalized structure metadata consumer now reuses
`of_kNormalizedStructureExact` after assembling its receipt-backed K and
structure-adaptation package, removing duplicated dispatcher transport while
retaining explicit normalization exclusions, metadata alignment, output shape,
generated translation, target typing, and sort arity.
The ordinary structure metadata consumer now likewise reuses
`of_normalizedStructureExact` after assembling its receipt-backed constructor
adaptation package, removing duplicated dispatcher transport while retaining
the explicit normalization exclusions, metadata alignment, output shape,
generated translation, target typing, and sort-arity witnesses.
The generated target consumer audit is now complete for the metadata branch
families: ordinary/K applications, constants, Nat literals, String literals,
and structures all delegate dispatcher-to-target transport to their exact
non-metadata endpoints after assembling their own metadata packages. Each
wrapper retains its branch-specific normalization, adaptation, alignment,
shape, translation, typing, and sort-arity obligations.
The restored source-indexed target-reduction boundary now also has an exact
variant: `sourceRecursorGeneratedRuleIotaTargetReductionExact` carries a
reducer equation whose result is definitionally the stored rule RHS through
the same indexed lookup and generated-rule witnesses. This keeps the exact
output contract available after restored-record source alignment; it does not
claim the final inductive soundness theorem.
The companion
`sourceRecursorGeneratedRuleResultsAndIotaTargetReductionExact` endpoint now
keeps the complete generated-rule result paired with that exact reducer
equation, so callers can retain constructor/minor, source metadata, and target
translation witnesses in one restored-record package.
The registration boundary now exposes the matching
`recursorGeneratedRuleResultAndIotaTargetReductionExact` consumer, preserving
the same generated result and exact stored-RHS equation before source-indexed
restoration.
Its ordered registration traversal now has the corresponding exact-output
package, retaining the complete generated result and exact reducer equation for
every stored recursor rule while keeping header and constructor branches
trivial.
The restored checker certificate now has an exact target-reduction companion,
`toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetReductionExact`,
which pairs the checked environment with the source-indexed exact package.
The restored ordinary target projection now also has an exact variant,
`sourceRecursorGeneratedRuleResultsAndIotaTargetOrdinaryExact`, preserving the
RHS equation while converting the same target witnesses to ordinary typing.
Its target-only spelling,
`sourceRecursorGeneratedRuleIotaTargetOrdinaryExact`, now exposes the same exact
ordinary package without dropping the source metadata and constructor lookup.
The restored checker certificate also has an exact ordinary-target companion,
`toCheckerEnvInductive_of_sourceTypehood_and_generatedRuleResultAndIotaTargetOrdinaryExact`,
which pairs the checker proof directly with that source-indexed exact ordinary
package while retaining the generated-result and reducer obligations.
Exact restored target-reduction and checker packages now also expose the
established plural generated-rule aliases, including plural target-reduction
spellings, so callers can preserve the exact stored-RHS equation without
renaming their traversal-level contracts.
The checked primitive restoration-stage package now has an exact generated-rule
target-reduction companion,
`addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetReductionPackage_of_restorationStagesExact`.
It preserves the existing model, checker, registration, and restoration
receipts while returning the exact stored-RHS reducer relation through the
ordered exact registration consumer.
The matching source-typehood route and its restoration-stage/plural aliases
now derive recursor model well-formedness internally while retaining the same
exact reducer callback and stored-RHS relation.
The restoration-stage ordinary checker package now has an exact companion,
`addDecl.checkedPrimitiveModelAndConstructiveCheckerGeneratedRuleResultAndIotaTargetOrdinaryPackage_of_restorationStagesExact`,
which projects the exact reducer result through ordinary typing and preserves
the explicit target WF callback.
The source-typehood ordinary route and its restoration-stage/plural aliases now
derive recursor model WF internally while retaining the exact stored-RHS
equation and ordinary target witnesses.
The checked frontend target-result package family now has matching exact
restoration-stage and source-typehood/plural aliases.  These endpoint names
reuse `GeneratedRecursorRuleIotaTargetReductionExact` through the new
`GeneratedRecursorRuleIotaTargetResultExact` spelling, so translated target
witnesses remain paired with the native reducer equation whose result is the
stored rule RHS.
The lower-level checked `IotaTargetResultPackage` spelling now has exact
restoration and source-typehood aliases as well.  These aliases intentionally
retain the complete generated-rule witness together with the exact target
reduction equation, so dropping that witness never drops the native result
constraint.
The direct checked `IotaTargetReductionPackage` spelling now has matching
exact restoration and source-typehood aliases, reusing the same endpoint
package so its reducer equation remains definitionally tied to the stored RHS.
The direct checked ordinary-target package now has exact restoration and
source-typehood aliases, reusing the generated ordinary exact consumer with
its explicit semantic-environment and target WF callbacks.
Registration and ordered-registration exact consumers now also expose
target-result spellings, including singular/plural generated-result aliases.
They are definitional endpoint names for the exact target-reduction packages,
so the stored-RHS equation and generated constructor/minor witness remain
paired at registration.
Restored source-indexed consumers now expose matching exact target-result and
checker spellings, including singular/plural aliases.  These names retain the
restored lookup metadata and the same exact stored-RHS relation.
Registration exact APIs now also provide the missing singular/plural
`Reduction(s)Exact` and `Result(s)Exact` spellings for recursor and ordered
traversals.  These are definitional aliases only; they add no proof path or
weaken the exact reducer contract.
The October 26 audit completes the same endpoint matrix for restored
source-indexed consumers and their checker certificates: singular/plural
`IotaTarget`, `Reduction(s)`, and `Result(s)` exact spellings now all resolve
to the existing exact reducer package.  Source lookup metadata, generated
constructor/minor witnesses, and the stored-RHS equation remain paired.
The checked-primitive restoration-stage aggregate now also has the missing
plural generated-rule `IotaTargetReductionPackage` exact spelling, reusing the
singular exact theorem without changing its callback or stored-RHS equation.

**Complete stored-rule generated semantics (October 25):** the indexed rule
receipt now has an explicit stored-rule bridge that recovers the constructor,
minor, source index, closed RHS semantic witness, and generated result for
every member of each registered recursor's stored rule list. The existing
complete semantic projection is defined through this paired bridge, so the
registration CPS boundary and its frontend wrapper derive complete semantic
coverage from one aligned indexed package. No executable behavior changed;
the remaining obligation is to consume these receipts in the actual iota and
recursor reduction soundness theorem.

**Inhabited telescope repair:** well-founded recursion now discharges two direct
inverse-weakening obligations by substituting zero for the Nat binders certified
by its existing guard. The new generic helpers support dependent telescopes and
a retained binder depending on the base context; their dependency audits exclude
admissions, choice, false strengthening and confluence. Public theorem premises
and executable behavior are unchanged. The full recursion theorem still inherits
general strengthening through checker dependencies. Three further context
extractions for the guarded measure telescope now use abstraction and typed zero instantiation, including
beneath the retained packed-argument binder. These native translation helpers
exclude false strengthening and confluence; they retain exactly the existing
projection definition, weakening and instantiation admissions, standard logic,
and three native persistent-container interfaces.
The abstraction/typed-zero direction also exists in draft
[upstream PR #53](https://github.com/digama0/lean4lean/pull/53), whose
`MLCtx.trExprS_dropN_nat` and larger recursion redesign were inspected at
`5a8c0d5`. This checkpoint repairs the current contracts and supplies explicit
trust audits; no duplicate upstream PR is opened.
The remaining direct fuel extraction now follows #53's same-context successor
replacement: the checked `succ t` witness stays under the original fuel binder,
and the induction consumes the resulting equality at adjacent fuel closings.
The intermediate `Step` witness states that equality instead of asserting an
outer-context translation. WF′/WF/WF₂ keep their exact top-level contracts.
All direct general-strengthening/extraction calls in WF′ are now removed;
transitive checker admissions remain. The new replacement helper pins three
inherited projection admissions, and its equality bridge pins three projection admissions.
Full default builds and all selected regression fixtures pass on both
toolchains. No new admission is introduced.

**Registered recursor checker extension (October 20):** the actual generated
recursor scope now supplies a model extension with `CheckerEnv`. The proof
constructs each constant from its generated-type receipt and follows the
native name checks to prove insertion succeeds in parent order, preserving
old constants, equations and value translations. Selected-domain and pass
support, parameter-free statistics, matching universe lists and an empty
initial virtual context remain explicit. The insertion theorem retains the
existing checker/value-translation admissions and native lookup interfaces;
no new admission is introduced. Complete inductive registration, rule/iota
semantics, consumer migration and `AddInduct` remain open.
The expanded recursor regression and full default builds pass on Lean 4.29.0
and the separate Lean 4.33.0-rc2 integration candidate.

**Recursive rule translation stage:** rule-body receipts now use the model
after all mutual recursor signatures are inserted. The old constructor-stage
premise is impossible for fresh recursive calls; a formal constant-occurrence
obstruction and exact generated single/mutual RHS controls establish why.
Recursor types still translate before insertion. All five checked rule bodies
typecheck after registration; recursive bodies fail on missing recursors
before it. The audit retains the existing projection admission and excludes
known-false strengthening/confluence dependencies. Full rule translation and
iota soundness remain open.

**Typed recursive calls and values:** a translated inserted recursor signature
now supplies a typed constant in the caller's universes and local context.
The application proof substitutes each actual argument through its dependent
telescope, derives the final major argument from the recursive-field opening
trace, and closes the higher-order field arguments with lambdas. Shared
selected declarations supply their argument receipts directly from context
well-formedness. The stored signature now also supplies its raw type through
the inverse implicit-binder pass. In the generated universe context, preserved
shared declarations derive the actual signature prefix; applying the changed
indices and closing the field arguments produces a value at its generated IH
domain. An alignment bridge supplies the annotation-peeled IH binder type.
This generated-context proof inherits 11 axioms on both toolchains; arbitrary
caller-universe instantiation retains its existing 16/19-axiom manifests.
The actual translated field terminal now supplies individual changed-index
typing from a typed partial family header and a native correspondence of
successively instantiated domains. This handles dependent indices without
assuming their individual translations or typings. The argument recovery
inherits seven axioms; the complete generated IH-value proof retains eleven
on both toolchains. The checked header batch now supplies the partial-family
input and its actual normalized residual signature. Native sort telescopes
discharge header/parameter normalization support constructively; general
headers retain those support obligations. The input transports through recursor
registration, universe extension and rule-context insertion. The older generic
checker normalization route still reaches known-false strengthening and is
excluded by the new proof audit. The actual translated index trace now
reconstructs a definitionally equal signature from the peeled declarations;
selected binding agreement derives native domain correspondence after changed
dependent substitutions. This removes the complete domain-correspondence premise
from the new field consumer. Its reconstruction/converted-consumer manifests
contain seven/eleven inherited axioms and exactly five existing projection
admission roots, excluding known-false strengthening/confluence. The new fixture
checks 384 actual generated telescopes, including 576 normalization changes and
384 peeled dependent domains. Canonical major/motive-tail alignment is now derived after changed-index
substitution from selected declarations and accepted family comparison. The
converted generated-IH consumer retains actual closure, freshness and parent
selection obligations; field-opening support and shared-binding preservation
for every rule remain open.
Full RHS translation,
rule/iota semantics and frontend soundness remain open. The proofs exclude
known-false strengthening/confluence results and add no admission. Three
actual higher-order values in parameterized indexed and mutual indexed
families match their instantiated minor/IH domains; malformed indices,
other-parent motives and higher-order arguments are rejected on both versions.
A further fixture checks a fourth value with two dependent indices, rebuilding
the actual family prefix and substituting each index through its domain;
malformed final indices, mismatched domains and non-Pi sources are rejected.
Proof audits throughout the fixture suite now explicitly request theorem and
opaque values, covering Lean 4.33's changed accessor default. A regression
must reach an existing projection admission through a theorem proof and
reject that path when forbidden. All updated audits pass on their respective
toolchains. Three older quotient diagnostics now distinguish direct proof
checks from their measured inherited admissions. Kernel proof obligations
and admission counts are unchanged.

**Generated IH opening and minor application bridge (October 20):** the actual
translated IH step now consumes a generated recursive value and its translated
native domain at the annotation-peeled IH binder, preserving the value
translation while converting its type through the opening equality. A second
bridge packages typed field/IH argument sequences into the peeled minor
application used by a rule RHS. These theorems are producer/consumer seams:
the all-rule CPS producer still must supply each generated value, shared field
opening, minor binder and exact argument sequence. Their six owned
declarations add no admissions and retain only the existing structural
translation interfaces. The native telescope bridge consumes the actual
successively instantiated argument proof and exposes the same typed minor
application without hiding any source or terminal premise. The peeled-domain
specialization reuses the opening translation and leaves only model/context
conversion explicit. Native argument receipts now transport across the
minor context extension without changing native telescopes or replacements.
Full RHS
translation, iota semantics, rejection consumer migration and `AddInduct`
remain open.

**Universal candidate reduction simulation:** every actual `NormalEq` in a
well-formed environment with the quotient rule registered now simulates every
candidate `Step`, and every finite candidate `Steps` path, using candidate
paths on the left and a direct final normal comparison. Both outputs retain
any supplied original type. This includes neutral Prop-source unfolding,
root eta expansion, original checked reduction and congruence under changing
dependent binders. All 155 audited roots exclude admissions and choice on
both versions. Confluence, admission-free normal-equality transitivity,
conversion-consumer migration and frontend soundness remain open.

**Inhabited normal-equality context conversion:** `NormalEq.weak_inv_of_hasType`
pulls a lifted normal equality back through one binder by instantiating a
typed inhabitant. The proof is a direct use of the admission-free simultaneous
normal-substitution API and its audit allows only `propext` and `Quot.sound`.
It supplies the constructive inhabited case while the unrestricted inverse
weakening theorem remains false and conditional.

**Constructive inductive registration alignment:**
`NativeInductive.RegistrationEvidence.aligned` now consumes the existing
header, constructor, and generated-recursor registration receipts and
transports `Aligned` through all three staged model extensions. The proof
checks each native constant's translated type, freshness, model-name shape,
and map equation against the corresponding `VEnv` insertion. It covers
arbitrary definition-safety levels by lowering the safe receipt. The
executable frontend is unchanged; `AddInduct` and full recursor semantics
remain open.

The constructive registration receipts now also expose positive exact map
lookups. `AddInductEvidence.lookupReceipt` derives the inserted header and
constructor values from freshness, name alignment, `Forall₂` translations,
and map well-formedness; `AddInductWithRecursorsEvidence.recursorLookup`
does the same for every generated recursor. These receipts make the model
entries available to checker-facing consumers while retaining the explicit
staging and translation premises. They do not complete `AddInduct`, the
inductive frontend, or recursor/iota soundness.

`AddInductWithRecursorsEvidence.lookupReceipt` now transports the header and
constructor lookups through the generated-recursor insertion and returns all
three exact lookup families in the final constant map. A regression consumes
this combined receipt through actual `RegistrationEvidence`; no lookup is
obtained by assuming a map equation without its freshness and no-duplication
premises.

`NativeInductive.RegistrationEvidence.orderedEntryLookup` now exposes the
checker-facing form of that invariant: every ordered header, constructor, and
generated-recursor entry has its exact `ConstantInfo` in the final model map.
The proof converts the ordered fresh/model-shaped registration batch to the
constructive `insertConsts` lookup principle and retains the explicit recursor
WF callback at the registration boundary.

`SafeInductiveFrontendScope.toCheckerEnvInductive_and_orderedEntryLookup` now
returns that exact lookup receipt alongside the constructed checker environment,
transporting the native scope's constant-map equality and WF proof through the
registration bridge. This connects the final model-map invariant to a
checker-facing frontend package without changing executable behavior.

**Universal original-core simulation:** every actual `NormalEq` in a
well-formed environment with the checked quotient rule registered now simulates
any original parallel step, and any finite original-core path, using the
repaired left paths. The complete application clause handles arbitrary left
functions and majors, actual capture reductions/checks, retained eta binders,
root beta and congruence. Both outputs keep the supplied original type. All 100
audited roots exclude admissions and choice on both versions. The original
Prop-source counterexample is simulated by repaired paths and still refutes
the old core-only target. The broader candidate-step and finite-path result
is proved above; confluence, consumer migration and frontend soundness remain open.

**Nonzero quotient exposure and actual EXTRA replay:** a normal comparison
with `Quot.mk` now exposes an actual left constructor at a nonzero source.
Actual Quot rigidity and sort typing eliminate the residual eta/Pi alternative.
For an explicit left `Quot.lift α r β f c major` prefix, recursive simulations
of the function capture and original major now suffice to replay actual root
EXTRA after every right capture reduces. The proof reconstructs both actual
pattern checks and retains the original result type. Controls start with a
left major that does not match, distinct domain/relation parameters, and a
retained dependent binder. All 65 audited roots exclude admissions and choice
on both versions. This explicit-prefix result is generalized by the complete
application and universal core-simulation theorems above; confluence repair
and frontend soundness remain open.

**Type uniqueness and dependent Pi injectivity:** the original stratified Pi
inversion now has a proof with both exact height bounds. Structural Strong
uniqueness gives heterogeneous type chains; collapsing them at the actual left
universe proves ordinary uniqueness and inverts arbitrary untyped Pi equality.
The original `IsDefEq.uniq` proof is unchanged and now excludes admissions,
choice and confluence. Its equality/conversion consequences are independently
audited. Dependent beta domains/codomains, heterogeneous chains, real delta and
quotient derivations, converted types, and unequal heights with distinct
but equivalent codomain universes pass on both toolchains. The lower uniqueness
module has no import path through the original consumers or confluence.
Inverse weakening later in `UniqueTyping.lean`, the false reduction/confluence
contract, projection translation and frontend soundness remain open.

**Ordinary soundness and head separation:** the original sort-injectivity and
sort/Pi-separation admissions are now proved with unchanged contracts, using
only `propext` and `Quot.sound`. Actual ordinary derivations inherit simultaneous
model soundness through the independently clean Strong conversion. Actual WF
history supplies all four chain-injectivity fields: universe equality, dependent
Pi chains, rigid head/argument equality and stored-telescope argument equality.
The model also separates actual rigid Quot spines from Pi types. Its import
graph excludes the old injectivity, uniqueness and confluence modules. Strict
197/204-root audits include the moved foundational helpers and existing
consumer names. Dependent beta chains, real ordinary/Strong quotient EXTRA
and a two-argument Quot spine are checked. Original dependent-Pi injectivity
and type uniqueness are now proved above; concrete nonzero root replay is supplied
above, and universal original-core simulation is now proved with repaired paths.
Universal candidate-step simulation is also proved above; confluence and
frontend soundness remain open.
Earlier dated checkpoint accounts below are superseded by this boundary.

**Actual rule validity and Strong-derivation soundness:** declaration history now
supplies quotient constants, family/constructor rigidity and unique ownership.
The actual quotient equation is valid at its stored type, including its
zero-level proof-field case. Together with delta validity this discharges every
stored-rule obligation of the simultaneous induction. `sound_of_wf` proves both
semantic inclusions and both endpoint semantic typings for actual Strong
derivations in a well-formed source included in a well-formed target. Its 131
strictly audited roots exclude admissions and choice. Ordinary frontend
soundness and the remaining consumer migration remain open; ordinary source
soundness and head separation are supplied above.

**Constructor-pattern rule soundness:** the rule argument now proves both
semantic inclusions for the current constructor-observation and proof-binding
alternatives. It retains actual stored membership, head-type filtering,
dependent binder typing and the actual endpoint equality. Finite extraction,
first occurrences, field indices and the level-zero decision avoid choice.
Actual declaration history identifies every stored constructor pattern as the
quotient equation and excludes competing delta equations at its head. All 200
audited roots exclude admissions and choice. The remaining quotient family
and proof-field premises are now instantiated by actual quotient validity above.

**Finite dependent telescope round trips:** reverse spine transfer now
recovers actual argument typings and reconstructs each domain/result type
observation as a chain at the stored constant type. Actual argument observation
sets form a typed valuation of every prefix of a sound telescope. Finite demands
then produce finite backed keys, including earlier demands needed to type later
ones; winding those keys rebuilds a typed head observation at the actual
application class. Controls exercise a dependent two-argument spine through
beta conversion, partial application, representative replacement and discovery
of an earlier demand omitted from the input. All 138 audited roots exclude
admissions and choice on both versions. Actual quotient-rule validity is now
supplied above.

**Constructive rule binding:** the rule-soundness foundation now recovers
actual dependent binder types, splits typed key telescopes, transfers typed
valuations between related anchors, and inverts rigid and constructor spines.
Every binder's observation set has a finite list representation selected by
finite induction, without choice. Controls transfer nonempty observations
between distinct beta-equivalent anchors and recover the actual third argument
class of the installed Quot.mk constructor. The exact 173-root audit excludes
admissions, choice and the false confluence foundation on both versions.
Actual quotient validity and Strong-derivation soundness are now supplied above;
ordinary frontend foundations remain open.

**Actual delta-rule validity:** every stored bare-constant equation of a
well-formed environment is now valid in its observation model, using actual
declaration-history lookup, head ownership and constructor rigidity. The
simultaneous induction therefore proves soundness and semantic typing of both
endpoints for actual strong derivations in well-formed source environments
without the quotient equation. They can be interpreted in later well-formed
environments containing the actual quotient equation. Controls include two
polymorphic unfoldings, related anchors, and a function-valued definition with
nonempty finite observation keys and a typed application. The 99-root audit
excludes admissions and choice on both versions. Validity of the quotient
equation and unrestricted Strong-derivation soundness are now supplied above;
the ordinary frontend foundation remains open.

**Semantic typing and simultaneous induction:** actual strong derivations now
produce observation soundness and semantic typing for both endpoints together,
conditional on validity of their actual stored equations. The no-equations
corollary discharges that premise from the source environment itself. Constant
spines recover the stored type, finite backed argument keys containing caller
demands, wrapped observation typing, and codomain/domain observation recovery.
Lambda spines recover body typing through dependent binders and nonreflexive
type conversion. The 121-root audit excludes admissions and choice on both
versions. HTS's syntax fallback alone does not certify actual typing; the
simultaneous theorem retains the actual strong derivation. Actual general
stored-rule and declaration-history validity and Strong-derivation soundness
are now supplied above; quotient/Pi separation and nonzero EXTRA remain open.

**Structural observation soundness:** application, lambda, conversion,
beta, eta, proof irrelevance and constant-level equality now preserve both
semantic inclusions and observation typing at related anchors. Together with
the variable, sort and Pi results below, every non-rule case of the actual
strong equality derivation has its simultaneous soundness proof. The
105-root audit excludes admissions and choice on both toolchains. Controls
reduce a dependent beta redex under a binder, change both an application's
function and argument, transport a lambda across different beta-equal anchors,
and retain duplicate eta demands and the original dependent result type.
These individual cases feed the simultaneous induction above. Actual stored-rule
soundness and declaration-history validity are now supplied above; quotient/Pi
separation and nonzero EXTRA remain open.

**Level invariance and dependent telescopes:** observations and their typing
now transfer across equivalent well-formed levels, including actual stored
rule bindings and delta bodies. Typed lambda/Pi telescopes can be constructed
and unwound; the dependent remainder transfers to any member of a key's
class using its codomain soundness induction hypothesis. Variable, sort and
the full dependent-Pi formation cases of simultaneous soundness are proved,
including typing at related anchors. The 115-root audit is admission-free
and choice-free on both toolchains. Controls derive their soundness premises
and change a beta-redex representative inside a genuinely dependent telescope.
Full expression/representative soundness, rule soundness and declaration-history
validity remain open, as do quotient/Pi separation and nonzero EXTRA.

**Expression observation interpretation:** anchored valuations now interpret
all six existing expression forms using actual stored constants and equations,
with typed backed keys and the original rule-binding conditions. Structural
weakening, substitution, instantiation, subsumption monotonicity, compactness,
closed-term invariance and hereditary backing are proved without admissions or
choice. The 139-root audit reads full types and bodies on both toolchains;
controls include a checked delta definition, the actual quotient equation and
nonempty finite demands under a binder. Level invariance and the initial
soundness cases are now supplied above. Full expression/representative and
rule/environment soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Constructive observation filter:** finite index maps now implement the
original contravariant coverage relation without global choice or decidable
equality on observations. Subsumption composes, finite demands admit
hereditary backing, and typed application survives coverage strengthening.
The filter's proof-irrelevance result and typed finite closure are proved;
86 roots have exact admission-free, choice-free manifests on both toolchains.
The structural interpreter is now supplied above. Interpretation soundness,
rule/environment soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Typed class foundation for separation:** heterogeneous sort-typed chains
and element-class collapse now yield actual typed definitional equalities,
without typing injectivity, confluence, admissions or choice. Application,
beta at any member of a typed argument class, related-anchor invariance and
actual function eta preserve the anchored classes. The 51-root audit pins
exact axiom manifests on both toolchains. This ports PR #53's necessary class
foundation; the constructive observation filter is now supplied above.
Interpretation soundness, quotient/Pi separation and nonzero EXTRA remain open.

**Nonzero quotient-major classification:** actual sort typings now prove
source-universe agreement for definitionally equal quotient types and recover a
constructor's source universe from its supplied result type. Any proof inhabiting
a quotient forces a zero-equivalent source, even for a neutral major. At a
nonzero source, arbitrary normal comparison to a constructor now exposes an
actual core path either to a literal constructor with all three related captures,
or to a lambda carrying an explicit equality between the original quotient type
and a Pi type. This eliminates both proof alternatives without false confluence.
Excluding the eta alternative still needs quotient/Pi separation; nonzero EXTRA,
universal simulation and actual-consumer migration remain open.

**General Prop-source application EXTRA:** hereditary exposure now follows
actual checked quotient firing from an arbitrary normally related left source,
beneath any finite related argument list, including retained dependent eta
binders. The complete application induction clause uses only the original
function and argument simulation hypotheses. All eight right captures may
reduce; their actual definitional equalities transport both rule checks before
the exposed left witnesses are joined. Both endpoints retain the original
supplied type. Exact audits retain only the two existing typing admissions.
The nonzero-source EXTRA clause still needs hereditary major exposure and
actual matching/check recovery. Universal simulation, confluence and
actual-consumer migration remain open.

**Universal hereditary constant-spine exposure:** any normal comparison to a
constant applied to captures now produces an actual original-core reduction
path to a proof, a literal related constant spine, or retained eta binders with
recursively exposed bodies. Simultaneous related substitution preserves this
structure, including dependent binder domains; applying related arguments
consumes eta binders by actual beta steps. The complete application theorem
handles any finite pending argument list and preserves both endpoint typings
at the original supplied type, without a recursive simulation premise.
Exact audits retain only the two existing typing admissions. The Prop-source
interpretation is now proved above. Nonzero-source EXTRA still needs to expose
the major and recover actual matching and checks.
Universal simulation, confluence and actual-consumer migration remain open.

**Checked quotient firing across related sources:** when both terms actually
match the quotient pattern, normal equality of the captures now derives the
left rule's two equality checks from the right checks at any source universe.
Only the function and payload need recursive simulation. A separate Prop-source
clause unfolds a saturated left eliminator with an arbitrary major, including
a neutral one, and joins its selected proof to the reduced right payload.
Both clauses use the actual checked right EXTRA and every captured parallel
reduction, construct a left candidate path, and preserve both original endpoint
types. Their exact graphs retain only the two existing typing admissions and
exclude choice, false confluence, inverse transport and normal transitivity.
These are firing clauses with explicit matching/component hypotheses. The
exposure result above supplies hereditary prefix structure; interpreting it
for nonzero-source checked firing remains open, as do universal simulation,
confluence and actual-consumer migration.

**General application beta simulation:** an arbitrary normally related
function can now follow beta on the right, with different normally related
arguments, without a left lambda-shape restriction or recursive simulation
premise in the beta-joining theorem. Forward beta preservation beneath retained
eta spines replaces inverse weakening; simultaneous substitution replaces
normal transitivity. The general application beta clause consumes just the
function/argument induction hypotheses and retains both original endpoint
types. Proof-valued functions also have their complete application clause.
Exact audits retain only the two existing typing admissions and exclude choice
and false confluence. Nonzero-source checked EXTRA still needs to connect
hereditary major exposure to its actual firing clauses. Universal simulation,
confluence and consumer migration remain open.

**Simultaneous substitution and lambda beta simulation:** related arguments
can now be substituted simultaneously into both endpoints of normal equality,
including eta with different dependent binder domains. The general proof has no
inherited source admission in either fork snapshot and avoids normal
transitivity and inverse weakening. Arbitrary candidate argument paths propagate
through duplicated occurrences beneath dependent binders. The actual lambda
beta clause combines recursive body/argument simulation, converted domains and
both endpoint typings at the original application type. Its exact trust boundary
is the two existing typing admissions. The general beta clause is now proved
above; checked EXTRA and the universal simulation remain open. The independent
substitution proof and strict regression are submitted as
[upstream PR #65](https://github.com/digama0/lean4lean/pull/65), with the official
master's additional inductive admissions explicitly audited there.

**Eta joins and replacement simulation clauses:** root eta expansion now joins
EVERY finite candidate path at an identical endpoint, including unfolding and
further eta steps. Eta/application joins also allow simultaneous candidate paths
in the function and argument and retain the original dependent result type.
The replacement `CoreSimulates` obligation has proved recursive clauses for all
eight non-application normal-equality constructors and application congruence.
These clauses still take their recursive simulation hypotheses. The general
application beta clause is now proved above; checked EXTRA remains open.
The eta proofs exclude inverse weakening, false confluence and choice, with exactly the
two independent typing admissions. Actual consumer manifests are unchanged.

**Canonical unfolding versus arbitrary core reduction:** every original
parallel successor of an unfoldable quotient application now joins its canonical
unfolding modulo `NormalEq`, with both endpoints at the original result type.
The congruence case has an identical endpoint; the proof recovers argument
reductions by classifying all proper lift prefixes and handles checked EXTRA
through the prior selector join. Exact trust gates retain only the two independent
typing admissions and exclude choice/false confluence. General normal-equality
simulation, new-step overlaps and actual-consumer migration remain open.

**Quotient rewrite overlap:** canonical Prop-source unfolding now joins the
original checked quotient EXTRA rule modulo `NormalEq`, including arbitrary
parallel argument reductions, syntactically different checked constructor
parameters and zero-equivalent source universes. Both endpoints keep the original
application type. Its complete graph excludes false confluence, derived quotient
injectivity, inverse weakening, projections and choice; exactly two independent
typing admissions remain. General simulation and actual consumer migration are
still open.

**Local-let cache transport:** entering and leaving local definitions preserve
the exact model context and expressions. All five actual state/cache producer
and restoration proofs now avoid generic native/projection weakening, false
strengthening and confluence, with only the existing `TrProj` placeholder in
each complete graph. Equivalence-manager transport preserves reflexive nodes
that mention the fresh identifier and carries their checked leaves unchanged.
Cache definitions, theorem contracts and accepted inputs are unchanged. Generic
lambda paths and broader frontend/model obligations remain open. The focused
master-based [PR #64](https://github.com/digama0/lean4lean/pull/64) now covers both
directions, with its own full build and strict provenance gates.

**Conditional gadget extraction:** the actual conditional recognizer now
closes its two Nat binders at zero and its three dependent reflection binders
at the gadget's own checked arguments. This follows upstream draft #53,
with local projection-free transport proofs preserving the existing contracts.
Its complete extraction graph drops general strengthening and inherits exactly
three existing projection/typing gaps; the whole recognizer's 33-axiom manifest
and broader checker gaps remain. No executable behavior changes.

**Native binder naming:** the actual `TrExprS.inst_fvar` API now preserves the
exact semantic context directly, across both declaration kinds and nested native
binders/projections. Its complete graph drops projection weakening and
instantiation, retaining exactly the existing `TrProj` placeholder. The existing
`TrExpr.openFreshFVar` consumer shares that reduction. Contracts and executable
behavior are unchanged, and the proof is validated on both toolchains. Broader
inference/frontend admissions remain. A focused master-based candidate is kept
separate; draft PR #53 already repairs this API through its larger redesign,
so no duplicate upstream PR is opened.

**Unused-let telescope reconstruction:** the actual `mkForall_trS`,
`mkLambda_trS` and `mkLet_trS` proofs now erase an unused native let directly.
A local let contributes no semantic binder, so retained projection evidence stays
in its original context. Each complete structural builder graph now inherits
exactly `TrProj`, dropping projection weakening; the converted APIs still inherit
other typing gaps. Existing contracts and checker behavior are unchanged.
Dependent-context, mixed-telescope and retained-let controls pass on both
versions. The focused [PR #64](https://github.com/digama0/lean4lean/pull/64)
now includes this consumer of its structural let-erasure proof. Arbitrary lambda
strengthening and whole inference/frontend soundness remain open.

**Projection core contract:** the Lean 4.33.0-rc2 integration now proves the
existing `reduceProjCore.WF` contract used by lazy projection comparison and
scoped methods. Its constructor-head rejection argument is shared with WHNF,
including checked normalization of string literals. This replays the core proof
already submitted in [PR #57](https://github.com/digama0/lean4lean/pull/57);
no duplicate contribution is opened. The source census loses one admission.
The older main worker was already proved; its regression now pins exactly the
remaining `TrProj` admission and seven axioms instead of accepting the entire
method baseline. General projection and frontend soundness remain open.

**Quotient-prefix application overlap:** expanding any partial `Quot.lift`
prefix and applying its generated lambda now provably joins applying first and
expanding the next prefix. The endpoints are identical terms at the original
dependent application type. All six partial lengths and a retained dependent
proof binder are checked. Computation uses no source admissions; the typed joins
retain exactly the two existing universe/function injectivity gaps. This advances
the candidate reduction presentation. The original false confluence contract,
general simulation, other overlaps and migration of checker consumers remain open.

The main remaining barrier is semantic: the non-inductive frontend is proved
without a direct admission, but its dependencies still include `sorryAx`.
Actual checked inductive/model registration and recursor semantics remain open.
Our executable also deliberately differs from upstream; this is not just a
proof-only patch set.

## Comparison snapshot

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
| Complete confluence and semantic reduction correctness | **Original simulation contract refuted:** the actual quotient model has a checked counterexample to `NormalEq.parRed`. Every actual normal equality now simulates every candidate step and finite candidate path, including original checked reduction, neutral Prop-source unfolding, eta expansion and congruence. Both outputs retain the supplied original type. | Confluence and related semantic obligations remain open. | Candidate confluence, admission-free normal-equality transitivity, migration of actual consumers, general strengthening, genuine projection and inductive recursor semantics. |
| Verify the full native arithmetic set | **Not complete:** many arithmetic contracts are proved, but GCD/AND/OR/XOR native reductions are disabled. | Newer primitive checking proofs and guards are available for review. | Restore those four operations with the actual primitive-extension proofs; close the well-founded validation gap. |
| Prevent demonstrated inductive source capture | **Concrete repair:** source preflight rejects capture inputs before generated names can bind them; native Lean 4.29.0 reproducer retained. | Native Lean 4.33.0-rc2 rejects this exact source constructor with `declHasFVars`, now regression-tested. | Version-bounded validation result, not a current native bug or a proof of logical unsoundness. |
| New semantic guarantees in the October 13 integration checkpoint | **None claimed.** Recursor/restoration, binder, header-typing, and transport proofs are restored against current APIs while preserving their existing contracts. | Compatibility preserves prior contracts; it is not a newly solved upstream obligation. | Submit only independently reviewable semantic or correctness changes after publication; keep compatibility repairs out of the progress score. |

Comparison anchors: our published proof source at
`4b3a958f89d999bc40ec6b409b135aa36108b8be`, and official
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

### Current integration checkpoint — October 19

Official `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` is an ancestor of this
integration; today's rebase check at its preceding checkpoint was a successful
no-op. The main Lean 4.29.0 review branch is still not based on that tip.
No force push is authorized or used. The validated snapshot is published
separately as `poc-verified-noninductive-upstream-20261019`.

The unchanged `reduceRecursor.WF` contract now composes the actual quotient
worker proof with inductive rejection in the constructor-free `TrEnv` model.
This removes its direct admission but retains inherited typing/confluence
admissions and native interface axioms. This upstream dispatcher accepts only
the expression argument; the older fork's cheap-flag interface is not added.
The abstract signature-registration model supplies constructive freshness,
lookup, extension, and orderedness proofs. It replaces three placeholders,
but does not establish positivity, generated recursor correctness, or genuine
checked inductive/model registration.

Rewrite metadata now handles every well-formed declaration history, including
upstream mutual definitions: all signatures are reserved before bodies are
checked, then their equations are registered. A new fixture checks a real
two-definition block whose second body uses the first constant, registered
equations and actual reduction, and duplicate-name rejection. These history
witnesses and general metadata proofs have no admissions or choice.

The quotient confluence obstruction is proved against the actual integration
model without depending on the refuted theorem, its confluence consequences,
derived quotient injectivity, or false strengthening. The typed Prop-source
and all-prefix unfolding preserve the original result type and are stable
under weakening, typed substitution, and context conversion. The strict
selector/completeness audits exclude admissions and choice. Full source typing
and model construction still inherit independent typing/injectivity admissions.
The old `NormalEq.parRed` contract remains false and admitted; general
simulation, confluence, eta overlaps, and downstream migration remain open.
The selector/prefix direction is attributed to upstream draft #53.

All 422 default build jobs and 33 fixtures pass on Lean 4.33.0-rc2,
including the quotient/model, primitive/frontend, and five existing integration
trust fixtures. Audits inspect theorem and opaque
bodies explicitly using `value? (allowOpaque := true)`, as required by the
newer API; no dependency allowlist is broadened. The source census decreases
from 129 matching lines / 133 occurrences to 125 / 129. This is evidence of
four direct admission removals, not unconditional frontend soundness.
Detailed contracts and receipts are in `PROOF_STATUS.md`.

### Earlier integration receipts — October 12

The following records describe intermediate checkpoints, not the current full
integration gate. The October 13 checkpoint above supersedes their stopping
points and broad statements about passing candidate targets.

Preparation on 2026-10-12 fetched the official snapshot above. A non-mutating
tip-to-tip merge preview reports conflicts across core checker and proof files;
it is not evidence of a completed rebase. Preserve both upstream correctness
fixes and this fork's verified contracts when resolving the integration.

An actual rebase is now **in progress in an isolated detached worktree**, based
on the same official tip. The published branch remains unchanged by that rebase.
The first environment/frontend replay is now reconciled at detached checkpoint
`c83d6b01209f9320fed46d11cc1e187a8c84219e`. It retains upstream's
body-before-primitive checks, mutual-block model, and theorem-as-Prop-constant
semantics while recovering this fork's **actual non-inductive, arbitrary-fuel,
batch, and empty-environment contracts**. The empty-model proof also accounts for
upstream's stage-2 constant map instead of changing runtime defaults.

That intermediate checkpoint passes **all default targets on Lean 4.33.0-rc2**
(161 jobs), a 20-theorem direct-admission/dependency audit, and three actual
checked runtime pipelines using different fuel configurations. The audit excludes
dependency on the admitted whole `addDecl.WF` theorem, but still inherits
`sorryAx` and the existing checker/native-interface axioms. No semantic admission
has been removed by this integration. The remaining fork commits are **not yet
replayed**: a green intermediate checkpoint is **not a completed rebase or
validation of the final branch**.

The next safe-definition replay is also reconciled at detached checkpoint
`dc217549a0e08a2f7006ba32a865867bf589765f`. It keeps upstream's stronger
primitive-extension proofs, metadata-aware type comparisons, and all fourteen
binary native arithmetic/predicate branches instead of replaying the fork's
historical temporary arithmetic removals. The fork's primitive-only extension
contract is recovered from the actual, stronger declaration theorem.

All default targets and both candidate fixtures pass. Actual fresh-slot checks
for `Nat.add`, `Char.ofNat`, and `String.ofList` accept domain metadata, reject
misplaced metadata and invalid safety/universe parameters, and check the String
constructor dependencies. An ill-typed primitive body is rejected before
recognizer probes. Direct native reductions pass without fallback unfolding.
These runtime controls use a native prelude and are **not a proof of its model
translation**; primitive proof audits still inherit the upstream checker trust
baseline. This is compatibility/preservation evidence, not a newly completed
primitive soundness milestone. The published branch's four disabled operations
remain disabled until the full rebase is validated and published.

The restricted and remaining-non-inductive frontend replays are reconciled at
`9a95087ca626e04ecaf2c4557f0992102531dac6` and
`f9879f700b003dc6e517edf550bb95873f6eb353`. The actual verified wrapper again
handles every non-inductive declaration form with arbitrary fuel, retaining
upstream's checked unsafe/mutual-block model and the fork's fuel-sensitive,
fresh-name-checked quotient worker. Native-prelude controls check quotient
headers against the actual upstream worker, reject invalid equality/reflexivity
headers and name collisions, and preserve exhausted-fuel rejection and
initialized idempotence. Three additional checked pipelines accept recursive
unsafe/partial bodies while rejecting safe dependencies on them, invalid mutual
blocks, wrong proofs, duplicate names, and inductive declarations.

**The quotient semantic boundary is still open:** successful initialization
requires inductive `Eq`, which the current `TrEnv` cannot translate. Both
initialization preservation proofs are therefore vacuous in their uninitialized
case. Passing native-prelude bootstrap controls does not supply that missing
model or establish constructive quotient-registration soundness.

The candidate retains upstream's native `deltaValue?` semantics and its actual
unfolding proof instead of the fork's historical safe-only delta scaffolding;
wrong universe arities and opaque unfolding still reject. The published branch
continues to use its previous behavior. All default targets and four candidate
fixtures pass. Audited proof bodies introduce no direct admissions or new axioms,
but still inherit `sorryAx` and the existing native/checker interfaces. These are
preserved contracts and explicit remaining obligations, not an admission-free
frontend milestone.

The original-level-normalization replay is reconciled at
`785d1daba69314c7b09f3bec90b806cfe2a2a714`. It restores the total
flatten/sort/subsume helper and its named-valuation preservation proof **without
replacing upstream's complete canonical comparison/equivalence checks with the
older incomplete core-only path**. Sixteen level-contract audits exclude both
direct admissions and inherited `sorryAx`; existing native level and tree-map
interface axioms remain. The broader frontend still inherits admissions.

Candidate regressions reproduce valid inequalities/equivalences that the native
fast paths reject, and prove their acceptance using the actual public
completeness contracts. The total helper matches the installed native normalizer
on 3,280 small and 10,000 generated inputs; the complete fallback additionally
accepts 2,216 comparisons and 207 equivalences in that generated corpus. These
are controls against a semantic regression, not a proof of full syntactic
agreement with the native normalizer. Completeness still requires successful
`VLevel.ofLevel` translations; six metavariable controls establish syntax
agreement only. All default targets and five candidate proof/runtime fixtures
pass. The rebase stops cleanly before the module-region cleanup replay; final
integration and publication remain unfinished.

The module-region cleanup and Nat.add replay are now reconciled in the isolated
candidate at `0af54e3` and `0fb93bc`. The cleanup preserves upstream's stronger
`Replay.replayFromImports` lifetime fix: module-region handles are projected
before `Environment.freeRegions`, avoiding dangling references during deferred
decrements. The original primitive patch's historical `checkPrimitiveDef` was
superseded by upstream's extracted typed local-probe clauses, so its obsolete
wrapper edits are not mechanically reintroduced. The candidate retains the
actual current Nat.add checker and adds the original recurrence/evaluation and
reflection contract as `VEnv.NatAddSpec`, with direct proof-body audits and
negative/positive lambda-domain controls.

The Nat.add compatibility fixture validates literal evaluation and reflection
from the two open equations, while `tests/Primitive.lean` checks that equation
wrappers use well-typed lambda binders and reject forall-shaped or wrong-domain
wrappers. The stronger current primitive clause proof remains the source of
recognizer preservation; the compatibility contract is not a new admission-free
kernel theorem. Its arithmetic proof inherits the existing `sorryAx`/classical
typing baseline, which is recorded rather than hidden. All prior level,
environment, frontend, quotient, and primitive fixtures continue to pass. The
rebase is clean at deliberate break 15 of 327, before the primitive-frontend
connection replay; final integration and publication remain unfinished.

### Upstream contributions

After the initial rebase passes its full validation, submit one coherent,
reviewable proof or correctness fix **as soon as it is ready**, normally one
reviewable item at a time; batch tiny dependent changes. Do not accumulate
another large divergent stack or open PRs merely for module additions. Pending
review does not block continuing verification. Re-check official master to
avoid duplicate work, build on its current toolchain,
include regression and transitive-axiom evidence, and keep fork-only status
documents out of the PR. No PR has been opened for this integration checkpoint.

First evaluate the closed quotient-equation pattern repair and the constant-case
confluence proof. Do not submit the substitution port: it already came from
upstream. Reassess the source-preflight contribution against upstream's own
checks; the tested native capture input is already rejected by Lean 4.33.0-rc2.

## Behavioral differences and findings

Our executable includes a restricted verified frontend, additional primitive
validation, safe-only delta unfolding, a replacement level implementation, and
stricter inductive source preflight. The main Lean 4.29 worker still disables native `Nat.gcd`, `Nat.land`,
`Nat.lor`, and `Nat.xor`; this Lean 4.33 integration retains upstream's enabled
reductions and their existing verification obligations.

[bugs-found.md](bugs-found.md) documents a native inductive source-variable
capture reproducer on **Lean 4.29.0**. This is an input-validation bug, not a
demonstration of logical unsoundness. Native Lean **4.33.0-rc2 rejects this exact
input**, as checked by `tests/NativeInductiveSourceRejection433.lean`; no upstream
report has been submitted. The quotient
equation-pattern and native-instantiation repairs are specification mismatches,
not additional native kernel bugs. See [divergences.md](divergences.md) for the
precise boundaries and reproducers.

## Validation and admission accounting

The current main Lean 4.29.0 proof source passes all default targets (456 jobs)
and all 42 selected regressions on October 19. This Lean 4.33.0-rc2 integration
passes its full default build (459 jobs) and all 70 selected regressions. The
independent current-master substitution PR passes its default build and
standalone regression. Each receipt validates its respective source snapshot;
exact trust bounds are recorded in `PROOF_STATUS.md`.

| Whole-word `sorry` or `admit` source census, October 19 | Published proof source | Local integration | Official master |
| --- | --- | --- | --- |
| Matching lines | 116 | 121 | 133 |
| Files containing matches | 18 | 22 | 29 |
| Occurrences | 120 | 125 | 137 |

This deliberately includes comments and `Experimental` sources. It is a source
census, **not an audit of theorem trust**: removing one admission does not make
every theorem depending on it admission-free, and adding substantial proved
code does not make the raw totals comparable as percentages. Both branches
retain foundational admissions. Our actual frontend's transitive `sorryAx`
dependency is the more important signal.

This integration removes three abstract signature/model placeholders and the
actual recursor dispatcher admission. Proved sort injectivity and sort/Pi
separation remove two more occurrences in both trees; original dependent-Pi
injectivity removes another. Nonzero constructor exposure and actual EXTRA
replay add no admission. The remaining `sorryAx` dependencies, including the
known-false confluence contract, remain explicitly conditional. Raw counts do not replace the dependency audits.

## Next priorities

1. Finish the actual upstream rebase, preserve verified contracts and upstream
   fixes, validate it, and publish only with the required explicit lease permission.
   Then submit focused, validated upstream contributions rather than rebuilding
   a large divergent patch stack.
2. Repair the demonstrated false `NormalEq.parRed` contract while preserving
   semantic conversion and accepted declarations. Universal original-core
   simulation by repaired paths is proved. Complete candidate unfolding/eta
   simulation, confluence and downstream migration. Close inverse weakening and
   genuine projection/inductive recursor semantics; the dispatcher proof here
   still depends on those foundations and constructor-free rejection.
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
