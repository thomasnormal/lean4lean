import Lean4Lean.Verify.InductiveRecursorTypeTranslationCPS
import Lean4Lean.Verify.InductiveRecursorApplicationTranslation
import Lean4Lean.Verify.InductiveGeneratedRuleResult
import Lean4Lean.Verify.InductiveIndexDomainStrengthening

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved)
open private readWF bindWF from Lean4Lean.Verify.InductiveStats

def RecursorSelectedDomainSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (full : LocalContext) (initial : MLCtx) : Prop :=
  ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
    ∃ projected, SelectedRecursorTelescope env universes full initial ids projected

/- The translated parent/minor endpoint already contains a model extension for
   every allocated recursor binder.  Once native allocation order is aligned
   with `recursorTypeBinders`, that extension itself supplies the semantic
   selected-domain telescope.  Keep the alignment as a premise: the endpoint
   does not manufacture a native binder-order equation. -/
theorem RecursorInfoModelEndpoint.selectedDomainSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx} {parent : Nat}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (alignment : ∀ ids, IndexMLCtxExtension initial ids final →
      (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar) :
    RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial := by
  obtain ⟨ids, extension⟩ := endpoint.extension
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have telescope : SelectedRecursorTelescope env universes finalReader.lctx initial ids final := by
    simpa only [finalNative] using extension.selectedTelescope finalWF
  exact ⟨ids, alignment ids extension, final, telescope⟩

/- The endpoint's extension is chronological: all parent-pass allocations are
   completed before the minor pass starts.  Expose both phases separately so
   a caller can compare native allocation order with the recursor-type binder
   order instead of silently treating the aggregate list as canonical. -/
theorem RecursorInfoModelEndpoint.passExtensions
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final) :
    ∃ parentModel parentIds minorIds,
      IndexMLCtxExtension initial parentIds parentModel ∧
      IndexMLCtxExtension parentModel minorIds final ∧
      IndexMLCtxExtension initial (parentIds ++ minorIds) final := by
  rcases endpoint with ⟨parentInfos, parentReader, parentModel, parentTrace, minorTrace,
    parentHistory, minorHistory⟩
  obtain ⟨parentIds, parentExtension⟩ := parentHistory.extension
  obtain ⟨minorIds, minorExtension⟩ := minorHistory.extension
  exact ⟨parentModel, parentIds, minorIds, parentExtension, minorExtension,
    parentExtension.trans minorExtension⟩

/- A chronological extension can be cut at any list split.  This is the
   small context fact needed to rebase a domain translated at its allocation
   prefix into the final context, even when the recursor type later groups
   that binder after a dependency allocated in a later pass. -/
theorem IndexMLCtxExtension.split
    {initial final : MLCtx} {ids left suffix : List FVarId}
    (extension : IndexMLCtxExtension initial ids final)
    (shape : ids = left ++ suffix) :
    ∃ middle,
      IndexMLCtxExtension initial left middle ∧
      IndexMLCtxExtension middle suffix final := by
  induction extension generalizing left suffix with
  | nil =>
    have shape' : left = [] ∧ suffix = [] := by simpa using shape
    obtain ⟨rfl, rfl⟩ := shape'
    exact ⟨initial, .nil, .nil⟩
  | @push oldIds model earlier identifier name domain semantic binder ih =>
    have shape' : oldIds ++ [identifier] = left ++ suffix := shape
    by_cases hleft : left.length ≤ oldIds.length
    · obtain ⟨remainder, oldShape, suffixShape⟩ :=
        (List.append_eq_append_of_length_le hleft).mp
          shape'.symm
      obtain ⟨middle, prefixExtension, remainderExtension⟩ := ih oldShape
      refine ⟨middle, prefixExtension, ?_⟩
      rw [suffixShape]
      exact remainderExtension.push identifier name domain semantic binder
    · have oldLePrefix : oldIds.length ≤ left.length := by
        exact Nat.le_of_lt (Nat.lt_of_not_ge hleft)
      obtain ⟨remainder, prefixShape, idShape⟩ :=
        (List.append_eq_append_of_length_le oldLePrefix).mp
          shape
      have remainderLength : remainder.length + suffix.length = 1 := by
        simpa only [List.length_singleton, List.length_append] using
          (congrArg List.length idShape).symm
      cases remainder with
      | nil =>
        have suffixShape : suffix = [identifier] := by simpa using idShape.symm
        have leftShape : left = oldIds := by simpa using prefixShape
        subst left
        subst suffix
        exact ⟨model, by simpa only [List.append_nil] using earlier,
          .push .nil identifier name domain semantic binder⟩
      | cons remainderHead remainderTail =>
        have remainderTailLength : remainderTail.length = 0 := by
          simp only [List.length_cons] at remainderLength
          omega
        have remainderTailNil : remainderTail = [] :=
          List.eq_nil_of_length_eq_zero remainderTailLength
        subst remainderTail
        have suffixLength : suffix.length = 0 := by
          simp only [List.length_cons, List.length_nil] at remainderLength
          omega
        have suffixNil : suffix = [] := List.eq_nil_of_length_eq_zero suffixLength
        subst suffix
        have identifierEq : remainderHead = identifier := by simpa using idShape.symm
        subst remainderHead
        have leftShape : left = oldIds ++ [identifier] := prefixShape
        subst left
        refine ⟨_, ?_, .nil⟩
        change IndexMLCtxExtension initial (oldIds ++ [identifier])
          (MLCtx.vlam identifier name domain semantic binder model)
        exact .push earlier identifier name domain semantic binder

/- The domain receipt also retains the suffix extension from the allocation
   prefix to the final model.  This is what supplies the weakening used by
   the rebase side of the grouped-order receipt. -/
theorem SelectedRecursorTelescope.domainReceiptWithSuffix
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final : MLCtx} {ids : List FVarId}
    (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (identifier : FVarId) (member : identifier ∈ ids) :
    ∃ preIds suffix model physicalIndex name domain binder semantic,
      ids = preIds ++ identifier :: suffix ∧
      SelectedRecursorTelescope env universes full initial preIds model ∧
      IndexMLCtxExtension model (identifier :: suffix) final ∧
      full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default) ∧
      model.lctx.find? identifier = none ∧
      TrExprS env universes model.vlctx domain semantic ∧
      env.IsType universes.length model.vlctx.toCtx semantic := by
  revert identifier
  induction telescope with
  | nil =>
    intro identifier member
    cases member
  | @push previous model earlier identifier physicalIndex name domain binder semantic
      lookup fresh translated typed earlierInduction =>
    intro selected member
    rcases List.mem_append.mp member with oldMember | newMember
    · obtain ⟨preIds, suffix, prefixModel, oldPhysical, oldName, oldDomain, oldBinder,
        oldSemantic, oldIds, oldTelescope, oldSuffix, oldLookup, oldFresh,
        oldTranslated, oldTyped⟩ := earlierInduction _ oldMember
      refine ⟨preIds, suffix ++ [identifier], prefixModel, oldPhysical, oldName,
        oldDomain, oldBinder, oldSemantic, ?_, oldTelescope, ?_, oldLookup,
        oldFresh, oldTranslated, oldTyped⟩
      · simpa [List.append_assoc] using congrArg (fun xs => xs ++ [identifier]) oldIds
      · simpa [List.append_assoc] using
          oldSuffix.trans (.push .nil identifier name domain semantic binder)
    · rcases List.mem_singleton.mp newMember with rfl
      refine ⟨previous, [], model, physicalIndex, name, domain, binder, semantic,
        ?_, earlier, (.push .nil _ name domain semantic binder), lookup,
        fresh, translated, typed⟩
      simp

/- A dependency-aware virtual-context rebase keeps the semantic prefix for each
   binder instead of pretending that a `List.Perm` can reorder an
   `IndexMLCtxExtension`.  The grouped list is only an outer presentation order;
   each domain is still translated in the chronological model where its native
   declaration was allocated. -/
structure DependencyAwareVirtualContextRebase
    (env : VEnv) (universes : List Name) (full : LocalContext)
    (initial final : MLCtx) (chronological grouped : List FVarId) : Prop where
  chronologicalExtension : IndexMLCtxExtension initial chronological final
  groupedOrder : grouped.Perm chronological
  domainReceipt : ∀ identifier, identifier ∈ grouped →
    ∃ preIds suffix model physicalIndex name domain binder semantic,
      chronological = preIds ++ identifier :: suffix ∧
      IndexMLCtxExtension initial preIds model ∧
      IndexMLCtxExtension model (identifier :: suffix) final ∧
      full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default) ∧
      model.lctx.find? identifier = none ∧
      TrExprS env universes model.vlctx domain semantic ∧
      env.IsType universes.length model.vlctx.toCtx semantic

/- A grouped-order receipt deliberately separates native allocation order from
   the order used by the recursor type.  Every domain keeps its chronological
   allocation prefix and a proved weakening into the final model. -/
structure RecursorBinderRebaseReceipt
    (env : VEnv) (universes : List Name) (stats : InductiveStats)
    (infos : Array RecInfo) (parent : Nat) (full : LocalContext)
    (initial final : MLCtx) (chronological grouped : List FVarId) : Prop where
  chronologicalExtension : IndexMLCtxExtension initial chronological final
  groupedOrder : grouped.Perm chronological
  groupedBinders : (recursorTypeBinders stats infos parent).toList = grouped.map Expr.fvar
  domainReceipt : ∀ identifier, identifier ∈ grouped →
    ∃ preIds suffix model physicalIndex name domain binder semantic,
      chronological = preIds ++ identifier :: suffix ∧
      IndexMLCtxExtension initial preIds model ∧
      IndexMLCtxExtension model (identifier :: suffix) final ∧
      full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default) ∧
      model.lctx.find? identifier = none ∧
      TrExprS env universes model.vlctx domain semantic ∧
      env.IsType universes.length model.vlctx.toCtx semantic ∧
      VLCtx.FVLift' model.vlctx final.vlctx 0
        (.skipN .refl (identifier :: suffix).length) 0 ∧
      TrExprS env universes final.vlctx domain
        (semantic.lift' (.skipN .refl (identifier :: suffix).length)) ∧
      env.IsType universes.length final.vlctx.toCtx
        (semantic.lift' (.skipN .refl (identifier :: suffix).length))

theorem RecursorBinderRebaseReceipt.dependencyAwareRebase
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped) :
    DependencyAwareVirtualContextRebase env universes full initial final chronological grouped := by
  refine ⟨receipt.chronologicalExtension, receipt.groupedOrder, ?_⟩
  intro identifier member
  obtain ⟨preIds, suffix, model, physicalIndex, name, domain, binder, semantic,
    idsShape, prefixExtension, suffixExtension, lookup, fresh, translated, typed, _, _, _⟩ :=
    receipt.domainReceipt identifier member
  exact ⟨preIds, suffix, model, physicalIndex, name, domain, binder, semantic,
    idsShape, prefixExtension, suffixExtension, lookup, fresh, translated, typed⟩

/- Transport a dependency-aware domain from its chronological allocation prefix
   into the final virtual context.  This is the basic semantic rebase operation;
   it does not manufacture a reordered well-formed `MLCtx`. -/
theorem DependencyAwareVirtualContextRebase.finalDomainSupport
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (rebase : DependencyAwareVirtualContextRebase env universes full initial final
      chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes)
    (native : final.lctx = full) (identifier : FVarId) (member : identifier ∈ grouped) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default) ∧
      final.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) ∧
      TrExprS env universes final.vlctx domain semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  have chronologicalMember : identifier ∈ chronological :=
    rebase.groupedOrder.mem_iff.mp member
  obtain ⟨preIds, suffix, model, physicalIndex, name, domain, binder, sourceSemantic,
    idsShape, prefixExtension, suffixExtension, lookup, fresh, translated, typed⟩ :=
    rebase.domainReceipt identifier member
  have suffixWeakening : VLCtx.FVLift' model.vlctx final.vlctx 0
      (.skipN .refl (identifier :: suffix).length) 0 := by
    simpa only using suffixExtension.weakening.toFVLift'
  have rebasedTranslation : TrExprS env universes final.vlctx domain
      (sourceSemantic.lift' (.skipN .refl (identifier :: suffix).length)) := by
    exact translated.weakFV' envWF.ordered suffixWeakening finalWF.tr.wf
  have rebasedTyped : env.IsType universes.length final.vlctx.toCtx
      (sourceSemantic.lift' (.skipN .refl (identifier :: suffix).length)) := by
    obtain ⟨level, typedDomain⟩ := typed
    exact ⟨level, typedDomain.weak' envWF.ordered suffixWeakening.toCtx⟩
  have initialWF : initial.WF env universes := by
    simpa only [rebase.chronologicalExtension.drop_eq] using
      MLCtx.WF.dropN chronological.length rebase.chronologicalExtension.bound finalWF
  have telescope : SelectedRecursorTelescope env universes full initial chronological final := by
    simpa only [native] using rebase.chronologicalExtension.selectedTelescope finalWF
  obtain ⟨_, projectedIndex, finalName, finalDomain, finalBinder, fullLookup, finalLookup⟩ :=
    telescope.lookups initialWF identifier chronologicalMember
  have declarationEq := Option.some.inj (lookup.symm.trans fullLookup)
  cases declarationEq
  refine ⟨physicalIndex, projectedIndex, name, domain, binder,
    sourceSemantic.lift' (.skipN .refl (identifier :: suffix).length), lookup, finalLookup,
    rebasedTranslation, rebasedTyped⟩

theorem RecursorInfoModelEndpoint.rebaseBinderOrder
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (grouped : List FVarId)
    (order : ∀ chronological, IndexMLCtxExtension initial chronological final →
      grouped.Perm chronological)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar) :
    ∃ chronological,
      RecursorBinderRebaseReceipt env universes stats infos 0 finalReader.lctx initial final
        chronological grouped := by
  obtain ⟨chronological, extension⟩ := endpoint.extension
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have telescope : SelectedRecursorTelescope env universes finalReader.lctx initial
      chronological final := by
    simpa only [finalNative] using extension.selectedTelescope finalWF
  refine ⟨chronological, ⟨extension, order chronological extension, alignment, ?_⟩⟩
  intro identifier member
  have permutation := order chronological extension
  have chronologicalMember : identifier ∈ chronological := permutation.mem_iff.mp member
  obtain ⟨preIds, suffix, model, physicalIndex, name, domain, binder, semantic,
    idsShape, prefixTelescope, suffixExtension, lookup, fresh, translated, typed⟩ :=
    telescope.domainReceiptWithSuffix identifier chronologicalMember
  have typedReceipt := typed
  obtain ⟨level, typedDomain⟩ := typed
  have suffixWeakening : VLCtx.FVLift' model.vlctx final.vlctx 0
      (.skipN .refl (identifier :: suffix).length) 0 := by
    simpa only using suffixExtension.weakening.toFVLift'
  have rebasedTranslation : TrExprS env universes final.vlctx domain
      (semantic.lift' (.skipN .refl (identifier :: suffix).length)) := by
    exact translated.weakFV' envWF.ordered suffixWeakening finalWF.tr.wf
  have rebasedTyped : env.IsType universes.length final.vlctx.toCtx
      (semantic.lift' (.skipN .refl (identifier :: suffix).length)) := by
    exact ⟨level, typedDomain.weak' envWF.ordered suffixWeakening.toCtx⟩
  exact ⟨preIds, suffix, model, physicalIndex, name, domain, binder, semantic,
    idsShape, prefixTelescope.extension, suffixExtension, lookup, fresh, translated,
    typedReceipt, suffixWeakening, rebasedTranslation, rebasedTyped⟩

/- Rebase the semantic domain receipt all the way to the final local context.
   This is the selected-domain fact needed by a body consumer after grouped
   binder order has been established.  The theorem exposes final cdecl
   provenance together with the weakened translation and typehood; it does not
   infer the canonical role-to-ID correspondence or any generated-rule fact. -/
theorem RecursorBinderRebaseReceipt.finalDomainSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default) ∧
      final.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) ∧
      TrExprS env universes final.vlctx domain semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  have chronologicalMember : identifier ∈ chronological :=
    receipt.groupedOrder.mem_iff.mp member
  apply Exists.elim (receipt.domainReceipt identifier member)
  intro preIds
  rintro ⟨suffix, model, physicalIndex, name, domain, binder, sourceSemantic,
    ⟨_, _, _, lookup, _, _, _, _, rebasedTranslation, rebasedTyped⟩⟩
  have extension := receipt.chronologicalExtension
  have initialWF : initial.WF env universes := by
    simpa only [extension.drop_eq] using
      MLCtx.WF.dropN chronological.length extension.bound finalWF
  have telescope : SelectedRecursorTelescope env universes full initial chronological final :=
    by simpa only [native] using extension.selectedTelescope finalWF
  obtain ⟨_, projectedIndex, finalName, finalDomain, finalBinder, fullLookup, finalLookup⟩ :=
    telescope.lookups initialWF identifier chronologicalMember
  have declarationEq := Option.some.inj (lookup.symm.trans fullLookup)
  cases declarationEq
  refine ⟨physicalIndex, projectedIndex, name, domain, binder,
    sourceSemantic.lift' (.skipN .refl (identifier :: suffix).length), lookup, finalLookup,
    rebasedTranslation, rebasedTyped⟩

/- Pull a final-context domain translation back through the chronological
   extension.  This is the syntax-level half of grouped transport: the source
   closure and initial-context free-variable conditions are explicit, while
   typehood is intentionally left to a separate inhabited-strengthening
   argument.  In particular, a branch minor's type need not be inhabited. -/
theorem RecursorBinderRebaseReceipt.initialDomainTranslationOfFinal
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped)
    {domain : Expr}
    (domainLookup : ∃ index name binder,
      final.lctx.find? identifier =
        some (.cdecl index identifier name domain binder .default))
    (closed : Closed domain 0)
    (free : FVarsIn (· ∈ initial.vlctx.fvars) domain) :
    ∃ semantic,
      TrExprS env universes initial.vlctx domain semantic := by
  obtain ⟨_, _, _, supportDomain, _, _, _, supportLookup, supportTranslated, _⟩ :=
    receipt.finalDomainSupport finalWF native identifier member
  obtain ⟨_, _, _, requestedLookup⟩ := domainLookup
  have declarationEq := Option.some.inj (supportLookup.symm.trans requestedLookup)
  cases declarationEq
  exact supportTranslated.weakFV_inv envWF receipt.chronologicalExtension.weakening
    (.refl envWF finalWF.tr.wf) closed free

/- When the selected final-domain receipt also exposes sort typing, strengthen
   that typing witness through the same chronological weakening.  This is the
   inhabited/typehood-strengthened companion to the syntax-only transport
   above; it does not change the grouped-context boundary. -/
theorem RecursorBinderRebaseReceipt.initialDomainTranslationAndTypeOfFinal
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped)
    {domain : Expr}
    (domainLookup : ∃ index name binder,
      final.lctx.find? identifier =
        some (.cdecl index identifier name domain binder .default))
    (closed : Closed domain 0)
    (free : FVarsIn (· ∈ initial.vlctx.fvars) domain) :
    ∃ semantic level,
      TrExprS env universes initial.vlctx domain semantic ∧
      env.HasType universes.length initial.vlctx.toCtx semantic (.sort level) := by
  obtain ⟨_, _, _, supportDomain, _, _, _, supportLookup, supportTranslated, supportTyped⟩ :=
    receipt.finalDomainSupport finalWF native identifier member
  obtain ⟨_, _, _, requestedLookup⟩ := domainLookup
  have declarationEq := Option.some.inj (supportLookup.symm.trans requestedLookup)
  cases declarationEq
  obtain ⟨level, supportTyped⟩ := supportTyped
  obtain ⟨reduced, reducedTranslated, reducedTyped, _⟩ :=
    TrExprS.strengthenIsType envWF
    receipt.chronologicalExtension.weakening.toFVLift'
    (.refl envWF finalWF.tr.wf) supportTranslated supportTyped closed free
  exact ⟨reduced, level, reducedTranslated, reducedTyped⟩

/- The final-domain receipts provide the cdecl agreement needed to compare a
   grouped recursor body opened in the native local context with the same body
   opened in the final model context.  This is a syntactic body-transport
   seam; it does not translate the motive/minor applications or prove iota. -/
theorem RecursorBinderRebaseReceipt.groupedBindingEquation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    {body : Expr} (bodyClosed : body.looseBVarRange' = 0) :
    full.mkForall (grouped.map Expr.fvar).toArray body =
      final.lctx.mkForall (grouped.map Expr.fvar).toArray body := by
  have extension := receipt.chronologicalExtension
  have initialWF : initial.WF env universes := by
    simpa only [extension.drop_eq] using
      MLCtx.WF.dropN chronological.length extension.bound finalWF
  have telescope : SelectedRecursorTelescope env universes full initial chronological final :=
    by simpa only [native] using extension.selectedTelescope finalWF
  have chronologicalDistinct := telescope.distinct initialWF
  have groupedDistinct : grouped.Nodup := receipt.groupedOrder.nodup_iff.mpr chronologicalDistinct
  have agreement : SelectedCDeclBindingAgreement full final.lctx grouped := by
    intro identifier member
    obtain ⟨physicalIndex, projectedIndex, name, domain, binder, semantic,
      fullLookup, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF native identifier member
    exact ⟨physicalIndex, projectedIndex, name, domain, binder, .default, .default,
      fullLookup, finalLookup⟩
  have fullScope : full.BindingScope := by
    simpa only [native] using finalWF.bindingScope
  exact mkForall_congr_selected_cdecl grouped fullScope finalWF.bindingScope
    bodyClosed groupedDistinct agreement

/- Feed the grouped body equation into the native raw recursor type.  The
   closedness of the recursor body is kept as a premise because generated body
   translation has its own proof boundary. -/
theorem RecursorBinderRebaseReceipt.rawTypeFinalEquation
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0) :
    recursorRawType stats infos parent full =
      final.lctx.mkForall (grouped.map Expr.fvar).toArray
        (recursorTypeBody infos parent) := by
  have extension := receipt.chronologicalExtension
  have initialWF : initial.WF env universes := by
    simpa only [extension.drop_eq] using
      MLCtx.WF.dropN chronological.length extension.bound finalWF
  have telescope : SelectedRecursorTelescope env universes full initial chronological final :=
    by simpa only [native] using extension.selectedTelescope finalWF
  have chronologicalDistinct := telescope.distinct initialWF
  have groupedDistinct : grouped.Nodup := receipt.groupedOrder.nodup_iff.mpr chronologicalDistinct
  have agreement : SelectedCDeclBindingAgreement full final.lctx grouped := by
    intro identifier member
    obtain ⟨physicalIndex, projectedIndex, name, domain, binder, semantic,
      fullLookup, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF native identifier member
    exact ⟨physicalIndex, projectedIndex, name, domain, binder, .default, .default,
      fullLookup, finalLookup⟩
  have fullScope : full.BindingScope := by
    simpa only [native] using finalWF.bindingScope
  have bindings : SelectedCDeclBindings full grouped := agreement.left
  calc
    recursorRawType stats infos parent full =
        full.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos parent) :=
      recursorRawType_eq_flat_selected stats infos parent full grouped fullScope bodyClosed
        receipt.groupedBinders groupedDistinct bindings
    _ = final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos parent) :=
      receipt.groupedBindingEquation finalWF native bodyClosed

/- Consume an externally recorded native declaration together with the
   dependency-aware grouped rebase. The native lookup is deliberately an
   input: source provenance identifies the declaration, while the rebase
   receipt supplies its final-context semantic translation and typehood. -/
theorem RecursorBinderRebaseReceipt.finalDomainSupportOfNativeDecl
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (identifier : FVarId) (member : identifier ∈ grouped)
    {nativeDecl : LocalDecl}
    (nativeLookup : full.find? identifier = some nativeDecl) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      nativeDecl = .cdecl physicalIndex identifier name domain binder .default ∧
      final.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) ∧
      TrExprS env universes final.vlctx domain semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  obtain ⟨_, projectedIndex, name, domain, binder, _, fullLookup, finalLookup, translated, typed⟩ :=
    receipt.finalDomainSupport finalWF native identifier member
  have declarationEq := Option.some.inj (nativeLookup.symm.trans fullLookup)
  cases declarationEq
  exact ⟨_, projectedIndex, name, domain, binder, _, rfl, finalLookup, translated, typed⟩

/- Native index provenance supplies the major declaration directly.  This
   consumer only transports that lookup through the grouped rebase; it keeps
   the source role equation and the grouped membership visible to callers. -/
theorem RecursorBinderRebaseReceipt.finalDomainSupportOfSourceMajor
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original finalReader : Context} {infos : Array RecInfo} {info : RecInfo}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (source : RecursorInfoIndexSource stats types elimLevel parent original info finalReader)
    (finalWF : final.WF env universes) (native : final.lctx = finalReader.lctx)
    (member : info.major.fvarId! ∈ grouped) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      finalReader.lctx.find? info.major.fvarId! =
        some (.cdecl physicalIndex info.major.fvarId! name domain binder .default) ∧
      final.lctx.find? info.major.fvarId! =
        some (.cdecl projectedIndex info.major.fvarId! name domain binder .default) ∧
      TrExprS env universes final.vlctx domain semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  obtain ⟨nativeDecl, nativeLookup, _, _⟩ := source.majorLookup
  obtain ⟨physicalIndex, projectedIndex, name, domain, binder, semantic,
      nativeEq, finalLookup, translated, typed⟩ :=
    receipt.finalDomainSupportOfNativeDecl finalWF native info.major.fvarId! member nativeLookup
  rw [nativeEq] at nativeLookup
  exact ⟨physicalIndex, projectedIndex, name, domain, binder, semantic, nativeLookup,
    finalLookup, translated, typed⟩

/- The source motive lookup carries its exact native domain shape.  Transporting
   it through the same seam gives the final semantic domain and typehood while
   preserving the source-derived grouped telescope equation as a separate fact. -/
theorem RecursorBinderRebaseReceipt.finalDomainSupportOfSourceMotive
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {parent : Nat}
    {original finalReader : Context} {infos : Array RecInfo} {info : RecInfo}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (source : RecursorInfoIndexSource stats types elimLevel parent original info finalReader)
    (finalWF : final.WF env universes) (native : final.lctx = finalReader.lctx)
    (scope : finalReader.lctx.BindingScope)
    (member : info.motive.fvarId! ∈ grouped) :
    ∃ physicalIndex projectedIndex name domain binder semantic,
      finalReader.lctx.find? info.motive.fvarId! =
        some (.cdecl physicalIndex info.motive.fvarId! name domain binder .default) ∧
      domain = finalReader.lctx.mkForall info.indices
        (finalReader.lctx.mkForall #[info.major] (.sort elimLevel)) ∧
      final.lctx.find? info.motive.fvarId! =
        some (.cdecl projectedIndex info.motive.fvarId! name domain binder .default) ∧
      TrExprS env universes final.vlctx domain semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  obtain ⟨physicalIndex, identifier, nativeLookup, identifierEq⟩ :=
    source.motiveLookupAtCurrent scope
  have nativeLookup' : finalReader.lctx.find? info.motive.fvarId! =
      some (.cdecl physicalIndex info.motive.fvarId!
        (recursorMotiveName types parent)
        (finalReader.lctx.mkForall info.indices
          (finalReader.lctx.mkForall #[info.major] (.sort elimLevel)))
        .default .default) := by
    simpa only [← identifierEq, Expr.fvarId!] using nativeLookup
  have nativeLookupOrig := nativeLookup'
  obtain ⟨physicalIndex', projectedIndex, name, domain, binder, semantic,
      nativeEq, finalLookup, translated, typed⟩ :=
    receipt.finalDomainSupportOfNativeDecl finalWF native info.motive.fvarId! member nativeLookup'
  have shape := source.motiveDomainShape scope nativeLookupOrig
  have domainEq : domain = finalReader.lctx.mkForall info.indices
      (finalReader.lctx.mkForall #[info.major] (.sort elimLevel)) := by
    have typeEq := congrArg LocalDecl.type nativeEq
    simpa only [LocalDecl.type] using typeEq.symm.trans shape
  rw [nativeEq] at nativeLookup'
  exact ⟨physicalIndex', projectedIndex, name, domain, binder, semantic, nativeLookup',
    domainEq, finalLookup, translated, typed⟩

/- Consume the grouped abstraction obligation without manufacturing a
   chronological `SelectedRecursorTelescope`.  The receipt supplies the
   native raw-type equation; the grouped semantic translation and typehood
   remain the explicit dependency-aware transport premise. -/
theorem RecursorBinderRebaseReceipt.rawTypeTranslationFromGroupedSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (support : RecursorGroupedTypeTranslationSupport env universes full initial grouped
      (recursorTypeBody infos parent)) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent full) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) := by
  obtain ⟨typeSemantic, level, translated, typed⟩ := support
  have equation := receipt.rawTypeFinalEquation finalWF native bodyClosed
  refine ⟨typeSemantic, level, ?_, typed⟩
  rw [equation]
  simpa only [native] using translated

/- A recursive grouped witness chain is a direct producer of the grouped
   support consumed above.  This adapter keeps the native raw-type equation
   and all rebase obligations in the receipt while exposing the chain as the
   semantic input at the application boundary. -/
theorem RecursorBinderRebaseReceipt.rawTypeTranslationFromGroupedChain
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain env universes full initial.vlctx
      (recursorTypeBody infos parent) grouped) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent full) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) := by
  exact receipt.rawTypeTranslationFromGroupedSupport finalWF native bodyClosed chain.toSupport

/- Lift the grouped-chain raw-type receipt through the endpoint's actual
   chronological extension.  This exposes both initial and final-context
   translations without turning the grouped witness into a reordered model
   context. -/
theorem RecursorInfoModelEndpoint.rawTypeAtFinalFromGroupedChain
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx} {parent : Nat}
    {chronological grouped : List FVarId}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes)
    (native : final.lctx = finalReader.lctx)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain env universes finalReader.lctx
      initial.vlctx (recursorTypeBody infos parent) grouped) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent finalReader.lctx) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) ∧
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx)
        (typeSemantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (typeSemantic.liftN (final.length - initial.length)) (.sort level) := by
  obtain ⟨typeSemantic, level, translated, typed⟩ :=
    receipt.rawTypeTranslationFromGroupedChain finalWF native bodyClosed chain
  obtain ⟨translatedFinal, typedFinal⟩ := endpoint.liftTypeTranslation envWF translated typed
  exact ⟨typeSemantic, level, translated, typed, translatedFinal, typedFinal⟩

/- The verified implicit-binder translation is semantic-preserving, so the
   grouped-chain raw-type receipt can be packaged as the complete recursor
   type receipt expected by downstream declaration construction. -/
theorem RecursorInfoModelEndpoint.recursorTypeFromGroupedChain
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx} {parent : Nat}
    {chronological grouped : List FVarId}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes)
    (native : final.lctx = finalReader.lctx)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain env universes finalReader.lctx
      initial.vlctx (recursorTypeBody infos parent) grouped) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final := by
  obtain ⟨typeSemantic, level, raw, typed, finalRaw, finalTyped⟩ :=
    endpoint.rawTypeAtFinalFromGroupedChain receipt envWF finalWF native bodyClosed chain
  exact ⟨typeSemantic, level, raw, raw.inferImplicit 1000 false, typed,
    finalRaw, finalRaw.inferImplicit 1000 false, finalTyped⟩

/- Package the semantic application endpoint with the grouped raw-type
   equation.  The body-application support is deliberately an input: proving
   motive/minor application semantics is a separate obligation from rebasing
   native binder domains and the syntactic raw-type shell. -/
theorem RecursorBinderRebaseReceipt.finalBodyApplicationReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (finalWF : final.WF env universes) (native : final.lctx = full)
    (bodySupport : RecursorTypeBodyApplicationSupport env universes infos parent final.vlctx)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0) :
    ∃ bodySemantic level,
      TrExprS env universes final.vlctx (recursorTypeBody infos parent) bodySemantic ∧
      env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos parent full =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos parent) := by
  obtain ⟨bodySemantic, level, bodyTranslated, bodyTyped⟩ := bodySupport.translated
  exact ⟨bodySemantic, level, bodyTranslated, bodyTyped,
    receipt.rawTypeFinalEquation finalWF native bodyClosed⟩

/- The canonical Bool body needs only the final major and motive cdecls.  Keep
   the other registration obligations in the interface: this theorem derives
   the body application shell, while minor semantics, generated-rule
   semantics, and iota soundness remain caller-supplied facts. -/
theorem canonicalBoolRecursorTypeBodyApplicationSupport
    {env : VEnv} {universes : List Name} {infos : Array RecInfo}
    {final : MLCtx} {elimLevel : Level} {motive major : FVarId}
    {semanticElimLevel : VLevel}
    (envWF : env.WF) (finalWF : final.WF env universes)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (majorEvidence : ∃ index name domain binder,
      final.lctx.find? major =
        some (.cdecl index major name domain binder .default))
    (motiveEvidence : ∃ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) ∧
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)))
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (_minorSemantics : MinorSemantics)
    (_generatedRuleSemantics : GeneratedRuleSemantics)
    (_iotaSoundness : IotaSoundness) :
    RecursorTypeBodyApplicationSupport env universes infos 0 final.vlctx := by
  obtain ⟨majorIndex, majorName, majorDomain, majorBinder, majorLookup⟩ := majorEvidence
  obtain ⟨motiveIndex, motiveName, motiveDomain, motiveBinder, motiveLookup,
    motiveDomainEq⟩ := motiveEvidence
  have majorBindings : SelectedCDeclBindings final.lctx [major] := by
    intro identifier member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨majorIndex, majorName, majorDomain, majorBinder, .default, majorLookup⟩
  obtain ⟨majorSemantic, majorType, _, majorTranslated, majorTypeTranslated, majorTyped⟩ :=
    finalWF.cdeclTranslation envWF majorLookup
  have majorArray : #[infos[0]!.major] = ([major].map Expr.fvar).toArray := by
    simp only [majorEq, List.map_cons, List.map_nil]
  have majorArrow : final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel) =
      .forallE majorName majorDomain (.sort elimLevel) majorBinder := by
    rw [majorArray, mkForall_selected_fold [major] finalWF.bindingScope rfl
      (by simp) majorBindings]
    simp only [List.foldr_cons, List.foldr_nil, Expr.abstract1,
      LocalContext.mkBindingList1, majorLookup, Expr.abstractList,
      Bool.false_eq_true, if_false]
  have emptyForall : ∀ body : Expr, final.lctx.mkForall #[] body = body := by
    intro body
    simp only [Lean.LocalContext.mkForall, Lean.LocalContext.mkBinding,
      Array.size_empty, Nat.foldRev_zero, Expr.abstractRange_eq]
    have abstractEmpty : body.abstract #[] = body := by
      have h := Expr.abstract_eq body []
      simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil body 0)
    rw [abstractEmpty]
  obtain ⟨motiveSemantic, motiveType, _, motiveTranslated, motiveTypeTranslated,
    motiveTyped⟩ := finalWF.cdeclTranslation envWF motiveLookup
  have motiveDomainShape : motiveDomain =
      .forallE majorName majorDomain (.sort elimLevel) majorBinder := by
    rw [motiveDomainEq, indicesEq, emptyForall, majorArrow]
  rw [motiveDomainShape] at motiveTypeTranslated
  cases motiveTypeTranslated with
  | forallE _ _ majorDomainTranslated arrowSortTranslated =>
    have majorAlignment := majorTypeTranslated.uniq envWF
      (.refl envWF finalWF.tr.wf) majorDomainTranslated
    have convertedMajor := majorTyped.defeqU_r envWF finalWF.tr.wf.toCtx majorAlignment
    cases arrowSortTranslated with
    | sort arrowMapped =>
      cases Option.some.inj (mapped.symm.trans arrowMapped)
      refine ⟨majorSemantic, _, motiveSemantic, semanticElimLevel, ?_, convertedMajor,
        ?_, motiveTyped⟩
      · simpa only [majorEq] using majorTranslated
      · simpa only [motiveEq, indicesEq, mkAppN, Array.foldl_empty] using motiveTranslated

/- Compose the canonical Bool cdecl bridge with the final grouped-body receipt.
   The role equations and grouped membership are explicit inputs, as are the
   minor, generated-rule, and iota obligations that a complete registration
   proof must discharge separately. -/
theorem RecursorBinderRebaseReceipt.canonicalBoolFinalBodyApplicationReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    {elimLevel : Level} {motive major : FVarId} {semanticElimLevel : VLevel}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent full
      initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes) (native : final.lctx = full)
    (parentZero : parent = 0)
    (majorMember : major ∈ grouped) (motiveMember : motive ∈ grouped)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (motiveShape : ∀ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) →
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)))
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (_minorSemantics : MinorSemantics)
    (_generatedRuleSemantics : GeneratedRuleSemantics)
    (_iotaSoundness : IotaSoundness) :
    ∃ bodySemantic level,
      TrExprS env universes final.vlctx (recursorTypeBody infos parent) bodySemantic ∧
      env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos parent full =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos parent) := by
  subst parent
  have majorEvidence : ∃ index name domain binder,
      final.lctx.find? major =
        some (.cdecl index major name domain binder .default) := by
    obtain ⟨_, projectedIndex, name, domain, binder, _, _, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF native major majorMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup⟩
  have motiveEvidence : ∃ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) ∧
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)) := by
    obtain ⟨_, projectedIndex, name, domain, binder, _, _, finalLookup, _, _⟩ :=
      receipt.finalDomainSupport finalWF native motive motiveMember
    exact ⟨projectedIndex, name, domain, binder, finalLookup,
      motiveShape projectedIndex name domain binder finalLookup⟩
  have bodyClosed : (recursorTypeBody infos 0).looseBVarRange' = 0 := by
    simp [Expr.looseBVarRange', Lean.mkAppN, recursorTypeBody, motiveEq, indicesEq, majorEq]
  have bodySupport := canonicalBoolRecursorTypeBodyApplicationSupport envWF finalWF
    motiveEq indicesEq majorEq majorEvidence motiveEvidence mapped
      _minorSemantics _generatedRuleSemantics _iotaSoundness
  exact receipt.finalBodyApplicationReceipt finalWF native bodySupport bodyClosed

/- Pair the canonical Bool body/application endpoint with the existing model
   receipt's declared-constant construction.  This is a registration package,
   not a proof of the remaining minor/generated-rule/iota obligations. -/
theorem RecursorBinderRebaseReceipt.canonicalBoolDeclaredRecursorReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader : Context}
    {infos : Array RecInfo} {full : LocalContext}
    {initial final : MLCtx} {chronological grouped : List FVarId}
    {motive major : FVarId} {semanticElimLevel : VLevel}
    (receipt : RecursorBinderRebaseReceipt env universes stats infos 0 full
      initial final chronological grouped)
    (typeReceipt : RecursorTypeModelReceipt env universes stats infos 0 reader initial final)
    (readerNative : reader.lctx = full)
    (envWF : env.WF) (finalWF : final.WF env universes) (native : final.lctx = full)
    (majorMember : major ∈ grouped) (motiveMember : motive ∈ grouped)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (motiveShape : ∀ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) →
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)))
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (_minorSemantics : MinorSemantics)
    (_generatedRuleSemantics : GeneratedRuleSemantics)
    (_iotaSoundness : IotaSoundness)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = []) :
    ∃ bodySemantic level constant,
      TrExprS env universes final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 reader.lctx =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray (recursorTypeBody infos 0) ∧
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          reader.lctx isK false 0 rules)) constant ∧
      constant.toVConstant.WF env := by
  obtain ⟨bodySemantic, bodyLevel, bodyTranslated, bodyTyped, bodyRaw⟩ :=
    receipt.canonicalBoolFinalBodyApplicationReceipt envWF finalWF native rfl
      majorMember motiveMember motiveEq indicesEq majorEq motiveShape mapped
      _minorSemantics _generatedRuleSemantics _iotaSoundness
  obtain ⟨constant, constantTranslated, constantWF⟩ := typeReceipt.existsDeclaredRecursor
    (types := types) lparams isK rules levels empty
  exact ⟨bodySemantic, bodyLevel, constant, bodyTranslated, bodyTyped,
    by simpa only [readerNative] using bodyRaw, constantTranslated, constantWF⟩

/- For canonical Bool, native parent allocation is major-then-motive, while
   the recursor type groups motive/minors before major.  Keep this shape
   obstruction explicit: selected-domain support needs a reordering/rebase
   theorem, not an unproved identification of the chronological extension. -/
theorem canonicalBoolRecursorBinderOrderBoundary
    {stats : InductiveStats} {infos : Array RecInfo}
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (distinct : major ≠ motive) :
    (recursorTypeBinders stats infos 0).toList ≠
      [major, motive, minorFalse, minorTrue].map Expr.fvar := by
  intro alignment
  have order : [motive, minorFalse, minorTrue, major] =
      [major, motive, minorFalse, minorTrue] := by
    simpa [recursorTypeBinders, params, infosEq, motiveEq, minorsEq, indicesEq, majorEq]
      using alignment
  have head := congrArg List.head? order
  have motiveMajor : motive = major := by simpa using head
  exact distinct motiveMajor.symm

/- The two concrete Bool binder lists are permutations even though their order
   is different.  Keep this structural fact separate from the endpoint's
   chronology: a caller still has to identify the native allocated IDs with the
   four roles before this permutation can be applied to an endpoint receipt. -/
theorem canonicalBoolRecursorBinderOrderPermutation
    {motive minorFalse minorTrue major : FVarId} :
    [motive, minorFalse, minorTrue, major].Perm
      [major, motive, minorFalse, minorTrue] := by
  have first : [motive, minorFalse, minorTrue, major].Perm
      [motive, minorFalse, major, minorTrue] :=
    .cons motive (.cons minorFalse (List.Perm.swap major minorTrue []))
  have second : [motive, minorFalse, major, minorTrue].Perm
      [motive, major, minorFalse, minorTrue] :=
    .cons motive (List.Perm.swap major minorFalse [minorTrue])
  have third : [motive, major, minorFalse, minorTrue].Perm
      [major, motive, minorFalse, minorTrue] :=
    List.Perm.swap major motive [minorFalse, minorTrue]
  exact first.trans (second.trans third)

/- An explicitly constructed native extension is enough to recover the
   allocation equation used by the grouped-order receipt.  Extension lists
   are unique for a fixed initial and final model, so callers need not prove
   the universal equation separately. -/
theorem canonicalBoolAllocationOfKnownExtension
    {initial final : MLCtx} {motive minorFalse minorTrue major : FVarId}
    (known : IndexMLCtxExtension initial [major, motive, minorFalse, minorTrue] final) :
    ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue] := by
  intro ids extension
  exact extension.eq_ids_of_same_final known

/- The grouped Bool order cannot be presented as a second selected telescope
   over the same native final model.  This is the concrete obstruction behind
   the semantic rebase boundary: a `List.Perm` does not reorder the model
   extension or its prefix translations. -/
theorem canonicalBoolGroupedTelescopeImpossible
    {env : VEnv} {universes : List Name} {full : LocalContext}
    {initial final : MLCtx}
    {motive minorFalse minorTrue major : FVarId}
    (chronological : SelectedRecursorTelescope env universes full initial
      [major, motive, minorFalse, minorTrue] final)
    (distinct : major ≠ motive) :
    ¬ SelectedRecursorTelescope env universes full initial
      [motive, minorFalse, minorTrue, major] final := by
  apply chronological.no_reordered_ids
  intro equality
  have head := congrArg List.head? equality
  apply distinct
  simpa using head

/- Specialize the grouped-order rebase endpoint to canonical Bool.  The native
   allocation equation remains explicit, while the recursor-type binder
   alignment and the required permutation are discharged from the concrete
   four-binder shape.  The result is a rebase receipt, not a reordered context
   extension: semantic prefix models stay in chronological allocation order. -/
theorem RecursorInfoModelEndpoint.canonicalBoolRebaseBinderOrder
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (allocation : ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue]) :
    ∃ chronological,
      RecursorBinderRebaseReceipt env universes stats infos 0 finalReader.lctx
        initial final chronological [motive, minorFalse, minorTrue, major] := by
  have alignment : (recursorTypeBinders stats infos 0).toList =
      [motive, minorFalse, minorTrue, major].map Expr.fvar := by
    simp [recursorTypeBinders, params, infosEq, motiveEq, minorsEq, indicesEq, majorEq]
  apply endpoint.rebaseBinderOrder envWF [motive, minorFalse, minorTrue, major]
  · intro chronological extension
    rw [allocation chronological extension]
    exact canonicalBoolRecursorBinderOrderPermutation
  · exact alignment

theorem RecursorInfoModelEndpoint.canonicalBoolRebaseBinderOrderOfKnownExtension
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (known : IndexMLCtxExtension initial [major, motive, minorFalse, minorTrue] final) :
    ∃ chronological,
      RecursorBinderRebaseReceipt env universes stats infos 0 finalReader.lctx
        initial final chronological [motive, minorFalse, minorTrue, major] := by
  exact endpoint.canonicalBoolRebaseBinderOrder envWF params infosEq motiveEq minorsEq indicesEq
    majorEq (canonicalBoolAllocationOfKnownExtension known)

/- Feed the canonical rebase receipt directly into the final body/application
   consumer.  The endpoint supplies the final model WF and native local-context
   equality; role membership is discharged from the fixed grouped Bool order. -/
theorem RecursorInfoModelEndpoint.canonicalBoolRebasedFinalBodyApplicationReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF)
    {motive minorFalse minorTrue major : FVarId} {info : RecInfo}
    (params : stats.params = #[]) (infosEq : infos = #[info])
    (motiveEq : info.motive = .fvar motive)
    (minorsEq : info.minors = #[.fvar minorFalse, .fvar minorTrue])
    (indicesEq : info.indices = #[])
    (majorEq : info.major = .fvar major)
    (allocation : ∀ ids, IndexMLCtxExtension initial ids final →
      ids = [major, motive, minorFalse, minorTrue])
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (_minorSemantics : MinorSemantics)
    (_generatedRuleSemantics : GeneratedRuleSemantics)
    (_iotaSoundness : IotaSoundness) :
    ∃ chronological bodySemantic level,
      RecursorBinderRebaseReceipt env universes stats infos 0 finalReader.lctx
        initial final chronological [motive, minorFalse, minorTrue, major] ∧
      TrExprS env universes final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 finalReader.lctx =
        final.lctx.mkForall
          ([motive, minorFalse, minorTrue, major].map Expr.fvar).toArray
          (recursorTypeBody infos 0) := by
  obtain ⟨chronological, receipt⟩ := endpoint.canonicalBoolRebaseBinderOrder envWF
    params infosEq motiveEq minorsEq indicesEq majorEq allocation
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have motiveShape : ∀ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) →
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)) := by
    intro index name domain binder lookup
    have motiveId : infos[0]!.motive.fvarId! = motive := by
      rw [show infos[0]!.motive = info.motive by simpa [infosEq]]
      rw [motiveEq]
      rfl
    have sourceLookup : finalReader.lctx.find? infos[0]!.motive.fvarId! =
        some (.cdecl index motive name domain binder .default) := by
      rw [motiveId]
      simpa only [finalNative] using lookup
    have finalScope : finalReader.lctx.BindingScope := by
      rw [← finalNative]
      exact finalWF.bindingScope
    have shape := source.motiveDomainShape finalScope sourceLookup
    simpa only [finalNative] using shape
  obtain ⟨bodySemantic, level, bodyTranslated, bodyTyped, bodyRaw⟩ :=
    receipt.canonicalBoolFinalBodyApplicationReceipt
      (motive := motive) (major := major)
      (grouped := [motive, minorFalse, minorTrue, major]) envWF finalWF finalNative
      (by simp) (by simp) (by simp)
      (by simpa [infosEq] using motiveEq) (by simpa [infosEq] using indicesEq)
      (by simpa [infosEq] using majorEq) motiveShape mapped
      _minorSemantics _generatedRuleSemantics _iotaSoundness
  exact ⟨chronological, bodySemantic, level, receipt, bodyTranslated, bodyTyped, bodyRaw⟩

/- Once selected-domain support is available, its semantic content can be
   consumed one binder at a time.  This packages the exact chronological
   prefix model, native cdecl provenance, translated domain, and domain
   typehood for every selected recursor binder.  Native metadata by itself
   supplies only the cdecl provenance; the telescope receipt is the missing
   semantic premise at the canonical frontend boundary. -/
theorem RecursorSelectedDomainSupport.domainReceipts
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {infos : Array RecInfo} {parent : Nat} {full : LocalContext} {initial : MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent full initial) :
    ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
      ∃ projected, SelectedRecursorTelescope env universes full initial ids projected ∧
        ∀ identifier, identifier ∈ ids →
          ∃ preIds suffix model physicalIndex name domain binder semantic,
            ids = preIds ++ identifier :: suffix ∧
            SelectedRecursorTelescope env universes full initial preIds model ∧
            full.find? identifier =
              some (.cdecl physicalIndex identifier name domain binder .default) ∧
            model.lctx.find? identifier = none ∧
            TrExprS env universes model.vlctx domain semantic ∧
            env.IsType universes.length model.vlctx.toCtx semantic := by
  obtain ⟨ids, selected, projected, telescope⟩ := support
  refine ⟨ids, selected, projected, telescope, ?_⟩
  intro identifier member
  exact telescope.domainReceipt identifier member

def RecursorFinalTypehood (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (finalReader : Context) (finalModel : MLCtx)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) : Prop :=
  ∀ parent, parent < types.size →
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes finalModel.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length finalModel.vlctx.toCtx semantic)

def RecursorInitialTypehood (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (infos : Array RecInfo) (finalReader : Context) (initialModel : MLCtx)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) : Prop :=
  ∀ parent, parent < types.size →
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic) ∧
    (∃ semantic,
      TrExprS env universes initialModel.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length initialModel.vlctx.toCtx semantic)

theorem RecursorSelectedDomainSupport.rawTypeSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo} {parent : Nat}
    {original current : Context} {initial : MLCtx}
    (support : RecursorSelectedDomainSupport env universes stats infos parent current.lctx initial)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (fullScope : current.lctx.BindingScope) (bound : parent < infos.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    RecursorRawTypeTranslationSupport env universes stats infos parent current.lctx initial := by
  obtain ⟨ids, selected, projected, telescope⟩ := support
  refine ⟨ids, selected, ⟨projected, telescope⟩, ?_⟩
  intro projected projectedTelescope
  exact projectedTelescope.bodyApplicationSupport envWF initialWF fullScope bound selected source mapped

theorem RecursorInfoModelEndpoint.recursorTypeFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    RecursorTypeModelReceipt env universes stats infos parent finalReader initial final := by
  have fullScope : finalReader.lctx.BindingScope := by
    simpa only [endpoint.context.2.1] using endpoint.context.1.bindingScope
  have infoBound : parent < infos.size := by simpa only [endpoint.infoSize] using bound
  exact endpoint.recursorType envWF initialWF parameterFree parent
    (support.rawTypeSupport envWF initialWF fullScope infoBound source mapped)

/-- Combine the selected-domain application receipt with the exact model constant
    used by native recursor registration.  This is the semantic boundary needed
    by callers that have established the recursor type support but have not yet
    assembled the whole registration CPS.  In particular, the theorem keeps
    the native index source, elimination-level mapping, and empty initial model
    context visible instead of manufacturing a model constant from a weaker
    typehood statement. -/
theorem RecursorInfoModelEndpoint.declaredRecursorFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = []) :
    ∃ (constant : VConstVal),
      RecursorTypeModelReceipt env universes stats infos parent finalReader initial final ∧
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          finalReader.lctx isK false parent rules)) constant ∧
      constant.toVConstant.WF env := by
  have receipt := endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound
    source mapped support
  obtain ⟨constant, translated, wellFormed⟩ :=
    receipt.existsDeclaredRecursor (types := types) lparams isK rules levels empty
  exact ⟨constant, receipt, translated, wellFormed⟩

/- Feed the grouped-chain type receipt into the existing metadata constructor.
   This packages only the declaration type and constant WF; generated rule
   semantics and iota obligations remain outside this type-level endpoint. -/
theorem RecursorInfoModelEndpoint.declaredRecursorFromGroupedChain
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx} {parent : Nat} {chronological grouped : List FVarId}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes)
    (native : final.lctx = finalReader.lctx)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain env universes finalReader.lctx
      initial.vlctx (recursorTypeBody infos parent) grouped)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = []) :
    ∃ (constant : VConstVal),
      RecursorTypeModelReceipt env universes stats infos parent finalReader initial final ∧
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          finalReader.lctx isK false parent rules)) constant ∧
      constant.toVConstant.WF env := by
  have typeReceipt := endpoint.recursorTypeFromGroupedChain receipt envWF finalWF native
    bodyClosed chain
  obtain ⟨constant, translated, wellFormed⟩ :=
    typeReceipt.existsDeclaredRecursor (types := types) lparams isK rules levels empty
  exact ⟨constant, typeReceipt, translated, wellFormed⟩

/- Start from the endpoint-level selected-domain/type-model receipt and carry
   it through the grouped-order rebase into the canonical Bool declaration
   package.  The native index source and all role/semantic obligations remain
   visible at this boundary. -/
theorem RecursorInfoModelEndpoint.canonicalBoolDeclaredRecursorReceipt
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos 0
      finalReader.lctx initial)
    (grouped : List FVarId)
    (order : ∀ ids, IndexMLCtxExtension initial ids final → grouped.Perm ids)
    (alignment : (recursorTypeBinders stats infos 0).toList = grouped.map Expr.fvar)
    {motive major : FVarId}
    (majorMember : major ∈ grouped) (motiveMember : motive ∈ grouped)
    (motiveEq : infos[0]!.motive = .fvar motive)
    (indicesEq : infos[0]!.indices = #[])
    (majorEq : infos[0]!.major = .fvar major)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = [])
    {MinorSemantics GeneratedRuleSemantics IotaSoundness : Prop}
    (_minorSemantics : MinorSemantics)
    (_generatedRuleSemantics : GeneratedRuleSemantics)
    (_iotaSoundness : IotaSoundness) :
    ∃ chronological bodySemantic level constant,
      RecursorBinderRebaseReceipt env universes stats infos 0 finalReader.lctx
        initial final chronological grouped ∧
      TrExprS env universes final.vlctx (recursorTypeBody infos 0) bodySemantic ∧
      env.HasType universes.length final.vlctx.toCtx bodySemantic (.sort level) ∧
      recursorRawType stats infos 0 finalReader.lctx =
        final.lctx.mkForall (grouped.map Expr.fvar).toArray
          (recursorTypeBody infos 0) ∧
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams
          finalReader.lctx isK false 0 rules)) constant ∧
      constant.toVConstant.WF env := by
  obtain ⟨chronological, receipt⟩ := endpoint.rebaseBinderOrder envWF grouped order alignment
  obtain ⟨finalWF, finalNative, _⟩ := endpoint.context
  have motiveShape : ∀ index name domain binder,
      final.lctx.find? motive =
        some (.cdecl index motive name domain binder .default) →
      domain = final.lctx.mkForall infos[0]!.indices
        (final.lctx.mkForall #[infos[0]!.major] (.sort elimLevel)) := by
    intro index name domain binder lookup
    have motiveId : infos[0]!.motive.fvarId! = motive := by
      rw [motiveEq]
      rfl
    have sourceLookup : finalReader.lctx.find? infos[0]!.motive.fvarId! =
        some (.cdecl index motive name domain binder .default) := by
      rw [motiveId]
      simpa only [finalNative] using lookup
    have finalScope : finalReader.lctx.BindingScope := by
      rw [← finalNative]
      exact finalWF.bindingScope
    have shape := source.motiveDomainShape finalScope sourceLookup
    simpa only [finalNative] using shape
  have typeReceipt := endpoint.recursorTypeFromDomains envWF initialWF parameterFree 0 bound
    source mapped support
  obtain ⟨bodySemantic, bodyLevel, constant, bodyTranslated, bodyTyped, bodyRaw,
    constantTranslated, constantWF⟩ :=
    receipt.canonicalBoolDeclaredRecursorReceipt typeReceipt rfl envWF finalWF finalNative
      majorMember motiveMember motiveEq indicesEq majorEq motiveShape mapped
      _minorSemantics _generatedRuleSemantics _iotaSoundness
      lparams isK rules levels empty
  exact ⟨chronological, bodySemantic, bodyLevel, constant, receipt, bodyTranslated,
    bodyTyped, bodyRaw, constantTranslated, constantWF⟩

/- Transfer the declared metadata translation to the exact recursor value held
   by a registered native environment.  Registration lookup and metadata
   identity stay explicit, so this theorem can be consumed by insertion
   evidence without identifying a native entry by its name alone. -/
theorem RecursorInfoModelEndpoint.registeredRecursorFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos 0
      finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel infos
      lparams finalReader.lctx isK false 0 rules) :
    ∃ constant,
      registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt env universes stats infos 0 finalReader initial final ∧
      TrConstVal .safe env (.recInfo recursor) constant ∧
      constant.toVConstant.WF env := by
  obtain ⟨constant, receipt, translated, wellFormed⟩ :=
    endpoint.declaredRecursorFromDomains envWF initialWF parameterFree 0 bound source mapped
      support lparams isK rules levels empty
  rw [← metadata] at translated
  exact ⟨constant, lookup, receipt, translated, wellFormed⟩

/- Carry the grouped-chain declaration package through a native recursor
   lookup.  The metadata equality is the only native registration handoff;
   no fresh insertion or rule/iota semantics are inferred here. -/
theorem RecursorInfoModelEndpoint.registeredRecursorFromGroupedChain
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx} {parent : Nat}
    {chronological grouped : List FVarId}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (receipt : RecursorBinderRebaseReceipt env universes stats infos parent
      finalReader.lctx initial final chronological grouped)
    (envWF : env.WF) (finalWF : final.WF env universes)
    (native : final.lctx = finalReader.lctx)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (chain : RecursorGroupedTypeTranslationChain env universes finalReader.lctx
      initial.vlctx (recursorTypeBody infos parent) grouped)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[parent]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel infos lparams
      finalReader.lctx isK false parent rules) :
    ∃ constant,
      registered.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt env universes stats infos parent finalReader initial final ∧
      TrConstVal .safe env (.recInfo recursor) constant ∧
      constant.toVConstant.WF env := by
  obtain ⟨constant, typeReceipt, translated, wellFormed⟩ :=
    endpoint.declaredRecursorFromGroupedChain receipt envWF finalWF native bodyClosed chain
      lparams isK rules levels empty
  rw [← metadata] at translated
  exact ⟨constant, lookup, typeReceipt, translated, wellFormed⟩

/- Insert the registered model constant into the semantic constructor
   environment.  The native lookup/metadata handoff supplies the model name;
   freshness is kept as an explicit premise, while the extension WF is proved
   by the ordinary constructor-header insertion theorem. -/
theorem RecursorInfoModelEndpoint.registeredRecursorInsertionFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {reader finalReader : Context}
    {infos : Array RecInfo} {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (bound : 0 < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel 0 reader infos[0]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos 0
      finalReader.lctx initial)
    (lparams : List Name) (isK : Bool) (rules : List RecursorRule)
    (levels : getRecLevelParams elimLevel lparams = universes)
    (empty : initial.vlctx = [])
    {registered : Kernel.Environment} {recursor : RecursorVal}
    (lookup : registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor))
    (metadata : recursor = declareRecursors.metadataVal stats types elimLevel infos
      lparams finalReader.lctx isK false 0 rules)
    (fresh : env.constants (mkRecName types[0]!.name) = none) :
    ∃ constant extended,
      registered.find? (mkRecName types[0]!.name) = some (.recInfo recursor) ∧
      RecursorTypeModelReceipt env universes stats infos 0 finalReader initial final ∧
      TrConstVal .safe env (.recInfo recursor) constant ∧
      constant.toVConstant.WF env ∧
      env.addConstructorHeaders [constant] = some extended ∧ extended.WF := by
  obtain ⟨constant, lookup, receipt, translated, wellFormed⟩ :=
    endpoint.registeredRecursorFromDomains envWF initialWF parameterFree bound source mapped
      support lparams isK rules levels empty lookup metadata
  have constantName : constant.name = mkRecName types[0]!.name := by
    have nameEq := translated.2.symm
    rw [metadata] at nameEq
    change constant.name = mkRecName types[0]!.name at nameEq
    exact nameEq
  have constantFresh : env.constants constant.name = none := by
    simpa [constantName] using fresh
  obtain ⟨extended, insertion⟩ := VEnv.addConstructorHeaders.exists
    (env := env) (ctors := [constant])
    (fun constructor member => by
      obtain rfl := List.mem_singleton.mp member
      exact constantFresh)
    (by simp)
  refine ⟨constant, extended, lookup, receipt, translated, wellFormed, insertion, ?_⟩
  exact VEnv.addConstructorHeaders.wf envWF (by
    intro constructor member
    obtain rfl := List.mem_singleton.mp member
    exact wellFormed) insertion

theorem RecursorInfoModelEndpoint.finalStoredTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        ((recursorRawType stats infos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support).finalStoredTypehood

theorem RecursorInfoModelEndpoint.finalRawTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx) semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support).finalRawTypehood

theorem RecursorInfoModelEndpoint.finalMetadataTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    ∃ semantic,
      TrExprS env universes final.vlctx
        (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules).type semantic ∧
      env.IsType universes.length final.vlctx.toCtx semantic := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support)
    |>.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules

theorem RecursorInfoModelEndpoint.initialTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
      lparams isK isUnsafe rules := by
  intro parent bound
  have receipt := endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound
    (sources parent bound) mapped (supports parent bound)
  exact ⟨receipt.rawTypehood, receipt.storedTypehood,
    receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩

theorem RecursorInfoModelEndpoint.initialStoredWF_of_declaredRecursorFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat) (bound : parent < types.size)
    (source : RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (support : RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constant : VConstVal) (lparams : List Name) (isK isUnsafe : Bool)
    (rules : List RecursorRule)
    (native : TrConstVal .safe env
      (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules)) constant)
    (levels : (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
      isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) : constant.toVConstant.WF env := by
  exact (endpoint.recursorTypeFromDomains envWF initialWF parameterFree parent bound source mapped support)
    |>.initialStoredWF_of_declaredRecursor constant lparams isK isUnsafe rules native levels
      envWF initialWF empty

theorem RecursorInfoModelEndpoint.initialStoredWFOfDeclaredRecursorsFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (constants : ∀ parent, parent < types.size → VConstVal)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (native : ∀ parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
          isK isUnsafe parent rules)) (constants parent bound))
    (levels : ∀ parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel infos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : initial.vlctx.toCtx = []) :
    ∀ parent (bound : parent < types.size), (constants parent bound).toVConstant.WF env := by
  intro parent bound
  exact endpoint.initialStoredWF_of_declaredRecursorFromDomains envWF initialWF parameterFree parent
    bound (sources parent bound) mapped (supports parent bound) (constants parent bound) lparams
    isK isUnsafe rules (native parent bound) (levels parent bound) empty

theorem RecursorInfoModelEndpoint.finalTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
      lparams isK isUnsafe rules := by
  intro parent bound
  exact ⟨endpoint.finalRawTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound),
    endpoint.finalStoredTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound),
    endpoint.finalMetadataTypehoodFromDomains envWF initialWF parameterFree parent bound
      (sources parent bound) mapped (supports parent bound)
      lparams isK isUnsafe rules⟩

theorem mkRecInfos.getTranslatedAppliedRecursorTypes
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats result.1 parent result.2 model finalModel := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact endpoint.recursorTypeFromDomains envWF modelWF fieldOnly parent bound
    (sources.2 parent bound) mapped (domainSupport result success finalModel endpoint parent bound)

theorem mkRecInfos.getTranslatedAppliedInitialStoredWFOfDeclaredRecursors
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (recursorConstant : ∀ (_finalInfos : Array RecInfo) (_finalReader : Context) (_finalModel : MLCtx)
      parent, parent < types.size → VConstVal)
    (recursorNative : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (finalModel : MLCtx)
      parent (bound : parent < types.size),
      TrConstVal .safe env
        (.recInfo (declareRecursors.metadataVal stats types elimLevel finalInfos lparams
          finalReader.lctx isK isUnsafe parent rules))
        (recursorConstant finalInfos finalReader finalModel parent bound))
    (recursorLevels : ∀ (finalInfos : Array RecInfo) (finalReader : Context) (_finalModel : MLCtx)
      parent (_bound : parent < types.size),
      (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe parent rules).levelParams = universes)
    (empty : model.vlctx.toCtx = []) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∀ bound, (recursorConstant result.1 result.2 finalModel parent bound).toVConstant.WF env := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent parentBound bound
  exact (receipts parent parentBound).initialStoredWF_of_declaredRecursor
    (recursorConstant result.1 result.2 finalModel parent bound) lparams isK isUnsafe rules
    (recursorNative result.1 result.2 finalModel parent bound)
    (recursorLevels result.1 result.2 finalModel parent bound) envWF modelWF empty

theorem mkRecInfos.getTranslatedAppliedFinalStoredTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats result.1 parent result.2.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalStoredTypehood

theorem mkRecInfos.getTranslatedAppliedFinalRawTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats result.1 parent result.2.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalRawTypehood

theorem mkRecInfos.getTranslatedAppliedFinalMetadataTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧ ∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel result.1 lparams result.2.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic := by
  intro result success
  obtain ⟨frame, counts, finalModel, endpoint, receipts⟩ :=
    mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
      fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  intro parent bound
  exact (receipts parent bound).finalMetadataTypehood types elimLevel lparams isK isUnsafe rules

theorem mkRecInfos.scopedTranslatedAppliedFinalMetadataTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (declareRecursors.metadataVal stats types elimLevel finalInfos lparams finalReader.lctx
              isK isUnsafe parent rules).type semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalMetadataTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, metadataTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint metadataTypehood

theorem mkRecInfos.scopedTranslatedAppliedFinalStoredTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            ((recursorRawType stats finalInfos parent finalReader.lctx).inferImplicit 1000 false) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalStoredTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, storedTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint storedTypehood

theorem mkRecInfos.scopedTranslatedAppliedFinalRawTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        ∃ semantic,
          TrExprS env universes finalModel.vlctx
            (recursorRawType stats finalInfos parent finalReader.lctx) semantic ∧
          env.IsType universes.length finalModel.vlctx.toCtx semantic) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalRawTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, rawTypehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint rawTypehood

theorem mkRecInfos.getTranslatedAppliedFinalTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        RecursorFinalTypehood env universes stats types elimLevel result.1 result.2
          finalModel lparams isK isUnsafe rules := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.finalTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem RecursorInfoModelEndpoint.initialAndFinalTypehoodFromDomains
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0)
    (sources : ∀ parent, parent < types.size →
      RecursorInfoIndexSource stats types elimLevel parent reader infos[parent]! finalReader)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (supports : ∀ parent, parent < types.size →
      RecursorSelectedDomainSupport env universes stats infos parent finalReader.lctx initial)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    RecursorInitialTypehood env universes stats types elimLevel infos finalReader initial
        lparams isK isUnsafe rules ∧
      RecursorFinalTypehood env universes stats types elimLevel infos finalReader final
        lparams isK isUnsafe rules := by
  exact ⟨endpoint.initialTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
      lparams isK isUnsafe rules,
    endpoint.finalTypehoodFromDomains envWF initialWF parameterFree sources mapped supports
      lparams isK isUnsafe rules⟩

theorem mkRecInfos.getTranslatedAppliedInitialTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.initialTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem mkRecInfos.getTranslatedAppliedInitialAndFinalTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) :
    (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      reader.RecursorScopeFrame result.2 ∧ RecursorInfoCounts types result.1 ∧
      ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.1 result.2
          model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.1 result.2
            finalModel lparams isK isUnsafe rules) := by
  intro result success
  obtain ⟨frame, _, counts, finalModel, endpoint⟩ := mkRecInfos.getTranslatedPasses stats types elimLevel
    reader envWF constants definitions fieldOnly model modelWF native reserved mapped
    parentSupport minorSupport result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨_, _, sources⟩ := mkRecInfos.getIndexSources stats types elimLevel
    reader readerWF reserved result success
  refine ⟨frame, counts, finalModel, endpoint, ?_⟩
  exact endpoint.initialAndFinalTypehoodFromDomains envWF modelWF fieldOnly
    (fun parent bound => sources.2 parent bound) mapped
    (fun parent bound => domainSupport result success finalModel endpoint parent bound)
    lparams isK isUnsafe rules

theorem mkRecInfos.scopedTranslatedAppliedFinalTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
        finalModel lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedFinalTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedInitialTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
        model lparams isK isUnsafe rules →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedInitialTypehood stats types elimLevel reader envWF constants
    definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport
    lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedInitialAndFinalTypehood {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedInitialAndFinalTypehood stats types elimLevel reader envWF
    constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
    domainSupport lparams isK isUnsafe rules).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, typehood⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint typehood

theorem mkRecInfos.scopedTranslatedAppliedRecursorTypes {ResultType : Type}
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (next : Array RecInfo → M ResultType) (reader : Context) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      (next finalInfos finalReader).WF post) :
    (mkRecInfos stats types elimLevel next reader).WF post := by
  rw [mkRecInfos.morphism stats types elimLevel next
    (fun finalInfos => do return (finalInfos, ← readThe Context))
    (fun result => next result.1 result.2) reader (fun _ _ => rfl)]
  refine (mkRecInfos.getTranslatedAppliedRecursorTypes stats types elimLevel reader envWF constants definitions
    fieldOnly model modelWF native reserved mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨finalInfos, finalReader⟩ ⟨frame, counts, finalModel, endpoint, receipts⟩
  exact nextWF finalInfos finalReader finalModel frame counts endpoint receipts

theorem mkRecInfos.registeredTranslatedAppliedRecursorTypes
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        ∀ parent, parent < types.size →
          RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have translatedApplied :
      (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
        reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
        ∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
          result.2.1 result.2.2 model finalModel ∧
          ∀ parent, parent < types.size →
            RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel := by
    unfold mkRecInfos.scopeRegistration
    refine mkRecInfos.scopedTranslatedAppliedRecursorTypes stats types elimLevel _ reader _ envWF
      constants definitions fieldOnly model modelWF native reserved mapped parentSupport minorSupport
      domainSupport ?_
    intro finalInfos finalReader finalModel frame counts endpoint receipts
    apply readWF
    apply bindWF
    intro registeredEnv
    exact .pure ⟨frame, counts, finalModel, endpoint, receipts⟩
  intro result success
  have readerWF : reader.lctx.WF := native ▸ modelWF.tr.1
  obtain ⟨frame, counts, registeredWF, retained, metadata, rhsScope⟩ :=
    mkRecInfos.registeredScope stats types elimLevel lparams isK isUnsafe reader
      readerWF reserved nativeEnvWF result success
  obtain ⟨_, _, finalModel, endpoint, receipts⟩ := translatedApplied result success
  exact ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩

/-- Construct translated model constants for the recursors actually stored by registration.
This supplies their type receipts; rule semantics and model insertion remain separate. -/
theorem mkRecInfos.registeredTranslatedAppliedDeclaredRecursors
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK : Bool) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (levels : getRecLevelParams elimLevel lparams = universes) (empty : model.vlctx = []) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK false reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        ∀ parent, parent < types.size →
          RecursorTypeModelReceipt env universes stats result.2.1 parent result.2.2 model finalModel) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK false result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 ∧
      ∀ parent, parent < types.size → ∃ (info : RecursorVal) (constant : VConstVal),
        result.1.find? (mkRecName types[parent]!.name) = some (.recInfo info) ∧
        TrConstVal .safe env (.recInfo info) constant ∧ constant.toVConstant.WF env := by
  refine (mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK false reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport).mono ?_
  rintro result ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained,
    metadata, rhsScope⟩
  refine ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained,
    metadata, rhsScope, ?_⟩
  intro parent bound
  obtain ⟨rules, _, lookup⟩ := metadata parent bound
  obtain ⟨constant, translated, wellFormed⟩ :=
    (receipts parent bound).existsDeclaredRecursor lparams isK rules levels empty
  exact ⟨_, constant, lookup, translated, wellFormed⟩

theorem mkRecInfos.registeredTranslatedAppliedInitialAndFinalTypehood
    {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model) :
    (mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader).WF fun result =>
      reader.RecursorScopeFrame result.2.2 ∧ RecursorInfoCounts types result.2.1 ∧
      (∃ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.2.1 result.2.2 model finalModel ∧
        (RecursorInitialTypehood env universes stats types elimLevel result.2.1 result.2.2
            model lparams isK isUnsafe rules ∧
          RecursorFinalTypehood env universes stats types elimLevel result.2.1 result.2.2
            finalModel lparams isK isUnsafe rules)) ∧
      result.1.constants.WF ∧
      (∀ name info, reader.env.find? name = some info → result.1.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel result.2.1 lparams result.2.2.lctx
        isK isUnsafe result.2.2 result.1 ∧
      LocalRecursorRuleRhsScope stats types result.2.1 result.2.2 result.1 := by
  have registered := mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport
  intro result success
  obtain ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩ :=
    registered result success
  have initial : RecursorInitialTypehood env universes stats types elimLevel result.2.1 result.2.2
      model lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.rawTypehood, receipt.storedTypehood,
      receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  have final : RecursorFinalTypehood env universes stats types elimLevel result.2.1 result.2.2
      finalModel lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.finalRawTypehood, receipt.finalStoredTypehood,
      receipt.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  exact ⟨frame, counts, ⟨finalModel, endpoint, initial, final⟩,
    registeredWF, retained, metadata, rhsScope⟩

theorem mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine (mkRecInfos.registeredTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader envWF constants definitions fieldOnly model modelWF native reserved
    nativeEnvWF mapped parentSupport minorSupport domainSupport).bind ?_
  rintro ⟨registeredEnv, finalInfos, finalReader⟩
    ⟨frame, counts, ⟨finalModel, endpoint, receipts⟩, registeredWF, retained, metadata, rhsScope⟩
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope

/- Registration can consume closed rule semantics while a later RHS consumer
   keeps a richer per-rule result.  The result relation is abstract here so
   this CPS layer does not depend on the concrete generated-body package. -/
theorem RecursorRuleRhsScope.impRegistrationRuleSemantics
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr} {ctx : Context}
    {ctors : List Constructor} {rules : List RecursorRule} {initial : Nat}
    (hscope : RecursorRuleRhsScope stats motives minors ctx ctors rules initial)
    (head : ∀ (entry : Constructor × Nat) (rule : RecursorRule),
      RecursorRuleRhsScopeReceipt stats motives minors ctx entry.1 minors[entry.2]! rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic) :
    List.Forall₂ (fun entry rule => ∃ semantic, TrExprS env universes [] rule.rhs semantic)
      (ctors.zipIdx initial) rules := by
  exact List.Forall₂.imp (fun entry rule receipt => head entry rule receipt) hscope

theorem mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults
    {ResultType : Type} {env : VEnv} {universes : List Name}
    {RuleResult : Array RecInfo → Context → Constructor → Expr → RecursorRule → Prop}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (resultHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RuleResult finalInfos finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            RuleResult finalInfos finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader next post envWF constants definitions fieldOnly model modelWF native
    reserved nativeEnvWF mapped parentSupport minorSupport domainSupport ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope
  have results : ∀ parent, parent < types.size → ∃ recursor,
      registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
      ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
        ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
          finalInfos[parent]!.minors[index]? = some minor ∧
          (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
          RuleResult finalInfos finalReader ctor minor rule := by
    intro parent hparent
    obtain ⟨recursor, hlookup, hentries⟩ := rhsScope parent hparent
    refine ⟨recursor, hlookup, ?_⟩
    intro index ctor hctor
    obtain ⟨rule, minor, hrule, hminor, hreceipt⟩ := hentries index ctor hctor
    exact ⟨rule, minor, hrule, hminor,
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        hreceipt hreceipt.fvars.counts.receipt,
      resultHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        hreceipt hreceipt.fvars.counts.receipt⟩
  have completeRuleSemantics := rhsScope.completeRuleSemantics metadata.metadata.orderedRules
    (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics

/- Instantiate the registration CPS boundary with the named generated
   constructor-RHS package.  The closed callback and generated callback are
   paired at each indexed receipt; the continuation receives complete
   stored-rule semantic coverage derived from that same indexed package. -/
theorem mkRecInfos.registeredScopedGeneratedRuleResultCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  exact mkRecInfos.registeredScopedTranslatedAppliedRecursorRuleResults
    (RuleResult := fun finalInfos finalReader ctor minor rule =>
      GeneratedRecursorRuleResult env universes stats
        (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
        finalReader ctor minor rule)
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
      scopedReceipt ordinaryReceipt =>
      generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
        scopedReceipt ordinaryReceipt)
    (fun registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
      registeredWF retained metadata rhsScope _results _completeRuleSemantics =>
      have completeRuleResults := rhsScope.completeRuleResultSemanticsIndexed
        metadata.metadata.orderedRules
        (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
          ⟨closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt,
            generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt⟩)
      have completeRuleSemantics := rhsScope.completeRuleSemanticsFromIndexed
        metadata.metadata.orderedRules
        (fun parent recursor index ctor rule minor scopedReceipt ordinaryReceipt =>
          ⟨closedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt,
            generatedHead registeredEnv finalInfos finalReader rhsScope parent recursor index ctor rule minor
              scopedReceipt ordinaryReceipt⟩)
      nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
        registeredWF retained metadata rhsScope completeRuleResults completeRuleSemantics)

/- Extend the generated-rule CPS boundary with the paired base/target iota
   endpoint.  The existing generated package remains available to the
   continuation; the additional indexed callback is obtained by projecting
   `GeneratedRecursorRuleIotaKind.baseAndTargetResults` from that same package. -/
theorem mkRecInfos.registeredScopedGeneratedRuleIotaCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic,
    hgenerated.iotaKind.baseAndTargetResults⟩

/- Keep the generated result and its paired base/target iota endpoint together
   in the registration CPS continuation.  The iota projection is derived from
   the exact generated witness supplied by the same indexed callback. -/
theorem mkRecInfos.registeredScopedGeneratedRuleIotaBaseAndTargetResultsCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic,
    hgenerated.iotaKind.baseAndTargetResults⟩

/- Keep the generated result and its paired base/target iota endpoint together
   in the registration CPS continuation.  The iota projection is derived from
   the exact generated witness supplied by the same indexed callback. -/
theorem mkRecInfos.registeredScopedGeneratedRuleResultAndIotaCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic, hgenerated,
    hgenerated.iotaKind.baseAndTargetResults⟩

theorem mkRecInfos.registeredScopedGeneratedRuleResultAndIotaBaseAndTargetResultsCPS
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (closedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        ∃ semantic, TrExprS env universes [] rule.rhs semantic)
    (generatedHead : ∀ (registeredEnv : Kernel.Environment) (finalInfos : Array RecInfo)
      (finalReader : Context),
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      ∀ (parent : Nat) (recursor : RecursorVal) (index : Nat) (ctor : Constructor)
        (rule : RecursorRule) (minor : Expr),
        RecursorRuleRhsScopeReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        RecursorRuleRhsReceipt stats (finalInfos.map (·.motive))
            (finalInfos.flatMap (·.minors)) finalReader ctor minor rule →
        GeneratedRecursorRuleResult env universes stats
          (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors)) finalReader ctor minor rule)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (∀ parent, parent < types.size →
        RecursorTypeModelReceipt env universes stats finalInfos parent finalReader model finalModel) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
          ∃ (rule : RecursorRule) (minor : Expr), recursor.rules[index]? = some rule ∧
            finalInfos[parent]!.minors[index]? = some minor ∧
            (∃ semantic, TrExprS env universes [] rule.rhs semantic) ∧
            GeneratedRecursorRuleResult env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule ∧
            GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats
              (finalInfos.map (·.motive)) (finalInfos.flatMap (·.minors))
              finalReader ctor minor rule) →
      (∀ parent, parent < types.size → ∃ recursor,
        registeredEnv.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
        ∀ rule ∈ recursor.rules, ∃ semantic, TrExprS env universes [] rule.rhs semantic) →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine mkRecInfos.registeredScopedGeneratedRuleResultCPS
    stats types elimLevel lparams isK isUnsafe reader next post envWF constants definitions fieldOnly
    model modelWF native reserved nativeEnvWF mapped parentSupport minorSupport domainSupport
    closedHead generatedHead ?_
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope results completeRuleSemantics
  apply nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope ?_ completeRuleSemantics
  intro parent hparent
  obtain ⟨recursor, hlookup, hentries⟩ := results parent hparent
  refine ⟨recursor, hlookup, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, minor, hrule, hminor, hsemantic, hgenerated⟩ := hentries index ctor hctor
  exact ⟨rule, minor, hrule, hminor, hsemantic, hgenerated,
    hgenerated.iotaKind.baseAndTargetResults⟩

theorem mkRecInfos.registeredScopedTranslatedAppliedInitialAndFinalTypehood
    {ResultType : Type} {env : VEnv} {universes : List Name}
    (stats : InductiveStats) (types : Array InductiveType) (elimLevel : Level)
    (lparams : List Name) (isK isUnsafe : Bool) (rules : List RecursorRule) (reader : Context)
    (next : Kernel.Environment → Array RecInfo → M ResultType) (post : ResultType → Prop)
    (envWF : env.WF) (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env) (fieldOnly : stats.params.size = 0)
    (model : MLCtx) (modelWF : model.WF env universes) (native : model.lctx = reader.lctx)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (nativeEnvWF : reader.env.constants.WF)
    {semanticElimLevel : VLevel} (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel)
    (parentSupport : (mkRecInfos.loopInd1 stats types elimLevel 0 #[]
      (fun parentInfos => do return (parentInfos, ← readThe Context)) reader).WF fun result =>
      ∀ trace : RecursorParentPassTrace stats types elimLevel 0 #[] reader result.1 result.2,
        RecursorParentPassTranslationSupport env universes trace)
    (minorSupport : ∀ parentInfos parentReader
      (parentTrace : RecursorParentPassTrace stats types elimLevel 0 #[] reader parentInfos parentReader)
      parentModel, TranslatedRecursorParentPass env universes parentTrace model parentModel →
      (mkRecInfos.loopInd2 stats types 0 parentInfos
        (fun finalInfos => do return (finalInfos, ← readThe Context)) parentReader).WF fun result =>
        ∀ trace : RecursorMinorPassTrace stats types 0 parentInfos parentReader result.1 result.2,
          MinorPassTranslationSupport env universes trace)
    (domainSupport : (mkRecInfos stats types elimLevel
      (fun finalInfos => do return (finalInfos, ← readThe Context)) reader).WF fun result =>
      ∀ finalModel, RecursorInfoModelEndpoint env universes stats types elimLevel reader
        result.1 result.2 model finalModel → ∀ parent, parent < types.size →
        RecursorSelectedDomainSupport env universes stats result.1 parent result.2.lctx model)
    (nextWF : ∀ registeredEnv finalInfos finalReader finalModel,
      reader.RecursorScopeFrame finalReader → RecursorInfoCounts types finalInfos →
      RecursorInfoModelEndpoint env universes stats types elimLevel reader finalInfos finalReader
        model finalModel →
      (RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
          model lparams isK isUnsafe rules ∧
        RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
          finalModel lparams isK isUnsafe rules) →
      registeredEnv.constants.WF →
      (∀ name info, reader.env.find? name = some info → registeredEnv.find? name = some info) →
      stats.RecursorOffsetMetadata types elimLevel finalInfos lparams finalReader.lctx
        isK isUnsafe finalReader registeredEnv →
      LocalRecursorRuleRhsScope stats types finalInfos finalReader registeredEnv →
      (next registeredEnv finalInfos finalReader).WF post) :
    (do let result ← mkRecInfos.scopeRegistration stats types elimLevel lparams isK isUnsafe reader
        next result.1 result.2.1 result.2.2).WF post := by
  refine (mkRecInfos.registeredScopedTranslatedAppliedRecursorTypes stats types elimLevel
    lparams isK isUnsafe reader next post envWF constants definitions fieldOnly model modelWF native
    reserved nativeEnvWF mapped parentSupport minorSupport domainSupport ?_)
  intro registeredEnv finalInfos finalReader finalModel frame counts endpoint receipts
    registeredWF retained metadata rhsScope
  have initial : RecursorInitialTypehood env universes stats types elimLevel finalInfos finalReader
      model lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.rawTypehood, receipt.storedTypehood,
      receipt.metadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  have final : RecursorFinalTypehood env universes stats types elimLevel finalInfos finalReader
      finalModel lparams isK isUnsafe rules := by
    intro parent bound
    have receipt := receipts parent bound
    exact ⟨receipt.finalRawTypehood, receipt.finalStoredTypehood,
      receipt.finalMetadataTypehood types elimLevel lparams isK isUnsafe rules⟩
  exact nextWF registeredEnv finalInfos finalReader finalModel frame counts endpoint ⟨initial, final⟩
    registeredWF retained metadata rhsScope

end Lean4Lean.AddInductive
