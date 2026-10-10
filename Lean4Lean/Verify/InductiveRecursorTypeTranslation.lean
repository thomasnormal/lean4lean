import Lean4Lean.Verify.InductiveMinorPassTranslationCPS
import Lean4Lean.Verify.InductiveRecursorTypeNative

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

inductive SelectedRecursorTelescope (env : VEnv) (universes : List Name)
    (full : LocalContext) (initial : MLCtx) : List FVarId → MLCtx → Prop where
  | nil : SelectedRecursorTelescope env universes full initial [] initial
  | push {ids : List FVarId} {model : MLCtx}
      (earlier : SelectedRecursorTelescope env universes full initial ids model)
      (identifier : FVarId) (physicalIndex : Nat) (name : Name) (domain : Expr)
      (binder : BinderInfo) (semantic : VExpr)
      (lookup : full.find? identifier =
        some (.cdecl physicalIndex identifier name domain binder .default))
      (fresh : model.lctx.find? identifier = none)
      (translated : TrExprS env universes model.vlctx domain semantic)
      (typed : env.IsType universes.length model.vlctx.toCtx semantic) :
      SelectedRecursorTelescope env universes full initial (ids ++ [identifier])
        (.vlam identifier name domain semantic binder model)

theorem SelectedRecursorTelescope.context
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) : final.WF env universes := by
  induction telescope with
  | nil => exact initialWF
  | push _ _ _ _ _ _ _ _ fresh translated typed earlierWF =>
    exact ⟨earlierWF, fresh, translated, typed⟩

theorem SelectedRecursorTelescope.extension
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final) :
    IndexMLCtxExtension initial ids final := by
  induction telescope with
  | nil => exact .nil
  | push _ identifier _ name domain binder semantic _ _ _ _ earlierExtension =>
    exact earlierExtension.push identifier name domain semantic binder

theorem SelectedRecursorTelescope.lookups
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) :
    ∀ identifier ∈ ids, ∃ physicalIndex projectedIndex name domain binder,
      full.find? identifier = some (.cdecl physicalIndex identifier name domain binder .default) ∧
      final.lctx.find? identifier =
        some (.cdecl projectedIndex identifier name domain binder .default) := by
  induction telescope with
  | nil => intro identifier member; cases member
  | @push ids model earlier identifier physicalIndex name domain binder semantic
      lookup fresh translated typed earlierLookups =>
    have modelWF := earlier.context initialWF
    have nextWF : (MLCtx.vlam identifier name domain semantic binder model).WF env universes :=
      ⟨modelWF, fresh, translated, typed⟩
    intro selected member
    rcases List.mem_append.mp member with oldMember | newMember
    · obtain ⟨oldPhysical, oldProjected, oldName, oldDomain, oldBinder, oldLookup, projectedLookup⟩ :=
        earlierLookups selected oldMember
      have different : selected ≠ identifier := by
        intro equality
        subst selected
        rw [fresh] at projectedLookup
        cases projectedLookup
      refine ⟨oldPhysical, oldProjected, oldName, oldDomain, oldBinder, oldLookup, ?_⟩
      rw [nextWF.find?_eq, MLCtx.decls, List.find?_cons]
      simpa only [LocalDecl.fvarId, beq_eq_false_iff_ne.mpr different] using
        modelWF.find?_eq.symm.trans projectedLookup
    · have equality : selected = identifier := List.mem_singleton.mp newMember
      subst selected
      refine ⟨physicalIndex, model.length, name, domain, binder, lookup, ?_⟩
      rw [nextWF.find?_eq]
      simp only [MLCtx.decls, List.find?_cons, LocalDecl.fvarId, beq_self_eq_true]

theorem SelectedRecursorTelescope.distinct
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) : ids.Nodup := by
  have extension := telescope.extension
  have selected := (telescope.context initialWF).fvarRevList_nodup ids.length extension.bound
  rw [extension.selection] at selected
  exact List.nodup_reverse.mp selected

theorem SelectedRecursorTelescope.bindingAgreement
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) :
    SelectedCDeclBindingAgreement full final.lctx ids := by
  intro identifier member
  obtain ⟨physicalIndex, projectedIndex, name, domain, binder, actualLookup, projectedLookup⟩ :=
    telescope.lookups initialWF identifier member
  exact ⟨physicalIndex, projectedIndex, name, domain, binder, .default, .default,
    actualLookup, projectedLookup⟩

theorem SelectedRecursorTelescope.nativeBindingEquation
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (initialWF : initial.WF env universes) (fullScope : full.BindingScope)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExprS env universes final.vlctx body bodySemantic) :
    full.mkForall (ids.map Expr.fvar).toArray body =
      final.lctx.mkForall (ids.map Expr.fvar).toArray body := by
  have closed : body.looseBVarRange' = 0 :=
    (final.noBV ▸ translated.closed).looseBVarRange_zero
  exact mkForall_congr_selected_cdecl ids fullScope (telescope.context initialWF).bindingScope
    closed (telescope.distinct initialWF) (telescope.bindingAgreement initialWF)

def RecursorTypeBodyApplicationSupport (env : VEnv) (universes : List Name)
    (infos : Array RecInfo) (parent : Nat) (virtual : VLCtx) : Prop :=
  ∃ majorSemantic majorType motiveSemantic level,
    TrExprS env universes virtual infos[parent]!.major majorSemantic ∧
    env.HasType universes.length virtual.toCtx majorSemantic majorType ∧
    TrExprS env universes virtual (mkAppN infos[parent]!.motive infos[parent]!.indices) motiveSemantic ∧
    env.HasType universes.length virtual.toCtx motiveSemantic (.forallE majorType (.sort level))

theorem RecursorTypeBodyApplicationSupport.translated
    {env : VEnv} {universes : List Name} {infos : Array RecInfo} {parent : Nat} {virtual : VLCtx}
    (support : RecursorTypeBodyApplicationSupport env universes infos parent virtual) :
    ∃ bodySemantic level,
      TrExprS env universes virtual
        (.app (mkAppN infos[parent]!.motive infos[parent]!.indices) infos[parent]!.major)
        bodySemantic ∧
      env.HasType universes.length virtual.toCtx bodySemantic (.sort level) := by
  obtain ⟨majorSemantic, majorType, motiveSemantic, level, majorTranslated, majorTyped,
    motiveTranslated, motiveTyped⟩ := support
  refine ⟨.app motiveSemantic majorSemantic, level, ?_, ?_⟩
  · exact TrExprS.app motiveTyped majorTyped motiveTranslated majorTranslated
  · simpa only [VExpr.inst] using motiveTyped.app majorTyped

theorem SelectedRecursorTelescope.typedAbstraction
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial final : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {body : Expr} {bodySemantic : VExpr}
    (translated : TrExprS env universes final.vlctx body bodySemantic)
    (typed : env.IsType universes.length final.vlctx.toCtx bodySemantic) :
    ∃ abstracted level,
      TrExprS env universes initial.vlctx
        (final.lctx.mkForall (ids.map Expr.fvar).toArray body) abstracted ∧
      env.HasType universes.length initial.vlctx.toCtx abstracted (.sort level) := by
  obtain ⟨bodyLevel, bodyTyped⟩ := typed
  obtain ⟨domainTranslated, level, domainTyped⟩ := telescope.extension.typedBodyAbstraction
    envWF (telescope.context initialWF) ⟨bodySemantic, translated, bodyTyped.toU⟩ ⟨bodyLevel, bodyTyped⟩
  obtain ⟨strictSemantic, strictTranslated, equality⟩ := domainTranslated
  exact ⟨strictSemantic, level, strictTranslated,
    domainTyped.defeqU_l envWF initialWF.tr.wf.toCtx equality.symm⟩

def RecursorRawTypeTranslationSupport (env : VEnv) (universes : List Name)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (full : LocalContext) (initial : MLCtx) : Prop :=
  ∃ ids, (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar ∧
    (∃ projected, SelectedRecursorTelescope env universes full initial ids projected) ∧
    ∀ projected, SelectedRecursorTelescope env universes full initial ids projected →
      RecursorTypeBodyApplicationSupport env universes infos parent projected.vlctx

theorem RecursorRawTypeTranslationSupport.selectedTypeTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {parent : Nat} {full : LocalContext} {initial : MLCtx}
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent full initial)
    (envWF : env.WF) (initialWF : initial.WF env universes) (fullScope : full.BindingScope) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (full.mkForall (recursorTypeBinders stats infos parent) (recursorTypeBody infos parent))
        typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) := by
  obtain ⟨ids, selected, ⟨projected, telescope⟩, bodySupport⟩ := support
  obtain ⟨bodySemantic, bodyLevel, bodyTranslated, bodyTyped⟩ := (bodySupport projected telescope).translated
  have bodyTranslation : TrExprS env universes projected.vlctx (recursorTypeBody infos parent)
      bodySemantic := bodyTranslated
  obtain ⟨typeSemantic, level, translated, typed⟩ := telescope.typedAbstraction envWF initialWF
    bodyTranslation ⟨bodyLevel, bodyTyped⟩
  have selectedArray : recursorTypeBinders stats infos parent = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  have binding := telescope.nativeBindingEquation initialWF fullScope bodyTranslation
  exact ⟨typeSemantic, level, by simpa only [selectedArray, binding] using translated, typed⟩

theorem RecursorInfoModelEndpoint.liftTypeTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) {expression : Expr} {semantic : VExpr} {level : VLevel}
    (translated : TrExprS env universes initial.vlctx expression semantic)
    (typed : env.HasType universes.length initial.vlctx.toCtx semantic (.sort level)) :
    TrExprS env universes final.vlctx expression
        (semantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (semantic.liftN (final.length - initial.length)) (.sort level) := by
  obtain ⟨allocated, extension⟩ := endpoint.extension
  have count : final.length - initial.length = allocated.length := by
    have lengths := extension.length_eq
    omega
  constructor
  · simpa only [count] using
      translated.weakFV envWF.ordered extension.weakening endpoint.context.1.tr.wf
  · simpa only [count, VExpr.liftN] using
      typed.weakN envWF.ordered extension.weakening.toCtx

theorem RecursorRawTypeTranslationSupport.rawTypeTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {parent : Nat} {full : LocalContext} {initial : MLCtx}
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent full initial)
    (envWF : env.WF) (initialWF : initial.WF env universes) (fullScope : full.BindingScope) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx (recursorRawType stats infos parent full) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) := by
  obtain ⟨typeSemantic, level, translated, typed⟩ :=
    support.selectedTypeTranslation envWF initialWF fullScope
  obtain ⟨ids, selected, ⟨projected, telescope⟩, bodySupport⟩ := support
  obtain ⟨bodySemantic, _, bodyTranslated, _⟩ := (bodySupport projected telescope).translated
  have bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0 :=
    (projected.noBV ▸ bodyTranslated.closed).looseBVarRange_zero
  have shape := BinderArrayFVars.of_toList_eq selected
  have selectedIds := binderArrayIds_of_toList_eq selected
  have distinct : (binderArrayIds (recursorTypeBinders stats infos parent)).Nodup := by
    simpa only [selectedIds] using telescope.distinct initialWF
  have bindings : SelectedCDeclBindings full (binderArrayIds (recursorTypeBinders stats infos parent)) := by
    simpa only [selectedIds] using (telescope.bindingAgreement initialWF).left
  have flattened := recursorRawType_eq_flat stats infos parent full fullScope bodyClosed
    shape distinct bindings
  exact ⟨typeSemantic, level, by simpa only [flattened] using translated, typed⟩

theorem RecursorInfoModelEndpoint.rawTypeTranslation
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (_parameterFree : stats.params.size = 0) (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent finalReader.lctx) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) := by
  have fullScope : finalReader.lctx.BindingScope := by
    simpa only [endpoint.context.2.1] using endpoint.context.1.bindingScope
  exact support.rawTypeTranslation envWF initialWF fullScope

theorem RecursorInfoModelEndpoint.rawTypeAtFinal
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {types : Array InductiveType}
    {elimLevel : Level} {reader finalReader : Context} {infos : Array RecInfo}
    {initial final : MLCtx}
    (endpoint : RecursorInfoModelEndpoint env universes stats types elimLevel
      reader infos finalReader initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (parameterFree : stats.params.size = 0) (parent : Nat)
    (support : RecursorRawTypeTranslationSupport env universes stats infos parent
      finalReader.lctx initial) :
    ∃ typeSemantic level,
      TrExprS env universes initial.vlctx
        (recursorRawType stats infos parent finalReader.lctx) typeSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx typeSemantic (.sort level) ∧
      TrExprS env universes final.vlctx
        (recursorRawType stats infos parent finalReader.lctx)
        (typeSemantic.liftN (final.length - initial.length)) ∧
      env.HasType universes.length final.vlctx.toCtx
        (typeSemantic.liftN (final.length - initial.length)) (.sort level) := by
  obtain ⟨typeSemantic, level, translated, typed⟩ := endpoint.rawTypeTranslation
    envWF initialWF parameterFree parent support
  obtain ⟨translatedLater, typedLater⟩ := endpoint.liftTypeTranslation envWF translated typed
  exact ⟨typeSemantic, level, translated, typed, translatedLater, typedLater⟩

end Lean4Lean.AddInductive
