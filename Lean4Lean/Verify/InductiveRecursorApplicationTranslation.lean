import Lean4Lean.Verify.InductiveRecursorApplicationFacts
import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.InductiveRecursorApplicationNative
import Lean4Lean.Verify.InductiveRecursorTypeTranslation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.cdeclTranslation
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (modelWF : model.WF env universes) (envWF : env.WF)
    {identifier : FVarId} {index : Nat} {name : Name} {domain : Expr}
    {binder : BinderInfo} {kind : LocalDeclKind}
    (lookup : model.lctx.find? identifier = some (.cdecl index identifier name domain binder kind)) :
    ∃ valueSemantic domainSemantic,
      model.vlctx.find? (.inr identifier) = some (valueSemantic, domainSemantic) ∧
      TrExprS env universes model.vlctx (.fvar identifier) valueSemantic ∧
      TrExprS env universes model.vlctx domain domainSemantic ∧
      env.HasType universes.length model.vlctx.toCtx valueSemantic domainSemantic := by
  have member := List.mem_of_find?_eq_some
    (modelWF.tr.1.find?_eq_find?_toList ▸ lookup)
  obtain ⟨valueSemantic, domainSemantic, semanticLookup, _, _, valueTranslated, domainTranslated⟩ :=
    modelWF.tr.find?_of_mem envWF member
  exact ⟨valueSemantic, domainSemantic, semanticLookup, valueTranslated, domainTranslated,
    modelWF.tr.wf.find?_wf envWF.ordered semanticLookup⟩

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.selectedForallApplication
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (modelWF : model.WF env universes) (envWF : env.WF)
    (identifiers : List FVarId) (distinct : identifiers.Nodup)
    (bindings : SelectedCDeclBindings model.lctx identifiers)
    {body : Expr} (bodyClosed : body.looseBVarRange' = 0)
    {value : Expr} {valueSemantic typeSemantic : VExpr}
    (valueTranslated : TrExprS env universes model.vlctx value valueSemantic)
    (valueTyped : env.HasType universes.length model.vlctx.toCtx valueSemantic typeSemantic)
    (typeTranslated : TrExprS env universes model.vlctx
      (model.lctx.mkForall (identifiers.map Expr.fvar).toArray body) typeSemantic) :
    ∃ applicationSemantic bodySemantic,
      TrExprS env universes model.vlctx
        (mkAppN value (identifiers.map Expr.fvar).toArray) applicationSemantic ∧
      env.HasType universes.length model.vlctx.toCtx applicationSemantic bodySemantic ∧
      TrExprS env universes model.vlctx body bodySemantic := by
  induction identifiers generalizing value valueSemantic typeSemantic with
  | nil =>
    rw [mkForall_selected_fold [] modelWF.bindingScope bodyClosed distinct bindings,
      List.foldr_nil] at typeTranslated
    exact ⟨valueSemantic, typeSemantic, by simpa using valueTranslated, valueTyped,
      typeTranslated⟩
  | cons identifier identifiers tailInduction =>
    obtain ⟨index, name, domain, binder, kind, lookup⟩ := bindings identifier (by simp)
    rw [mkForall_selected_cons identifier identifiers modelWF.bindingScope bodyClosed distinct
      bindings index name domain binder kind lookup] at typeTranslated
    cases typeTranslated with
    | forallE domainIsType bodyIsType domainTranslated bodyTranslated =>
      obtain ⟨argumentSemantic, argumentType, _, argumentTranslated, argumentTypeTranslated,
        argumentTyped⟩ := modelWF.cdeclTranslation envWF lookup
      have argumentAlignment := argumentTypeTranslated.uniq envWF
        (.refl envWF modelWF.tr.wf) domainTranslated
      have convertedTyped := argumentTyped.defeqU_r envWF modelWF.tr.wf.toCtx argumentAlignment
      have applicationTranslated := TrExprS.app valueTyped convertedTyped
        valueTranslated argumentTranslated
      have applicationTyped := valueTyped.app convertedTyped
      have instantiatedType := bodyTranslated.inst envWF.ordered convertedTyped argumentTranslated
      rw [Expr.instantiate1'_abstract1] at instantiatedType
      have tailBindings := bindings.subset
        (fun selected member => List.mem_cons_of_mem identifier member)
      obtain ⟨applicationSemantic, bodySemantic, translated, typed, terminalTranslated⟩ :=
        tailInduction distinct.tail tailBindings applicationTranslated applicationTyped instantiatedType
      refine ⟨applicationSemantic, bodySemantic, ?_, typed, terminalTranslated⟩
      simpa only [mkAppN, ← Array.foldl_toList, List.toList_toArray, List.map_cons,
        List.foldl_cons, mkApp] using translated

theorem _root_.Lean4Lean.TypeChecker.MLCtx.WF.selectedForallSortApplication
    {env : VEnv} {universes : List Name} {model : MLCtx}
    (modelWF : model.WF env universes) (envWF : env.WF)
    (identifiers : List FVarId) (distinct : identifiers.Nodup)
    (bindings : SelectedCDeclBindings model.lctx identifiers)
    {level : Level} {semanticLevel : VLevel}
    (mapped : VLevel.ofLevel universes level = some semanticLevel)
    {value : Expr} {valueSemantic typeSemantic : VExpr}
    (valueTranslated : TrExprS env universes model.vlctx value valueSemantic)
    (valueTyped : env.HasType universes.length model.vlctx.toCtx valueSemantic typeSemantic)
    (typeTranslated : TrExprS env universes model.vlctx
      (model.lctx.mkForall (identifiers.map Expr.fvar).toArray (.sort level)) typeSemantic) :
    ∃ applicationSemantic,
      TrExprS env universes model.vlctx
        (mkAppN value (identifiers.map Expr.fvar).toArray) applicationSemantic ∧
      env.HasType universes.length model.vlctx.toCtx applicationSemantic (.sort semanticLevel) := by
  obtain ⟨applicationSemantic, bodySemantic, translated, typed, terminalTranslated⟩ :=
    modelWF.selectedForallApplication envWF identifiers distinct bindings rfl
      valueTranslated valueTyped typeTranslated
  cases terminalTranslated with
  | sort terminalMapped =>
    cases Option.some.inj (mapped.symm.trans terminalMapped)
    exact ⟨applicationSemantic, translated, typed⟩

theorem SelectedRecursorTelescope.selectedMember
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial projected : MLCtx}
    {ids : List FVarId} (_telescope : SelectedRecursorTelescope env universes full initial ids projected)
    {stats : InductiveStats} {infos : Array RecInfo} {parent : Nat}
    (selected : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    {expression : Expr} (member : expression ∈ (recursorTypeBinders stats infos parent).toList) :
    expression.fvarId! ∈ ids := by
  rw [selected] at member
  obtain ⟨identifier, identifierMember, expressionEq⟩ := List.mem_map.mp member
  rw [← expressionEq]
  exact identifierMember

theorem SelectedRecursorTelescope.bindingAgreementFor
    {env : VEnv} {universes : List Name} {full : LocalContext} {initial projected : MLCtx}
    {ids : List FVarId} (telescope : SelectedRecursorTelescope env universes full initial ids projected)
    (initialWF : initial.WF env universes) {selected : List FVarId}
    (included : ∀ identifier ∈ selected, identifier ∈ ids) :
    SelectedCDeclBindingAgreement full projected.lctx selected :=
  fun identifier member => telescope.bindingAgreement initialWF identifier (included identifier member)

theorem SelectedRecursorTelescope.bodyApplicationSupport
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo} {parent : Nat}
    {original current : Context} {initial projected : MLCtx} {ids : List FVarId}
    (telescope : SelectedRecursorTelescope env universes current.lctx initial ids projected)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (fullScope : current.lctx.BindingScope) (bound : parent < infos.size)
    (selected : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    (source : RecursorInfoIndexSource stats types elimLevel parent original infos[parent]! current)
    {semanticElimLevel : VLevel}
    (mapped : VLevel.ofLevel universes elimLevel = some semanticElimLevel) :
    RecursorTypeBodyApplicationSupport env universes infos parent projected.vlctx := by
  have projectedWF := telescope.context initialWF
  have projectedScope := projectedWF.bindingScope
  have agreement := telescope.bindingAgreement initialWF
  have majorMember : infos[parent]!.major ∈ (recursorTypeBinders stats infos parent).toList := by
    simp [recursorTypeBinders]
  have majorIdMember := telescope.selectedMember selected majorMember
  have shape := BinderArrayFVars.of_toList_eq selected
  obtain ⟨majorIdentifier, majorShape⟩ := shape infos[parent]!.major majorMember
  have majorIdentifierEq : infos[parent]!.major.fvarId! = majorIdentifier := by
    rw [majorShape]; rfl
  rw [majorIdentifierEq] at majorIdMember
  have majorAgreement := telescope.bindingAgreementFor initialWF
    (selected := [majorIdentifier]) (fun identifier member => by
      obtain rfl := List.mem_singleton.mp member
      exact majorIdMember)
  obtain ⟨_, majorIndex, majorName, majorDomain, majorBinder, _, majorKind, _, majorLookup⟩ :=
    agreement majorIdentifier majorIdMember
  have majorArray : #[infos[parent]!.major] = ([majorIdentifier].map Expr.fvar).toArray := by
    simp only [majorShape, List.map_cons, List.map_nil]
  have indexIncluded : ∀ identifier ∈ binderArrayIds infos[parent]!.indices, identifier ∈ ids := by
    intro identifier member
    obtain ⟨expression, member, equality⟩ := List.mem_map.mp member
    have selectedMember : expression ∈ (recursorTypeBinders stats infos parent).toList := by
      simp only [recursorTypeBinders, Array.toList_append, List.mem_append]
      exact Or.inl (Or.inr member)
    exact equality ▸ telescope.selectedMember selected selectedMember
  have indexAgreement := telescope.bindingAgreementFor initialWF indexIncluded
  have indicesShape : BinderArrayFVars infos[parent]!.indices := by
    intro expression member
    exact shape expression (by
      simp only [recursorTypeBinders, Array.toList_append, List.mem_append]
      exact Or.inl (Or.inr member))
  have indicesArray := indicesShape.array_eq
  have fullDistinct : (binderArrayIds (recursorTypeBinders stats infos parent)).Nodup := by
    rw [binderArrayIds_of_toList_eq selected]
    exact telescope.distinct initialWF
  simp only [recursorTypeBinders, binderArrayIds_append] at fullDistinct
  have indicesDistinct := (List.nodup_append.mp (List.nodup_append.mp fullDistinct).1).2.1
  have majorBindingEquation : current.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel) =
      projected.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel) := by
    rw [majorArray]
    exact mkForall_congr_selected_cdecl [majorIdentifier] fullScope projectedScope rfl
      (by simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
        and_self]) majorAgreement
  have majorClosed : (current.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel)).looseBVarRange' = 0 := by
    rw [majorArray]
    exact mkForall_selected_closed [majorIdentifier] fullScope rfl (by simp) majorAgreement.left
  have motiveBindingEquation : current.lctx.mkForall infos[parent]!.indices
        (current.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel)) =
      projected.lctx.mkForall infos[parent]!.indices
        (projected.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel)) := by
    rw [indicesArray, ← majorBindingEquation]
    exact mkForall_congr_selected_cdecl (binderArrayIds infos[parent]!.indices)
      fullScope projectedScope majorClosed indicesDistinct indexAgreement
  have parentMember : infos[parent]! ∈ infos := by
    simpa only [getElem!_pos infos parent bound] using Array.getElem_mem bound
  have motiveMember : infos[parent]!.motive ∈ (recursorTypeBinders stats infos parent).toList := by
    have member : infos[parent]!.motive ∈ (infos.map (fun info => info.motive)).toList :=
      Array.mem_toList_iff.mpr (Array.mem_map.mpr ⟨infos[parent]!, parentMember, rfl⟩)
    simp only [recursorTypeBinders, Array.toList_append, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr member)))
  obtain ⟨nativeMotiveIndex, motiveIdentifier, nativeMotiveLookup, motiveShape⟩ :=
    source.motiveLookupAtCurrent fullScope
  have motiveIdentifierEq : infos[parent]!.motive.fvarId! = motiveIdentifier := by
    rw [← motiveShape]; rfl
  have motiveIdMember := telescope.selectedMember selected motiveMember
  rw [motiveIdentifierEq] at motiveIdMember nativeMotiveLookup
  obtain ⟨_, motiveIndex, motiveName, motiveDomain, motiveBinder, _, motiveKind,
    fullMotiveLookup, motiveLookup⟩ := agreement motiveIdentifier motiveIdMember
  have declarationEquation := Option.some.inj (fullMotiveLookup.symm.trans nativeMotiveLookup)
  have motiveDomainEquation := congrArg LocalDecl.type declarationEquation
  obtain ⟨motiveSemantic, motiveType, _, motiveTranslated, motiveTypeTranslated, motiveTyped⟩ :=
    projectedWF.cdeclTranslation envWF motiveLookup
  change motiveDomain = current.lctx.mkForall infos[parent]!.indices
    (current.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel)) at motiveDomainEquation
  rw [motiveDomainEquation, motiveBindingEquation] at motiveTypeTranslated
  have projectedMajorClosed :
      (projected.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel)).looseBVarRange' = 0 := by
    rwa [majorBindingEquation] at majorClosed
  obtain ⟨applicationSemantic, applicationType, applicationTranslated, applicationTyped,
    applicationTypeTranslated⟩ := projectedWF.selectedForallApplication envWF
      (binderArrayIds infos[parent]!.indices) indicesDistinct indexAgreement.right
      projectedMajorClosed motiveTranslated motiveTyped (by
        simpa only [← indicesArray] using motiveTypeTranslated)
  have majorArrow : projected.lctx.mkForall #[infos[parent]!.major] (.sort elimLevel) =
      .forallE majorName majorDomain (.sort elimLevel) majorBinder := by
    rw [majorArray, mkForall_selected_fold [majorIdentifier] projectedScope rfl
      (by simp) majorAgreement.right]
    simp only [List.foldr_cons, List.foldr_nil, Expr.abstract1,
      LocalContext.mkBindingList1, majorLookup, Expr.abstractList, Bool.false_eq_true, if_false]
  rw [majorArrow] at applicationTypeTranslated
  cases applicationTypeTranslated with
  | forallE _ _ majorDomainTranslated arrowSortTranslated =>
    cases arrowSortTranslated with
    | sort arrowMapped =>
      cases Option.some.inj (mapped.symm.trans arrowMapped)
      obtain ⟨majorSemantic, majorType, _, majorTranslated, majorTypeTranslated, majorTyped⟩ :=
        projectedWF.cdeclTranslation envWF majorLookup
      have majorAlignment := majorTypeTranslated.uniq envWF
        (.refl envWF projectedWF.tr.wf) majorDomainTranslated
      have convertedMajor := majorTyped.defeqU_r envWF projectedWF.tr.wf.toCtx majorAlignment
      refine ⟨majorSemantic, _, applicationSemantic, semanticElimLevel, ?_, convertedMajor,
        ?_, applicationTyped⟩
      · simpa only [← majorShape] using majorTranslated
      · simpa only [← motiveShape, ← indicesArray] using applicationTranslated

end Lean4Lean.AddInductive
