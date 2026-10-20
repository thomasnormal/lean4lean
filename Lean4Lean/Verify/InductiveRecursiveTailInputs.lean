import Lean4Lean.Verify.InductiveRecursorTailAlignment

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

private theorem mkAppList_eqv_sameArgs {left right : Expr} (arguments : List Expr)
    (heads : (left == right) = true) :
    (left.mkAppList arguments == right.mkAppList arguments) = true := by
  induction arguments generalizing left right with
  | nil => exact heads
  | cons argument arguments induction =>
    apply induction
    change (Expr.app left argument).eqv (.app right argument) = true
    rw [Expr.eqv_eq]
    simpa only [(· == ·), Expr.eqv', ← Expr.eqv_eq] using
      (show ((left == right) && (argument == argument)) = true by rw [heads]; simp)

/-- Family recognition preserves accepted parameter annotation/name variation
through application to the actual changed indices. -/
theorem isValidIndAppIdx.familyIndexApplicationMatches
    (accepted : isValidIndAppIdx stats terminal parent = true) :
    (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2 == terminal) = true := by
  have compared := mkAppList_eqv_sameArgs (getIIndices stats terminal).2.toList
    (isValidIndAppIdx.familyIndexPrefixMatches accepted)
  rw [familyIndexPrefix_apply] at compared
  have applicationConstructor : mkApp = Expr.app := rfl
  simpa only [mkAppN, Array.foldl_toList, Expr.mkAppList_eq_foldl, applicationConstructor] using compared

/-- The exact stored tail agrees with the actual terminal in native expression
comparison, even when native parameter expressions are structurally distinct. -/
theorem canonicalRecursorTail_matchesFieldTerminal
    (accepted : isValidIndAppIdx stats terminal parent = true)
    (selectedParent : parent = (getIIndices stats terminal).1)
    (infos : Array RecInfo) (name : Name) (binder : BinderInfo) :
    (Expr.forallE name (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) binder ==
      .forallE name terminal
        (.app ((mkAppN infos[(getIIndices stats terminal).1]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1)
          (.bvar 0)) binder) = true := by
  rw [← selectedParent]
  change (Expr.forallE _ _ _ _).eqv (.forallE _ _ _ _) = true
  rw [Expr.eqv_eq]
  have domain := isValidIndAppIdx.familyIndexApplicationMatches accepted
  have reflexive : ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1).eqv
      ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1) = true := Expr.eqv_refl _
  simpa only [Expr.eqv', ← Expr.eqv_eq, reflexive, decide_true,
    Bool.and_true, Bool.not_false, Bool.true_or, (· == ·)] using domain

/-- The actual selected index/major declarations determine the canonical tail.
The domain retains the stored family prefix; accepted field-prefix variations
are aligned by expression comparison in the call consumer. -/
theorem UArgModelEndpoint.canonicalIndexArgumentsFromSelectedTrace
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source sortTerminal terminal argument : Expr} {index finalIndex : Nat}
    {arguments : Array Expr} {reader indexReader fieldReader finalReader : Context}
    {virtual finalVirtual : VLCtx} {semantic finalSemantic : VExpr} {base initial final : MLCtx}
    (infos : Array RecInfo) (parent : Nat)
    {trace : RecursorIndexTrace stats source index #[] reader sortTerminal finalIndex infos[parent]!.indices indexReader}
    {opening : RecursorUArgOpeningTrace argument fieldReader terminal arguments finalReader}
    (endpoint : UArgModelEndpoint env universes opening initial final)
    (input : FamilyIndexInput env universes base stats terminal source)
    (history : TranslatedRecursorIndexTrace env universes trace virtual semantic finalVirtual finalSemantic)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (native : base.lctx = reader.lctx) (converted : base.vlctx = virtual)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (insertion : VLCtx.FVLift' base.vlctx final.vlctx 0 lift 0)
    (full : LocalContext) (fullScope : full.BindingScope)
    (agreement : SelectedCDeclBindingAgreement indexReader.lctx full (binderArrayIds infos[parent]!.indices))
    (arity : (getIIndices stats terminal).2.size = infos[parent]!.indices.size)
    (major : FVarId) (majorShape : infos[parent]!.major = .fvar major)
    (majorIndex : Nat) (majorName : Name) (majorBinder : BinderInfo) (majorKind : LocalDeclKind)
    (majorLookup : full.find? major = some (.cdecl majorIndex major majorName
      (mkAppN (mkAppN stats.indConsts[parent]! stats.params) infos[parent]!.indices) majorBinder majorKind))
    (headClosed : (mkAppN stats.indConsts[parent]! stats.params).looseBVarRange' = 0)
    (motiveClosed : infos[parent]!.motive.looseBVarRange' = 0)
    (headDisjoint : ∀ identifier ∈ (mkAppN stats.indConsts[parent]! stats.params).fvarsList,
      identifier ∉ binderArrayIds infos[parent]!.indices)
    (motiveDisjoint : ∀ identifier ∈ infos[parent]!.motive.fvarsList,
      identifier ∉ binderArrayIds infos[parent]!.indices)
    (majorFresh : major ∉ infos[parent]!.motive.fvarsList)
    (majorDifferent : major ∉ binderArrayIds infos[parent]!.indices) :
    NativeTelescopeArguments env universes final
      (full.mkForall infos[parent]!.indices (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder) := by
  obtain ⟨indexModel, ids, indexWF, indexNative, indexVirtual, array, telescope, _⟩ :=
    input.reconstruct history envWF baseWF native converted reserved
  simp only [List.nil_append] at array
  have selected := binderArrayIds_of_toList_eq array
  have actualArray : infos[parent]!.indices = (ids.map Expr.fvar).toArray := by
    rw [← array, Array.toArray_toList]
  have argumentsClosed : ∀ value ∈ (getIIndices stats terminal).2.toList, value.looseBVarRange' = 0 := by
    obtain ⟨semantic, translated⟩ := endpoint.terminalTranslation
    rw [← familyIndexPrefix_apply stats terminal] at translated
    have closed := (final.noBV ▸ translated.closed).looseBVarRange_zero
    have allClosed := Expr.mkAppRevList_args_noLooseBVars (familyIndexPrefix stats terminal)
      (getIIndices stats terminal).2.toList.reverse (by
        simpa only [← Expr.mkAppList_reverse, List.reverse_reverse] using closed)
    intro value member
    exact allClosed value (List.mem_reverse.mpr member)
  have count : (getIIndices stats terminal).2.toList.length = ids.length := by
    have sizes := congrArg List.length array
    simp only [Array.length_toList, List.length_map] at sizes ⊢
    omega
  have applicationConstructor : mkApp = Expr.app := rfl
  have head : mkAppN (mkAppN stats.indConsts[parent]! stats.params) infos[parent]!.indices =
      (mkAppN stats.indConsts[parent]! stats.params).mkAppList (ids.map Expr.fvar) := by
    simp only [mkAppN, ← array, Array.foldl_toList, Expr.mkAppList_eq_foldl, applicationConstructor]
  have motiveApp : mkAppN infos[parent]!.motive infos[parent]!.indices =
      infos[parent]!.motive.mkAppList (ids.map Expr.fvar) := by
    simp only [mkAppN, ← array, Array.foldl_toList, Expr.mkAppList_eq_foldl, applicationConstructor]
  have lookup := majorLookup
  rw [head] at lookup
  have majorTail := recursorMajorTail_eq fullScope major majorIndex majorName _ majorBinder majorKind
    lookup infos[parent]!.motive ids motiveClosed majorFresh (selected ▸ majorDifferent)
  have tailClosed : (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)).looseBVarRange' = 0 := by
    rw [recursorTypeBody, majorShape, motiveApp, majorTail]
    have domainClosed := Expr.mkAppList_closed (mkAppN stats.indConsts[parent]! stats.params) (ids.map Expr.fvar) headClosed (by
      intro value member; obtain ⟨_, _, rfl⟩ := List.mem_map.mp member; rfl)
    have resultClosed := Expr.mkAppList_closed infos[parent]!.motive (ids.map Expr.fvar) motiveClosed (by
      intro value member; obtain ⟨_, _, rfl⟩ := List.mem_map.mp member; rfl)
    simp [Expr.looseBVarRange', domainClosed, resultClosed]
  obtain ⟨targetEnd, support⟩ := endpoint.indexArgumentsFromSelectedTrace input history envWF baseWF
    native converted reserved insertion full fullScope agreement _ tailClosed arity
  have support' := support
  rw [actualArray] at support'
  have terminalEq := support'.terminalOfSelected fullScope tailClosed (telescope.distinct baseWF)
    (selected ▸ agreement).right count argumentsClosed
  rw [recursorTypeBody, majorShape, motiveApp] at terminalEq
  rw [recursorMajorTail_substitution fullScope major majorIndex majorName majorBinder majorKind
    (mkAppN stats.indConsts[parent]! stats.params) infos[parent]!.motive ids _ lookup
    (telescope.distinct baseWF) count argumentsClosed headClosed motiveClosed
    (selected ▸ headDisjoint) (selected ▸ motiveDisjoint) majorFresh (selected ▸ majorDifferent)] at terminalEq
  rw [terminalEq] at support
  simpa only [mkAppN, Array.foldl_toList, Expr.mkAppList_eq_foldl, applicationConstructor] using support

/-- Accepted native tail comparison aligns the actual stored signature with
the field terminal before applying the major value. -/
theorem UArgModelEndpoint.recursiveCallFromInputOfEqvTail
    {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    {name : Name} {levels : List Level} {source : Expr}
    (input : RecursorConstantInput env universes final.vlctx name levels source)
    (envWF : env.WF) (stats : InductiveStats) (motives minors indices : Array Expr)
    {majorName : Name} {majorBody actualTail : Expr} {majorBinder : BinderInfo}
    (prefixArguments : NativeTelescopeArguments env universes final source
      (stats.params ++ motives ++ minors ++ indices).toList
      actualTail)
    (tailMatches : (actualTail == .forallE majorName terminal majorBody majorBinder) = true) :
    ∃ value resultType,
      TrExprS env universes final.vlctx
        ((mkAppN (mkAppN (mkAppN (mkAppN (.const name levels) stats.params)
          motives) minors) indices).app (mkAppN argument arguments)) value ∧
      TrExprS env universes final.vlctx
        (majorBody.instantiate1' (mkAppN argument arguments)) resultType ∧
      env.HasType universes.length final.vlctx.toCtx value resultType := by
  have modelWF := endpoint.context.1
  obtain ⟨prefixValue, prefixType, prefixTranslated, prefixTypeTranslated, prefixTyped⟩ :=
    prefixArguments.application envWF modelWF input.sourceTranslated input.valueTranslated input.valueTyped
  have prefixTypeTranslated := prefixTypeTranslated.eqv tailMatches
  cases prefixTypeTranslated with
  | forallE _ _ domainTranslated bodyTranslated =>
    obtain ⟨majorValue, majorType, majorTranslated, majorTypeTranslated, majorTyped⟩ :=
      endpoint.application envWF
    have equality := majorTypeTranslated.uniq envWF
      (.refl envWF modelWF.tr.wf) domainTranslated
    have converted := majorTyped.defeqU_r envWF modelWF.tr.wf.toCtx equality
    refine ⟨_, _, ?_, bodyTranslated.inst envWF.ordered converted majorTranslated,
      prefixTyped.app converted⟩
    have translated := TrExprS.app prefixTyped converted prefixTranslated majorTranslated
    have applicationConstructor : mkApp = Expr.app := rfl
    simpa only [Array.toList_append, Expr.mkAppList_append, Expr.mkAppList_eq_foldl,
      mkAppN, ← Array.foldl_toList, List.foldl_append, applicationConstructor] using translated


/-- Close the actual field arguments after comparison-based tail alignment. -/
theorem UArgModelEndpoint.recursiveValueFromInputOfEqvTail
    {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    {name : Name} {levels : List Level} {source : Expr}
    (input : RecursorConstantInput env universes final.vlctx name levels source)
    (envWF : env.WF) (stats : InductiveStats) (motives minors indices : Array Expr)
    {majorName : Name} {majorBody actualTail : Expr} {majorBinder : BinderInfo}
    (prefixArguments : NativeTelescopeArguments env universes final source
      (stats.params ++ motives ++ minors ++ indices).toList
      actualTail)
    (tailMatches : (actualTail == .forallE majorName terminal majorBody majorBinder) = true) :
    ∃ value valueType,
      TrExprS env universes initial.vlctx
        (finalReader.lctx.mkLambda arguments
          ((mkAppN (mkAppN (mkAppN (mkAppN (.const name levels) stats.params)
            motives) minors) indices).app (mkAppN argument arguments))) value ∧
      TrExprS env universes initial.vlctx
        (finalReader.lctx.mkForall arguments
          (majorBody.instantiate1' (mkAppN argument arguments))) valueType ∧
      env.HasType universes.length initial.vlctx.toCtx value valueType := by
  obtain ⟨_, _, translated, resultTranslated, typed⟩ := endpoint.recursiveCallFromInputOfEqvTail input envWF stats motives minors indices prefixArguments tailMatches
  obtain ⟨_, _, _, modelWF, native, _, ids, extension, selected⟩ := endpoint
  have arrays : arguments = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  obtain ⟨valueTranslated, valueTyped⟩ :=
    extension.typedValueAbstraction envWF modelWF translated typed
  have closed : (majorBody.instantiate1' (mkAppN argument arguments)).looseBVarRange' = 0 :=
    (final.noBV ▸ resultTranslated.closed).looseBVarRange_zero
  have resultBinding := extension.nativeBodyAbstraction modelWF closed
  have typeTranslated := (modelWF.mkForall_trS envWF resultTranslated
    (typed.isType envWF modelWF.tr.wf.toCtx) ids.length extension.bound).1
  rw [extension.drop_eq, ← resultBinding] at typeTranslated
  refine ⟨_, _, ?_, ?_, valueTyped⟩
  · simpa only [← native, arrays] using valueTranslated
  · simpa only [← native, arrays] using typeTranslated


set_option maxHeartbeats 800000 in
/-- A generated recursive value consumes the canonical stored-family tail.
Accepted family comparison supplies its alignment with the actual field;
no equality of native parameter syntax or complete call typing is assumed. -/
theorem UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromCanonicalTail
    {env before : VEnv} {models : List VConstVal} {safety : DefinitionSafety}
    {info : RecursorVal} {constant : VConstVal}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx}
    (endpoint : UArgModelEndpoint env info.levelParams opening initial final)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat) (full : LocalContext)
    (stored : info.type = (recursorRawType stats infos parent full).inferImplicit 1000 false)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF) (fullScope : full.BindingScope)
    (ids : List FVarId) (distinct : ids.Nodup)
    (shared : (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors)).toList =
      ids.map Expr.fvar)
    (agreement : SelectedCDeclBindingAgreement full final.lctx ids)
    (closed : (full.mkForall infos[parent]!.indices
      (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))).looseBVarRange' = 0)
    {majorName : Name} {majorBinder : BinderInfo}
    (accepted : isValidIndAppIdx stats terminal parent = true)
    (selectedParent : parent = (getIIndices stats terminal).1)
    (indices : NativeTelescopeArguments env info.levelParams final
      (full.mkForall infos[parent]!.indices
        (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive
          (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)) :
    ∃ value domain,
      TrExprS env info.levelParams initial.vlctx
        (finalReader.lctx.mkLambda arguments
          ((mkAppN (mkAppN (mkAppN (mkAppN
            (.const info.name (info.levelParams.map Level.param)) stats.params)
            (infos.map (·.motive))) (infos.flatMap (·.minors))) (getIIndices stats terminal).2).app
              (mkAppN argument arguments))) value ∧
      TrExprS env info.levelParams initial.vlctx
        (recursorIHDomain stats infos argument terminal arguments finalReader) domain ∧
      env.HasType info.levelParams.length initial.vlctx.toCtx value domain := by
  obtain ⟨input⟩ := recursorRawOriginalInputAfterInsertion signature stored member inserted
    envWF endpoint.context.1
  have shape := recursorRawType_sharedPrefix stats infos parent full final.lctx ids fullScope
    endpoint.context.1.bindingScope shared distinct agreement closed
  have prefixSupport := NativeTelescopeArguments.selectedPrefix envWF endpoint.context.1 ids
    distinct agreement.right closed indices
  rw [← shape, ← shared, ← Array.toList_append] at prefixSupport
  have prefixSupport' : NativeTelescopeArguments env info.levelParams final (recursorRawType stats infos parent full)
      (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors) ++ (getIIndices stats terminal).2).toList
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder) := by
    simpa only [Array.toList_append, List.append_assoc] using prefixSupport
  have compared := canonicalRecursorTail_matchesFieldTerminal accepted selectedParent infos majorName majorBinder
  obtain ⟨value, domain, translated, domainTranslated, typed⟩ :=
    @UArgModelEndpoint.recursiveValueFromInputOfEqvTail env info.levelParams argument terminal arguments
      reader finalReader opening initial final endpoint info.name (info.levelParams.map Level.param)
      (recursorRawType stats infos parent full) input envWF stats (infos.map (·.motive))
      (infos.flatMap (·.minors)) (getIIndices stats terminal).2 majorName
      (.app ((mkAppN infos[(getIIndices stats terminal).1]!.motive
        (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0))
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params) (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)
      majorBinder prefixSupport' compared
  refine ⟨value, domain, translated, ?_, typed⟩
  simpa only [recursorIHDomain, recursorIHBody, Expr.instantiate1',
    Expr.instantiate1'_liftLooseBVars_0, Nat.lt_irrefl, beq_self_eq_true,
    Bool.false_eq_true, if_false, if_true, Expr.liftLooseBVars_zero] using domainTranslated


end Lean4Lean.AddInductive
