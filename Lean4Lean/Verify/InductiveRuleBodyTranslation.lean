import Lean4Lean.Verify.InductiveRecursiveTailInputs
import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveParameterPrefixReplacement

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved TypedParameterApplications)

/-- A generated recursive value can be consumed by the actual annotation-peeled
IH binder recorded in one translated IH step.  The value and its native domain
are still supplied by the rule producer; this theorem only performs the
opening/domain conversion that the RHS consumer needs. -/
theorem IHModelStep.acceptsGeneratedValue
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {nativeValue : Expr} {valueSemantic domainSemantic : VExpr}
    (valueTranslated : TrExprS env universes initial.vlctx nativeValue valueSemantic)
    (domainTranslated : TrExprS env universes initial.vlctx domain domainSemantic)
    (valueTyped : env.HasType universes.length initial.vlctx.toCtx valueSemantic domainSemantic) :
    ∃ peeled, TrExprS env universes initial.vlctx nativeValue valueSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx valueSemantic peeled := by
  obtain ⟨terminal, arguments, argumentReader, opening, argumentModel, rawSemantic,
    peeled, level, domainEq, endpoint, ihOpening, finalEq, finalWF, finalNative⟩ := step
  refine ⟨peeled, valueTranslated, ?_⟩
  exact ihOpening.acceptsValue envWF initialWF domainTranslated valueTyped

/-- The preceding generated-value theorem can be fed directly to the actual
IH step.  This is the producer/consumer seam used by a constructor RHS: the
producer supplies the native recursive value and its domain, while the step
supplies the annotation-peeled binder expected by the minor. -/
theorem IHModelStep.acceptsGeneratedRecursiveValue
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {nativeValue : Expr}
    (generated : ∃ value domainSemantic,
      TrExprS env universes initial.vlctx nativeValue value ∧
      TrExprS env universes initial.vlctx domain domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx value domainSemantic) :
    ∃ peeled value, TrExprS env universes initial.vlctx nativeValue value ∧
      env.HasType universes.length initial.vlctx.toCtx value peeled := by
  obtain ⟨value, domainSemantic, valueTranslated, domainTranslated, valueTyped⟩ := generated
  obtain ⟨peeled, valueTranslated, valueTyped⟩ := step.acceptsGeneratedValue envWF initialWF
    valueTranslated domainTranslated valueTyped
  exact ⟨peeled, value, valueTranslated, valueTyped⟩

/-- Assemble a minor application once its actual peeled domain and all field/IH
arguments have been checked.  `TypedParameterApplications` retains each
argument translation and typing, so the result is the RHS application rather
than an assumed conversion. -/
theorem RecursorMinorOpening.applyArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {replacements : List Expr}
    {argumentSemantics : List VExpr} {resultSemantic : VExpr}
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (arguments : TypedParameterApplications env universes model peeled replacements
      argumentSemantics resultSemantic)
    (envWF : env.WF) (modelWF : model.WF env universes) :
    TrExprS env universes model.vlctx (minor.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments minorSemantic argumentSemantics) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic argumentSemantics) resultSemantic := by
  exact arguments.apply envWF modelWF minorTranslated minorTyped

/-- The native telescope proof used by a generated rule can be converted to the
peeled minor application without hiding the individual argument checks. -/
theorem RecursorMinorOpening.applyNativeArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (_opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {source : Expr} {replacements : List Expr}
    {terminal : Expr}
    (sourceTranslated : TrExprS env universes model.vlctx source peeled)
    (nativeArguments : NativeTelescopeArguments env universes model source replacements terminal)
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (modelWF : model.WF env universes) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes model peeled replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx (minor.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  obtain ⟨values, terminalSemantic, typedArguments, terminalTranslated⟩ :=
    nativeArguments.translated envWF modelWF sourceTranslated
  obtain ⟨appliedTranslated, appliedTyped⟩ :=
    (TypedParameterApplications.ofTypedArguments typedArguments).apply
      envWF modelWF minorTranslated minorTyped
  exact ⟨values, terminalSemantic, .ofTypedArguments typedArguments,
    appliedTranslated, appliedTyped⟩

/-- The common peeled-domain case uses the opening's own native translation;
the producer only supplies the checked native argument telescope. -/
theorem RecursorMinorOpening.applyNativePeeledArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx}
    {minor : Expr} {minorSemantic : VExpr} {replacements : List Expr} {terminal : Expr}
    (nativeArguments : NativeTelescopeArguments env universes model
      (peelTypeAnnotations domain) replacements terminal)
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (converted : model.vlctx = virtual) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes model peeled replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx (minor.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  exact opening.applyNativeArguments (by simpa only [converted] using opening.peeledTranslated)
    nativeArguments minorTranslated minorTyped envWF modelWF

/-- The composed field/IH receipt can be consumed directly by the peeled minor
application once the actual minor-domain source correspondence is supplied. -/
theorem RecursorMinorOpening.applyNativePeeledFieldAndIHArguments
    {env : VEnv} {universes : List Name} {reader : Context} {virtual : VLCtx}
    {parentName : Name} {constructor : Constructor} {domain : Expr}
    {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes reader virtual parentName constructor
      domain rawSemantic peeled level)
    {model : MLCtx} {fieldModel : MLCtx} {fields : Array Expr}
    {ihSource : Expr} {replacements : List Expr} {terminal : Expr}
    (nativeArguments : NativeTelescopeArguments env universes model
      (fieldModel.lctx.mkForall fields ihSource) replacements terminal)
    (sourceEq : peelTypeAnnotations domain = fieldModel.lctx.mkForall fields ihSource)
    (minorTranslated : TrExprS env universes model.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length model.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (converted : model.vlctx = virtual) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes model peeled replacements values terminalSemantic ∧
      TrExprS env universes model.vlctx (minor.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length model.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  exact opening.applyNativePeeledArguments (sourceEq.symm ▸ nativeArguments)
    minorTranslated minorTyped envWF modelWF converted

/-- Native argument receipts transport across a context extension without
changing the native telescope or replacement expressions. -/
theorem NativeTelescopeArguments.weakFV
    (arguments : NativeTelescopeArguments env universes model source replacements terminal)
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' model.vlctx target.vlctx 0 lift 0) :
    NativeTelescopeArguments env universes target source replacements terminal := by
  induction arguments with
  | nil => exact .nil
  | cons domainTranslated argumentTranslated argumentTyped remaining induction =>
    exact .cons (domainTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf)
      (argumentTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf)
      (argumentTyped.weak' envWF.ordered insertion.toCtx) induction

private theorem extensionCDecls {env : VEnv} {universes : List Name} {initial final : MLCtx}
    {ids : List FVarId} (extension : IndexMLCtxExtension initial ids final)
    (finalWF : final.WF env universes) :
    SelectedCDeclBindings final.lctx ids := by
  induction extension with
  | nil => intro id member; simp at member
  | @push ids model earlier id name domain semantic bi ih =>
    have modelWF := finalWF.1
    intro selected member
    rw [List.mem_append] at member
    rcases member with member | member
    · obtain ⟨index, name', domain', bi', kind', lookup⟩ := ih finalWF.1 selected member
      refine ⟨index, name', domain', bi', kind', ?_⟩
      have selectedPresent : selected ∈ model.vlctx.fvars := by
        have selectedPrefix := MLCtx.fvarRevList_prefix model (n := ids.length) (hn := earlier.bound)
        rw [earlier.selection] at selectedPrefix
        exact selectedPrefix.subset (List.mem_reverse.mpr member)
      have newAbsent : id ∉ model.vlctx.fvars := by
        have nodup := finalWF.fvars_nodup
        intro member
        exact (List.pairwise_cons.mp nodup).1 id member rfl
      have hne : id ≠ selected := by
        intro equality
        subst id
        exact newAbsent selectedPresent
      change (model.lctx.fvarIdToDecl.insert id _).find? selected = _
      rw [modelWF.tr.1.map_wf.find?_insert]
      simp only [beq_iff_eq, hne, ↓reduceIte]
      exact lookup
    · simp only [List.mem_singleton] at member
      subst selected
      refine ⟨model.length, name, domain, bi, .default, ?_⟩
      change (model.lctx.fvarIdToDecl.insert id _).find? id = _
      rw [modelWF.tr.1.map_wf.find?_insert]
      simp only [beq_self_eq_true, ↓reduceIte]
      simp only [modelWF.decls_size]

/-- The constructor-field trace supplies a checked native telescope for the
field fvars.  The body remains explicit so later IH arguments can be appended
after their actual dependent substitutions. -/
theorem CtorFieldModelEndpoint.nativeFieldArguments
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {source terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader finalReader : Context}
    {trace : RecursorCtorFieldTrace stats source 0 #[] #[] reader
      terminal finalIndex fields recursiveFields finalReader}
    {initial fieldModel : MLCtx} {semantic : VExpr}
    (endpoint : CtorFieldModelEndpoint env universes trace initial fieldModel semantic)
    (envWF : env.WF) {body : Expr} (bodyClosed : body.looseBVarRange' = 0) :
    NativeTelescopeArguments env universes fieldModel
      (fieldModel.lctx.mkForall fields body) fields.toList body := by
  obtain ⟨_, _, _, modelWF, _, _, ids, extension, selected⟩ := endpoint
  have distinct : ids.Nodup := by
    have selected := modelWF.fvarRevList_nodup ids.length extension.bound
    rw [extension.selection] at selected
    exact List.nodup_reverse.mp selected
  have bindings := extensionCDecls extension modelWF
  have selected' : fields = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using selected
  rw [selected']
  exact NativeTelescopeArguments.selected envWF modelWF ids distinct bindings bodyClosed

/-- A generated recursive value from one actual IH trace step is checked as an
argument of that step's annotation-peeled native domain.  The receipt is then
weakened through the step's real model extension; the remaining telescope is
left explicit for the caller's dependent IH sequence. -/
theorem IHModelStep.generatedNativeArgument
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    {nativeValue : Expr}
    (generated : ∃ value domainSemantic,
      TrExprS env universes initial.vlctx nativeValue value ∧
      TrExprS env universes initial.vlctx domain domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx value domainSemantic)
    {name : Name} {body : Expr} {binder : BinderInfo} {arguments : List Expr} {terminal : Expr}
    (remaining : NativeTelescopeArguments env universes final
      (body.instantiate1' nativeValue) arguments terminal) :
    NativeTelescopeArguments env universes final
      (.forallE name (peelTypeAnnotations domain) body binder)
      (nativeValue :: arguments) terminal := by
  obtain ⟨value, domainSemantic, valueTranslated, domainTranslated, generatedTyped⟩ := generated
  have extension := IHModelStep.extension step
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ihOpening, _, finalWF, _⟩ := step
  have valueTyped := ihOpening.acceptsValue envWF initialWF domainTranslated generatedTyped
  have insertion := extension.weakening.toFVLift'
  have domainTranslated := ihOpening.peeledTranslated.weakFV' envWF.ordered insertion finalWF.tr.wf
  have valueTranslated := valueTranslated.weakFV' envWF.ordered insertion finalWF.tr.wf
  have valueTyped := valueTyped.weak' envWF.ordered insertion.toCtx
  exact .cons domainTranslated valueTranslated valueTyped remaining

set_option maxHeartbeats 800000 in
/-- The canonical recursor-tail producer supplies the native recursive lambda
and its generated IH domain for one actual translated IH step.  The step's
source equation is used only to expose that domain under the source expression
recorded by the IH trace; no equality between the canonical call syntax and
the trace domain is inferred. -/
theorem IHModelStep.generatedCanonicalRecursiveValue
    {env before : VEnv} {models : List VConstVal} {safety : DefinitionSafety}
    {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final : MLCtx} (step : IHModelStep env universes source initial final)
    {info : RecursorVal} {constant : VConstVal}
    (universesEq : universes = info.levelParams)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (parent : Nat) (full : LocalContext)
    (stored : info.type = (recursorRawType stats infos parent full).inferImplicit 1000 false)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF) (fullScope : full.BindingScope)
    (ids : List FVarId) (distinct : ids.Nodup)
    (shared : (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors)).toList =
      ids.map Expr.fvar)
    (agreement : ∀ {argument terminal : Expr} {arguments : Array Expr}
      {reader finalReader : Context}
      {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
      {argumentModel : MLCtx},
      UArgModelEndpoint env info.levelParams opening initial argumentModel →
      SelectedCDeclBindingAgreement full argumentModel.lctx ids)
    (closed : (full.mkForall infos[parent]!.indices
      (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))).looseBVarRange' = 0)
    {majorName : Name} {majorBinder : BinderInfo}
    (accepted : ∀ terminal : Expr, isValidIndAppIdx stats terminal parent = true)
    (selectedParent : ∀ terminal : Expr, parent = (getIIndices stats terminal).1)
    (indices : ∀ {argumentModel : MLCtx} (terminal : Expr),
      NativeTelescopeArguments env info.levelParams argumentModel
      (full.mkForall infos[parent]!.indices
        (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params)
        (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive
          (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)) :
    ∃ nativeValue value domainSemantic,
      TrExprS env universes initial.vlctx nativeValue value ∧
      TrExprS env universes initial.vlctx domain domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx value domainSemantic := by
  subst universes
  obtain ⟨terminal, arguments, argumentReader, opening, argumentModel, rawSemantic,
    peeled, level, domainEq, endpoint, ihOpening, finalEq, finalWF, finalNative⟩ := step
  obtain ⟨value, domainSemantic, translated, domainTranslated, typed⟩ :=
    endpoint.recursiveValueInGeneratedIHDomainFromCanonicalTail signature stats infos parent full
      stored member inserted envWF fullScope ids distinct shared (agreement endpoint) closed
      (accepted terminal) (selectedParent terminal) (indices terminal)
  refine ⟨argumentReader.lctx.mkLambda arguments
      ((mkAppN (mkAppN (mkAppN (mkAppN (.const info.name
        (info.levelParams.map Level.param)) stats.params)
        (infos.map (·.motive))) (infos.flatMap (·.minors)))
        (getIIndices stats terminal).2).app (mkAppN argument arguments)),
    value, domainSemantic, translated, ?_, typed⟩
  simpa only [domainEq] using domainTranslated

/-- Explicit recursive IH source decomposition.  Every constructor records the
step-generated value, its semantic/domain receipts, and the dependent tail
substitution needed before the next IH binder is consumed. -/
inductive GeneratedIHNativeSuffix (env : VEnv) (universes : List Name)
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo} :
    {index : Nat} → {hypotheses : Array Expr} → {reader : Context}
    → {finalHypotheses : Array Expr} → {finalReader : Context}
    → {trace : RecursorIHTrace stats fields infos index hypotheses reader finalHypotheses finalReader}
    → {initial final : MLCtx}
    → TranslatedRecursorIHTrace env universes trace initial final
    → Expr → List Expr → Expr → Prop where
  | stop {index : Nat} {hypotheses : Array Expr} {reader : Context}
      {model : MLCtx} (complete : ¬ index < fields.size) (modelWF : model.WF env universes)
      (native : model.lctx = reader.lctx) {source terminal : Expr} (sourceEq : source = terminal) :
      GeneratedIHNativeSuffix env universes
        (trace := .stop (hypotheses := hypotheses) (reader := reader) complete)
        (initial := model) (final := model)
        (TranslatedRecursorIHTrace.stop complete modelWF native) source [] terminal
  | step {index : Nat} {hypotheses finalHypotheses : Array Expr} {reader finalReader : Context}
      {domain : Expr} {initial middle final : MLCtx}
      {source : RecursorIHDomainSource stats infos fields[index]! reader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (rest : TranslatedRecursorIHTrace env universes tail middle final)
      {nativeValue : Expr} {value domainSemantic : VExpr}
      (nativeTranslated : TrExprS env universes initial.vlctx nativeValue value)
      (domainTranslated : TrExprS env universes initial.vlctx domain domainSemantic)
      (valueTyped : env.HasType universes.length initial.vlctx.toCtx value domainSemantic)
      {name : Name} {body : Expr} {binder : BinderInfo} {arguments : List Expr} {terminal : Expr}
      {sourceExpr : Expr}
      (sourceEq : sourceExpr = .forallE name (peelTypeAnnotations domain) body binder)
      (tailWitness : GeneratedIHNativeSuffix env universes rest
        (body.instantiate1' nativeValue) arguments terminal) :
      GeneratedIHNativeSuffix env universes
        (trace := .step bound source tail) (initial := initial) (final := final)
        (TranslatedRecursorIHTrace.step bound source tail head rest)
        sourceExpr (nativeValue :: arguments) terminal

/-- A generated IH value can be checked in a later model by weakening the
step-local opening and value receipts through the actual intervening extension. -/
theorem IHModelStep.generatedNativeArgumentAtTarget
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial final target : MLCtx} (step : IHModelStep env universes source initial final)
    (envWF : env.WF) (initialWF : initial.WF env universes) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' final.vlctx target.vlctx 0 lift 0)
    {nativeValue : Expr}
    (generated : ∃ value domainSemantic,
      TrExprS env universes initial.vlctx nativeValue value ∧
      TrExprS env universes initial.vlctx domain domainSemantic ∧
      env.HasType universes.length initial.vlctx.toCtx value domainSemantic)
    {name : Name} {body : Expr} {binder : BinderInfo} {arguments : List Expr} {terminal : Expr}
    (remaining : NativeTelescopeArguments env universes target
      (body.instantiate1' nativeValue) arguments terminal) :
    NativeTelescopeArguments env universes target
      (.forallE name (peelTypeAnnotations domain) body binder)
      (nativeValue :: arguments) terminal := by
  obtain ⟨value, domainSemantic, valueTranslated, domainTranslated, generatedTyped⟩ := generated
  have extension := IHModelStep.extension step
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ihOpening, _, finalWF, _⟩ := step
  have valueTyped := ihOpening.acceptsValue envWF initialWF domainTranslated generatedTyped
  have stepInsertion := extension.weakening.toFVLift'
  have domainTranslated := ihOpening.peeledTranslated.weakFV' envWF.ordered stepInsertion finalWF.tr.wf
  have valueTranslated := valueTranslated.weakFV' envWF.ordered stepInsertion finalWF.tr.wf
  have valueTyped := valueTyped.weak' envWF.ordered stepInsertion.toCtx
  have domainTranslated := domainTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf
  have valueTranslated := valueTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf
  have valueTyped := valueTyped.weak' envWF.ordered insertion.toCtx
  exact .cons domainTranslated valueTranslated valueTyped remaining

/-- An indexed witness records the generated value and source substitution at
each actual translated IH step; it then yields the final native suffix receipt. -/
theorem GeneratedIHNativeSuffix.nativeArguments
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses : Array Expr} {suffixReader : Context}
    {finalHypotheses : Array Expr} {finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses suffixReader finalHypotheses finalReader}
    {initial final : MLCtx}
    {history : TranslatedRecursorIHTrace env universes trace initial final}
    {source : Expr} {replacements : List Expr} {terminal : Expr}
    (witness : GeneratedIHNativeSuffix env universes
      (trace := trace) (initial := initial) (final := final) history source replacements terminal)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (finalWF : final.WF env universes) :
    NativeTelescopeArguments env universes final source replacements terminal := by
  induction witness with
  | stop complete modelWF native sourceEq =>
    cases sourceEq
    exact .nil
  | step bound head rest nativeTranslated domainTranslated valueTyped sourceEq tailWitness tailInduction =>
    cases sourceEq
    obtain ⟨ids, extension, _⟩ := rest.extension
    exact head.generatedNativeArgumentAtTarget envWF initialWF finalWF
      extension.weakening.toFVLift'
      ⟨_, _, nativeTranslated, domainTranslated, valueTyped⟩
      (tailInduction head.context.1 finalWF)

/-- A completed generated suffix transports through the actual minor-opening
extension into a later model without changing its native source or values. -/
theorem GeneratedIHNativeSuffix.nativeArgumentsAtTarget
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses : Array Expr} {suffixReader : Context}
    {finalHypotheses : Array Expr} {finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses suffixReader finalHypotheses finalReader}
    {initial final target : MLCtx}
    {history : TranslatedRecursorIHTrace env universes trace initial final}
    {source : Expr} {replacements : List Expr} {terminal : Expr}
    (witness : GeneratedIHNativeSuffix env universes
      (trace := trace) (initial := initial) (final := final) history source replacements terminal)
    (envWF : env.WF) (initialWF : initial.WF env universes) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' final.vlctx target.vlctx 0 lift 0) :
    NativeTelescopeArguments env universes target source replacements terminal := by
  exact (witness.nativeArguments envWF initialWF history.context.1).weakFV
    envWF targetWF insertion

/-- Consume a completed generated IH suffix together with the checked
constructor-field prefix.  The source correspondence with the peeled minor
domain remains an explicit premise; this theorem only composes the two native
receipts and delegates the semantic application to the actual minor opening. -/
theorem GeneratedIHNativeSuffix.applyNativePeeledFieldAndIHArguments
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses : Array Expr} {suffixReader : Context}
    {finalHypotheses : Array Expr} {finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses suffixReader finalHypotheses finalReader}
    {initial final : MLCtx}
    {history : TranslatedRecursorIHTrace env universes trace initial final}
    {source : Expr} {replacements : List Expr} {terminal : Expr}
    (suffix : GeneratedIHNativeSuffix env universes
      (trace := trace) (initial := initial) (final := final) history source replacements terminal)
    {minorReader : Context} {virtual : VLCtx} {parentName : Name} {constructor : Constructor}
    {domain : Expr} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    {fieldModel : MLCtx} {minor : Expr} {minorSemantic : VExpr}
    {minorSource : Expr} {fieldArguments : List Expr}
    (fieldReceipt : NativeTelescopeArguments env universes final
      (fieldModel.lctx.mkForall fields minorSource) fieldArguments source)
    (sourceEq : peelTypeAnnotations domain = fieldModel.lctx.mkForall fields minorSource)
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (initialWF : initial.WF env universes)
    (finalWF : final.WF env universes) (converted : final.vlctx = virtual) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes final peeled
        (fieldArguments ++ replacements) values terminalSemantic ∧
      TrExprS env universes final.vlctx (minor.mkAppList (fieldArguments ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  have ihReceipt := suffix.nativeArguments envWF initialWF finalWF
  have composed := fieldReceipt.append ihReceipt
  exact opening.applyNativePeeledFieldAndIHArguments composed sourceEq minorTranslated minorTyped
    envWF finalWF converted

/-- A minor step transports the actual constructor-field prefix receipt from
the field model through the IH and minor context extensions.  The native body
is retained as an explicit expression for the subsequent generated IH values. -/
theorem MinorModelStep.nativeFieldArguments
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx} (step : MinorModelStep env universes parentName source initial final)
    (envWF : env.WF) {body : Expr} (bodyClosed : body.looseBVarRange' = 0) :
    ∃ (fieldModel : MLCtx) (fields : Array Expr),
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields body) fields.toList body := by
  obtain ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, finalWF, finalNative⟩ := step
  have fieldArgs := CtorFieldModelEndpoint.nativeFieldArguments endpoint envWF bodyClosed
  obtain ⟨hypothesisIds, hypothesisExtension, _⟩ := history.extension
  have extension : IndexMLCtxExtension fieldModel
      (hypothesisIds ++ [⟨domainReader.ngen.curr⟩]) final := by
    rw [finalEq]
    exact hypothesisExtension.trans (opening.extension hypothesisModel)
  exact ⟨fieldModel, fields, fieldArgs.weakFV envWF finalWF extension.weakening.toFVLift'⟩

/-- Compose the checked constructor-field prefix with the actual native IH suffix.
The suffix receipt carries the generated recursive replacements and their dependent
translations; only its source/terminal shape is abstracted here. -/
theorem MinorModelStep.nativeFieldAndIHArguments
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (envWF : env.WF) {ihSource : Expr} (ihSourceClosed : ihSource.looseBVarRange' = 0)
    {replacements : List Expr} {terminal : Expr}
    (ihSuffix : NativeTelescopeArguments env universes final ihSource replacements terminal) :
    ∃ (fieldModel : MLCtx) (fields : Array Expr),
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields ihSource)
        (fields.toList ++ replacements) terminal := by
  obtain ⟨terminalExpr, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, finalWF, finalNative⟩ := step
  have fieldArgs := CtorFieldModelEndpoint.nativeFieldArguments endpoint envWF ihSourceClosed
  obtain ⟨hypothesisIds, hypothesisExtension, _⟩ := history.extension
  have extension : IndexMLCtxExtension fieldModel
      (hypothesisIds ++ [⟨domainReader.ngen.curr⟩]) final := by
    rw [finalEq]
    exact hypothesisExtension.trans (opening.extension hypothesisModel)
  have fieldArgs := fieldArgs.weakFV envWF finalWF extension.weakening.toFVLift'
  exact ⟨fieldModel, fields, fieldArgs.append ihSuffix⟩

end Lean4Lean.AddInductive
