import Lean4Lean.Verify.InductiveRecursiveTailInputs
import Lean4Lean.Verify.InductiveGeneratedRuleResult
import Lean4Lean.Verify.InductiveMinorTranslationCPS
import Lean4Lean.Verify.InductiveParameterPrefixReplacement
import Lean4Lean.Verify.InductiveHeaderResidualKinds

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ContextReserved TypedParameterApplications)

theorem _root_.Lean4Lean.ElimNestedInductive.TypedParameterArguments.resultKind
    (arguments : ElimNestedInductive.TypedParameterArguments environment universes model
      source replacements values result)
    (environmentWF : environment.WF) (modelWF : model.WF environment universes)
    (kind : environment.SortArity universes.length model.vlctx.toCtx
      (count + replacements.length) source) :
    environment.SortArity universes.length model.vlctx.toCtx count result := by
  induction arguments with
  | nil => simpa only [List.length_nil, Nat.add_zero] using kind
  | cons translated typed remaining induction =>
    apply induction
    exact (VEnv.SortArity.forallBody
      (by simpa only [List.length_cons, Nat.add_assoc] using kind)
      environmentWF modelWF.tr.wf.toCtx).instN environmentWF.ordered .zero typed

theorem _root_.Lean4Lean.VEnv.SortArity.weak'
    {environment : VEnv} {universes count : Nat} {source target : List VExpr}
    {type : VExpr} {lift : Lift}
    (kind : environment.SortArity universes source count type)
    (ordered : environment.Ordered) (insertion : Ctx.Lift' lift source target) :
    environment.SortArity universes target count (type.lift' lift) := by
  induction kind generalizing lift target with
  | sort levelWF equality =>
    exact .sort levelWF (by simpa only [VExpr.lift'] using equality.weak' ordered insertion)
  | forallE domainTyped equality tail induction =>
    exact .forallE (domainTyped.weak' ordered insertion)
      (by simpa only [VExpr.lift'] using equality.weak' ordered insertion)
      (induction insertion.cons)

/- Apply a typed replacement telescope after moving its function and argument
   witnesses through an explicit base-to-target context insertion. -/
theorem _root_.Lean4Lean.ElimNestedInductive.TypedParameterArguments.applyWeakFV
    {env : VEnv} {universes : List Name} {base target : MLCtx}
    {native : Expr}
    {rhsSemantic rhsType : VExpr} {replacements : List Expr}
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (rhsTranslated : TrExprS env universes base.vlctx native rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    (envWF : env.WF)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    TrExprS env universes target.vlctx
      (native.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) := by
  have targetArguments := argumentTyping.weakFV envWF targetWF insertion
  exact targetArguments.apply
    (rhsTranslated.weakFV' envWF.ordered insertion targetWF.tr.wf)
    (rhsTyped.weak' envWF.ordered insertion.toCtx)

/- Add the terminal sort-arity transport to the target application consumer.
   The kind premise remains indexed by the produced RHS type. -/
theorem _root_.Lean4Lean.ElimNestedInductive.TypedParameterArguments.applyWeakFVKind
    {env : VEnv} {universes : List Name} {base target : MLCtx}
    {native : Expr}
    {rhsSemantic rhsType : VExpr} {replacements : List Expr}
    {arguments : List VExpr} {resultType : VExpr} {count : Nat}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (rhsTranslated : TrExprS env universes base.vlctx native rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    (envWF : env.WF)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    TrExprS env universes target.vlctx
      (native.mkAppList replacements)
      (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
        (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  obtain ⟨translated, typed⟩ := argumentTyping.applyWeakFV
    (native := native) rhsTranslated rhsTyped envWF targetWF insertion
  exact ⟨translated, typed,
    (argumentTyping.weakFV envWF targetWF insertion).resultKind envWF targetWF
      (kind.weak' envWF.ordered insertion.toCtx)⟩

/- Package the target application transport at the generated-rule boundary.
   The caller keeps the base RHS translation, typed replacement telescope,
   and context insertion explicit; this wrapper merely exposes the named
   target iota endpoint used by recursor consumers. -/
theorem GeneratedRecursorRuleIotaTargetResult.ofBaseApplication
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    {base target : MLCtx} {count : Nat} {arguments : List VExpr}
    {resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    GeneratedRecursorRuleIotaTargetResult env universes stats motives minors ctx constructor minor rule := by
  obtain ⟨translated, typed, resultKind⟩ := argumentTyping.applyWeakFVKind
    (native := rule.rhs) rhsTranslated rhsTyped envWF kind targetWF insertion
  exact ⟨target, count, arguments, resultType, insertionLift, replacements, rhsSemantic,
    translated, typed, resultKind⟩

/- Produce the paired base/target endpoint package from one typed replacement
   telescope.  The base side is applied in its original model context, while
   the target side is obtained by the explicit weak-FV transport above. -/
theorem GeneratedRecursorRuleIotaBaseAndTargetResults.ofBaseApplication
    {env : VEnv} {universes : List Name} {stats : InductiveStats}
    {motives minors : Array Expr} {ctx : Context} {constructor : Constructor}
    {minor : Expr} {rule : RecursorRule}
    {base target : MLCtx} {count : Nat} {arguments : List VExpr}
    {resultType : VExpr} {insertionLift : Lift} {replacements : List Expr}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    GeneratedRecursorRuleIotaBaseAndTargetResults env universes stats motives minors ctx constructor
      minor rule := by
  obtain ⟨baseTranslated, baseTyped⟩ := argumentTyping.apply rhsTranslated rhsTyped
  have baseKind := argumentTyping.resultKind envWF baseWF kind
  obtain ⟨targetTranslated, targetTyped, targetKind⟩ :=
    argumentTyping.applyWeakFVKind (native := rule.rhs) rhsTranslated rhsTyped envWF
      kind targetWF insertion
  exact ⟨base, target, count, arguments, resultType, insertionLift, replacements,
    rhsSemantic, rhsType, baseTranslated, baseTyped, baseKind, targetTranslated, targetTyped,
    targetKind⟩

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

private theorem peelTypeAnnotations_mkForall_selected {lctx : LocalContext} {body : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope) (closed : body.looseBVarRange' = 0)
    (peeled : peelTypeAnnotations body = body)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    peelTypeAnnotations (lctx.mkForall (ids.map Expr.fvar).toArray body) =
      lctx.mkForall (ids.map Expr.fvar).toArray body := by
  cases ids with
  | nil =>
    simp only [List.map_nil]
    change peelTypeAnnotations (lctx.mkForall #[] body) = lctx.mkForall #[] body
    simp only [LocalContext.mkForall, LocalContext.mkBinding, Array.size_empty,
      Nat.foldRev_zero, Expr.abstractRange_eq]
    have abstractEmpty : body.abstract #[] = body := by
      have h := Expr.abstract_eq body []
      simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil body 0)
    rw [abstractEmpty]
    exact peeled
  | cons identifier ids =>
    exact peelTypeAnnotations_mkForall_selected_nonempty _ scope closed
      (by simp [distinct]) bindings (by simp)

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

/-- The premises supplied by a rule producer for one canonical recursive IH.
They remain a record so suffix assembly can invoke the canonical producer
without collapsing its environment, family, source and argument obligations. -/
structure CanonicalRecursiveIHInput
    {env : VEnv} {universes : List Name} {stats : InductiveStats} {infos : Array RecInfo}
    {argument domain : Expr} {reader : Context}
    {source : RecursorIHDomainSource stats infos argument reader domain}
    {initial middle : MLCtx}
    (_head : IHModelStep env universes source initial middle) (sourceExpr : Expr) : Type where
  before : VEnv
  models : List VConstVal
  safety : DefinitionSafety
  info : RecursorVal
  constant : VConstVal
  universesEq : universes = info.levelParams
  signature : TrConstVal safety before (.recInfo info) constant
  parent : Nat
  full : LocalContext
  stored : info.type = (recursorRawType stats infos parent full).inferImplicit 1000 false
  member : constant ∈ models
  inserted : before.addConstructorHeaders models = some env
  fullScope : full.BindingScope
  ids : List FVarId
  distinct : ids.Nodup
  shared : (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors)).toList =
    ids.map Expr.fvar
  agreement : ∀ {argument terminal : Expr} {arguments : Array Expr}
    {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {argumentModel : MLCtx},
    UArgModelEndpoint env info.levelParams opening initial argumentModel →
    SelectedCDeclBindingAgreement full argumentModel.lctx ids
  closed : (full.mkForall infos[parent]!.indices
    (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))).looseBVarRange' = 0
  majorName : Name
  majorBinder : BinderInfo
  accepted : ∀ terminal : Expr, isValidIndAppIdx stats terminal parent = true
  selectedParent : ∀ terminal : Expr, parent = (getIIndices stats terminal).1
  indices : ∀ {argumentModel : MLCtx} (terminal : Expr),
    NativeTelescopeArguments env info.levelParams argumentModel
      (full.mkForall infos[parent]!.indices
        (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList
      (.forallE majorName (mkAppN (mkAppN stats.indConsts[parent]! stats.params)
        (getIIndices stats terminal).2)
        (.app ((mkAppN infos[parent]!.motive
          (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)
  name : Name
  body : Expr
  binder : BinderInfo
  sourceEq : sourceExpr = .forallE name (peelTypeAnnotations domain) body binder

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

set_option maxHeartbeats 800000 in
/-- Build the generated IH suffix recursively from a native forall shape.  The
shape carries the exact source telescope and terminal; each step generator
supplies the native recursive value, its semantic/domain receipts, and the
explicit peeled-binder source equation.  Instantiation of the shape supplies
the dependent source for the tail, so no structural equality between the
minor domain and the generated source is inferred here. -/
theorem GeneratedIHNativeSuffix.ofNativeForallTail
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses : Array Expr} {suffixReader : Context}
    {finalHypotheses : Array Expr} {finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses suffixReader finalHypotheses finalReader}
    {initial final : MLCtx}
    (history : TranslatedRecursorIHTrace env universes trace initial final)
    {source terminal : Expr} {count : Nat}
    (shape : NativeForallTail source count terminal)
    (countShape : count = fields.size - index)
    (generated : ∀ {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {reader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! reader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader}
      {initial middle final : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (rest : TranslatedRecursorIHTrace env universes tail middle final)
      (sourceExpr : Expr),
      ∃ nativeValue value domainSemantic name body binder,
        TrExprS env universes initial.vlctx nativeValue value ∧
        TrExprS env universes initial.vlctx domain domainSemantic ∧
        env.HasType universes.length initial.vlctx.toCtx value domainSemantic ∧
        sourceExpr = .forallE name (peelTypeAnnotations domain) body binder) :
    ∃ replacements terminal,
      GeneratedIHNativeSuffix env universes history source replacements terminal := by
  revert source count terminal
  induction history with
  | stop complete modelWF native =>
    intro source terminal count shape countShape
    have countZero : count = 0 := by omega
    cases shape with
    | nil =>
      refine ⟨[], _, .stop complete modelWF native rfl⟩
    | cons shape =>
      omega
  | @step idx hypotheses₁ finalHypotheses₁ reader₁ finalReader₁ domain₁ initial₁ middle₁ final₁
      bound sourceInfo tail head rest tailInduction =>
    intro source terminal count shape countShape
    obtain ⟨nativeValue, value, domainSemantic, name, body, binder,
      nativeTranslated, domainTranslated, valueTyped, sourceEq⟩ :=
      generated bound head rest source
    cases sourceEq
    cases shape with
    | @cons tailBody tailCount tailTerminal tailName tailDomain tailBinder shape =>
      have tailCountEq : tailCount = fields.size - (idx + 1) := by omega
      obtain ⟨arguments, terminal, tailWitness⟩ :=
        tailInduction (source := body.instantiate1' nativeValue)
          (shape := shape.instantiate1' nativeValue 0)
          tailCountEq
      refine ⟨nativeValue :: arguments, terminal, .step bound head rest
        nativeTranslated domainTranslated valueTyped rfl tailWitness⟩
    | nil =>
      omega

set_option maxHeartbeats 800000 in
/-- Assemble a generated IH suffix from canonical recursor-tail premises.
The producer record is instantiated at each actual translated IH step, and its
source equation is retained as the explicit peeled-binder obligation. -/
theorem GeneratedIHNativeSuffix.ofCanonicalForallTail
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {fields : Array Expr} {infos : Array RecInfo}
    {index : Nat} {hypotheses : Array Expr} {suffixReader : Context}
    {finalHypotheses : Array Expr} {finalReader : Context}
    {trace : RecursorIHTrace stats fields infos index hypotheses suffixReader finalHypotheses finalReader}
    {initial final : MLCtx}
    (history : TranslatedRecursorIHTrace env universes trace initial final)
    {source terminal : Expr} {count : Nat}
    (shape : NativeForallTail source count terminal)
    (countShape : count = fields.size - index)
    (envWF : env.WF)
    (canonical : ∀ {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {reader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! reader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨reader.ngen.curr⟩))
        (recursorIHContext reader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr) :
    ∃ replacements terminal,
      GeneratedIHNativeSuffix env universes history source replacements terminal := by
  apply GeneratedIHNativeSuffix.ofNativeForallTail history shape countShape
  intro index hypotheses finalHypotheses reader finalReader domain source tail initial middle final
    bound head rest sourceExpr
  obtain ⟨before, models, safety, info, constant, universesEq, signature, parent, full, stored,
    member, inserted, fullScope, ids, distinct, shared, agreement, closed, majorName, majorBinder,
    accepted, selectedParent, indices, name, body, binder, sourceEq⟩ :=
    canonical (index := index) (hypotheses := hypotheses) (finalHypotheses := finalHypotheses)
      (reader := reader) (finalReader := finalReader) (domain := domain) (source := source)
      (tail := tail) (initial := initial) (middle := middle) bound head sourceExpr
  obtain ⟨nativeValue, value, domainSemantic, valueTranslated, domainTranslated, valueTyped⟩ :=
    head.generatedCanonicalRecursiveValue universesEq signature parent full stored member inserted
      envWF fullScope ids distinct shared agreement closed accepted selectedParent indices
  exact ⟨nativeValue, value, domainSemantic, name, body, binder, valueTranslated, domainTranslated,
    valueTyped, sourceEq⟩

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

set_option maxHeartbeats 800000 in
/-- The peeled minor domain has the native field prefix followed by the native
IH telescope.  The two contexts remain explicit: field declarations are
looked up in the field reader, while IH declarations are looked up in the
later domain reader.  The closure and annotation-peeled body obligations are
therefore supplied by the caller rather than inferred from a structural
context equality. -/
theorem MinorModelStep.peeledDomainSource
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) := by
  obtain ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, finalWF, finalNative⟩ := step
  obtain ⟨fieldVirtual, terminalSemantic, fieldHistory, fieldWF, fieldNative,
    fieldConverted, fieldIds, fieldExtension, fieldSelected⟩ := endpoint
  obtain ⟨hypothesisIds, hypothesisExtension, hypothesisSelected⟩ := history.extension
  have fieldFrame := fieldHistory.scope reserved
  have hypothesisFrame := hypothesisTrace.scope fieldFrame.wf fieldFrame.reserved
  have fieldDistinct : fieldIds.Nodup := by
    have selected := fieldWF.fvarRevList_nodup fieldIds.length fieldExtension.bound
    rw [fieldExtension.selection] at selected
    exact List.nodup_reverse.mp selected
  have fieldBindingsModel := extensionCDecls fieldExtension fieldWF
  have fieldBindings : SelectedCDeclBindings fieldReader.lctx fieldIds := by
    simpa only [fieldNative] using fieldBindingsModel
  have fieldScope : fieldReader.lctx.BindingScope := by
    simpa only [fieldNative] using fieldWF.bindingScope
  have fieldAgreement : SelectedCDeclBindingAgreement fieldReader.lctx domainReader.lctx fieldIds :=
    fieldBindings.agreementAcross hypothesisFrame fieldFrame.wf
  have fieldArray : fields = (fieldIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using fieldSelected
  have hypothesisDeclared : RecursorFieldsDeclared domainReader.lctx hypotheses := by
    have declared : RecursorFieldsDeclared fieldReader.lctx #[] := by
      intro expression member
      simp only [Array.not_mem_empty] at member
    have declared := hypothesisTrace.declared declared
    simpa only [history.context.2.1] using declared
  have hypothesisWF : domainReader.lctx.WF := by
    simpa only [history.context.2.1] using history.context.1.tr.1
  have hypothesisScope : domainReader.lctx.BindingScope := by
    simpa only [history.context.2.1] using history.context.1.bindingScope
  have hypothesisDistinct : hypothesisIds.Nodup := by
    have selected := history.context.1.fvarRevList_nodup hypothesisIds.length hypothesisExtension.bound
    rw [hypothesisExtension.selection] at selected
    exact List.nodup_reverse.mp selected
  have hypothesisArray : hypotheses = (hypothesisIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray, Array.toList_empty, List.nil_append] using hypothesisSelected
  have hypothesisBindings : SelectedCDeclBindings domainReader.lctx hypothesisIds := by
    have bindings := hypothesisDeclared.selectedBindings hypothesisWF
    have idsArray : binderArrayIds (hypothesisIds.map Expr.fvar).toArray = hypothesisIds := by
      simp only [binderArrayIds, List.toList_toArray, List.map_map]
      change List.map (fun id => id) hypothesisIds = hypothesisIds
      exact List.map_id' hypothesisIds
    rw [← idsArray]
    simpa only [hypothesisArray] using bindings
  have bodyClosed' := bodyClosed terminal fields
  have bodyPeeled' := bodyPeeled terminal fields
  have innerClosed :
      (domainReader.lctx.mkForall hypotheses
        (recursorMinorBody stats infos constructor terminal fields)).looseBVarRange' = 0 := by
    rw [hypothesisArray]
    exact mkForall_selected_closed hypothesisIds hypothesisScope bodyClosed'
      hypothesisDistinct hypothesisBindings
  have innerPeeled :
      peelTypeAnnotations (domainReader.lctx.mkForall hypotheses
        (recursorMinorBody stats infos constructor terminal fields)) =
        domainReader.lctx.mkForall hypotheses
          (recursorMinorBody stats infos constructor terminal fields) := by
    rw [hypothesisArray]
    exact peelTypeAnnotations_mkForall_selected hypothesisIds hypothesisScope
      bodyClosed' bodyPeeled' hypothesisDistinct hypothesisBindings
  have outerEquality :
      domainReader.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) =
        fieldReader.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) := by
    rw [fieldArray]
    exact mkForall_congr_selected_cdecl fieldIds hypothesisScope fieldScope
      (fieldArray ▸ innerClosed) fieldDistinct (by
        intro id member
        obtain ⟨leftIndex, rightIndex, name, domain, bi, leftKind, rightKind,
          leftLookup, rightLookup⟩ := fieldAgreement id member
        exact ⟨rightIndex, leftIndex, name, domain, bi, rightKind, leftKind,
          rightLookup, leftLookup⟩)
  have outerPeeled :
      peelTypeAnnotations (domainReader.lctx.mkForall fields
        (domainReader.lctx.mkForall hypotheses
          (recursorMinorBody stats infos constructor terminal fields))) =
        domainReader.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) := by
    rw [fieldArray]
    exact peelTypeAnnotations_mkForall_selected fieldIds hypothesisScope
      (fieldArray ▸ innerClosed) (fieldArray ▸ innerPeeled)
      fieldDistinct fieldAgreement.right
  refine ⟨fieldModel, terminal, fields, hypotheses, ?_⟩
  rw [domainEq, recursorMinorDomain, outerPeeled, outerEquality, fieldNative]

set_option maxHeartbeats 1000000 in
/-- Build the generated IH argument receipt for one actual minor step.  The
canonical producer is instantiated at the translated IH history, then the
receipt is weakened through the real minor-opening extension. -/
theorem MinorModelStep.generatedNativeIHArguments
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr) :
    ∃ (hypotheses : Array Expr) (body : Expr) (replacements : List Expr) (terminal : Expr),
      NativeTelescopeArguments env universes final
        (domainReader.lctx.mkForall hypotheses body) replacements terminal := by
  obtain ⟨terminalExpr, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, finalWF, finalNative⟩ := step
  obtain ⟨fieldVirtual, fieldTerminalSemantic, fieldHistory, fieldWF, fieldNative,
    fieldConverted, fieldIds, fieldExtension, fieldSelected⟩ := endpoint
  obtain ⟨hypothesisIds, hypothesisExtension, hypothesisSelected⟩ := history.extension
  have fieldFrame := fieldHistory.scope reserved
  have hypothesisFrame := hypothesisTrace.scope fieldFrame.wf fieldFrame.reserved
  have hypothesisWF : domainReader.lctx.WF := by
    simpa only [history.context.2.1] using history.context.1.tr.1
  have hypothesisScope : domainReader.lctx.BindingScope := by
    simpa only [history.context.2.1] using history.context.1.bindingScope
  have hypothesisDeclared : RecursorFieldsDeclared domainReader.lctx hypotheses := by
    have declared : RecursorFieldsDeclared fieldReader.lctx #[] := by
      intro expression member
      simp only [Array.not_mem_empty] at member
    have declared := hypothesisTrace.declared declared
    simpa only [history.context.2.1] using declared
  have hypothesisDistinct : hypothesisIds.Nodup := by
    have selected := history.context.1.fvarRevList_nodup hypothesisIds.length hypothesisExtension.bound
    rw [hypothesisExtension.selection] at selected
    exact List.nodup_reverse.mp selected
  have hypothesisArray : hypotheses = (hypothesisIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray, Array.toList_empty, List.nil_append] using hypothesisSelected
  have hypothesisBindings : SelectedCDeclBindings domainReader.lctx hypothesisIds := by
    have bindings := hypothesisDeclared.selectedBindings hypothesisWF
    have idsArray : binderArrayIds (hypothesisIds.map Expr.fvar).toArray = hypothesisIds := by
      simp only [binderArrayIds, List.toList_toArray, List.map_map]
      change List.map (fun id => id) hypothesisIds = hypothesisIds
      exact List.map_id' hypothesisIds
    rw [← idsArray]
    simpa only [hypothesisArray] using bindings
  have hypothesisCount : hypotheses.size = recursiveFields.size := by
    have count := hypothesisTrace.counts
    simpa only [Array.size_empty, Nat.zero_add, Nat.sub_zero] using count
  have idsCount : hypothesisIds.length = recursiveFields.size := by
    have arrayCount := congrArg (fun array : Array Expr => array.toList.length) hypothesisArray
    have hypothesisLength : hypotheses.size = hypothesisIds.length := by
      simpa only [Array.length_toList, List.toList_toArray, List.length_map] using arrayCount
    exact hypothesisLength.symm.trans hypothesisCount
  let body := recursorMinorBody stats infos constructor terminalExpr fields
  have bodyClosed' : body.looseBVarRange' = 0 := bodyClosed terminalExpr fields
  have tail : NativeForallTail (domainReader.lctx.mkForall hypotheses body)
      hypothesisIds.length (body.abstractList hypothesisIds) := by
    rw [hypothesisArray]
    exact mkForall_selected_tail hypothesisIds hypothesisScope bodyClosed'
      hypothesisDistinct hypothesisBindings
  have suffixCount : hypothesisIds.length = recursiveFields.size - 0 := by simpa using idsCount
  obtain ⟨replacements, suffixTerminal, suffix⟩ :=
    GeneratedIHNativeSuffix.ofCanonicalForallTail history tail suffixCount envWF
      (fun {index} {hypotheses finalHypotheses suffixReader finalReader domain source tail initial middle}
        bound head sourceExpr =>
        canonical (fields := recursiveFields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
  have suffixAtTarget := suffix.nativeArgumentsAtTarget envWF fieldWF finalWF
    (by
      rw [finalEq]
      exact (opening.extension hypothesisModel).weakening.toFVLift')
  exact ⟨hypotheses, body, replacements, suffixTerminal, suffixAtTarget⟩

/- An ordinary translation of each generated minor body already supplies the
   closure premise needed by the recursive-IH telescope producer. Derive that
   premise from the final model's no-bound-variable invariant instead of
   making callers duplicate it alongside the semantic body witnesses. -/
theorem MinorModelStep.generatedNativeIHArgumentsOfTranslated
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyTranslated : ∀ terminal fields, ∃ bodySemantic,
      TrExpr env universes final.vlctx
        (recursorMinorBody stats infos constructor terminal fields) bodySemantic)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr) :
    ∃ (hypotheses : Array Expr) (body : Expr) (replacements : List Expr) (terminal : Expr),
      NativeTelescopeArguments env universes final
        (domainReader.lctx.mkForall hypotheses body) replacements terminal := by
  have bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0 := by
    intro terminal fields
    obtain ⟨bodySemantic, translated⟩ := bodyTranslated terminal fields
    exact (final.noBV ▸ translated.closed).looseBVarRange_zero
  apply MinorModelStep.generatedNativeIHArguments (step := step) (reserved := reserved)
    (bodyClosed := bodyClosed) (envWF := envWF)
  intro fields index hypotheses finalHypotheses suffixReader finalReader domain source tail
    initial middle bound head sourceExpr
  exact canonical (fields := fields) (index := index) (hypotheses := hypotheses)
    (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
    (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
    (initial := initial) (middle := middle) bound head sourceExpr

set_option maxHeartbeats 1400000 in
/-- The actual minor-step bridge: canonical recursive values are assembled into
the IH suffix, appended to the field receipt, and returned with the explicit
peeled-domain source equality needed by the minor application. -/
theorem MinorModelStep.generatedNativeFieldAndIHArguments
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (suffixTerminal : Expr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) suffixTerminal := by
  obtain ⟨terminal, finalIndex, fields, recursiveFields, fieldReader, hypotheses,
    fieldTrace, hypothesisTrace, semantic, fieldModel, hypothesisModel, rawSemantic,
    peeled, level, domainEq, endpoint, history, opening, finalEq, finalWF, finalNative⟩ := step
  let endpoint' := endpoint
  obtain ⟨fieldVirtual, terminalSemantic, fieldHistory, fieldWF, fieldNative,
    fieldConverted, fieldIds, fieldExtension, fieldSelected⟩ := endpoint
  obtain ⟨hypothesisIds, hypothesisExtension, hypothesisSelected⟩ := history.extension
  have fieldFrame := fieldHistory.scope reserved
  have hypothesisFrame := hypothesisTrace.scope fieldFrame.wf fieldFrame.reserved
  have fieldDistinct : fieldIds.Nodup := by
    have selected := fieldWF.fvarRevList_nodup fieldIds.length fieldExtension.bound
    rw [fieldExtension.selection] at selected
    exact List.nodup_reverse.mp selected
  have fieldBindingsModel := extensionCDecls fieldExtension fieldWF
  have fieldBindings : SelectedCDeclBindings fieldReader.lctx fieldIds := by
    simpa only [fieldNative] using fieldBindingsModel
  have fieldScope : fieldReader.lctx.BindingScope := by
    simpa only [fieldNative] using fieldWF.bindingScope
  have fieldAgreement : SelectedCDeclBindingAgreement fieldReader.lctx domainReader.lctx fieldIds :=
    fieldBindings.agreementAcross hypothesisFrame fieldFrame.wf
  have fieldArray : fields = (fieldIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using fieldSelected
  have hypothesisDeclared : RecursorFieldsDeclared domainReader.lctx hypotheses := by
    have declared : RecursorFieldsDeclared fieldReader.lctx #[] := by
      intro expression member
      simp only [Array.not_mem_empty] at member
    have declared := hypothesisTrace.declared declared
    simpa only [history.context.2.1] using declared
  have hypothesisWF : domainReader.lctx.WF := by
    simpa only [history.context.2.1] using history.context.1.tr.1
  have hypothesisScope : domainReader.lctx.BindingScope := by
    simpa only [history.context.2.1] using history.context.1.bindingScope
  have hypothesisDistinct : hypothesisIds.Nodup := by
    have selected := history.context.1.fvarRevList_nodup hypothesisIds.length hypothesisExtension.bound
    rw [hypothesisExtension.selection] at selected
    exact List.nodup_reverse.mp selected
  have hypothesisArray : hypotheses = (hypothesisIds.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray, Array.toList_empty, List.nil_append] using hypothesisSelected
  have hypothesisBindings : SelectedCDeclBindings domainReader.lctx hypothesisIds := by
    have bindings := hypothesisDeclared.selectedBindings hypothesisWF
    have idsArray : binderArrayIds (hypothesisIds.map Expr.fvar).toArray = hypothesisIds := by
      simp only [binderArrayIds, List.toList_toArray, List.map_map]
      change List.map (fun id => id) hypothesisIds = hypothesisIds
      exact List.map_id' hypothesisIds
    rw [← idsArray]
    simpa only [hypothesisArray] using bindings
  let body := recursorMinorBody stats infos constructor terminal fields
  have bodyClosed' : body.looseBVarRange' = 0 := bodyClosed terminal fields
  have bodyPeeled' : peelTypeAnnotations body = body := bodyPeeled terminal fields
  have innerClosed :
      (domainReader.lctx.mkForall hypotheses body).looseBVarRange' = 0 := by
    rw [hypothesisArray]
    exact mkForall_selected_closed hypothesisIds hypothesisScope bodyClosed'
      hypothesisDistinct hypothesisBindings
  have innerPeeled :
      peelTypeAnnotations (domainReader.lctx.mkForall hypotheses body) =
        domainReader.lctx.mkForall hypotheses body := by
    rw [hypothesisArray]
    exact peelTypeAnnotations_mkForall_selected hypothesisIds hypothesisScope
      bodyClosed' bodyPeeled' hypothesisDistinct hypothesisBindings
  have outerEquality :
      domainReader.lctx.mkForall fields (domainReader.lctx.mkForall hypotheses body) =
        fieldReader.lctx.mkForall fields (domainReader.lctx.mkForall hypotheses body) := by
    rw [fieldArray]
    exact mkForall_congr_selected_cdecl fieldIds hypothesisScope fieldScope
      (by simpa only [body] using innerClosed) fieldDistinct (by
        intro id member
        obtain ⟨leftIndex, rightIndex, name, domain', bi, leftKind, rightKind,
          leftLookup, rightLookup⟩ := fieldAgreement id member
        exact ⟨rightIndex, leftIndex, name, domain', bi, rightKind, leftKind,
          rightLookup, leftLookup⟩)
  have outerPeeled :
      peelTypeAnnotations (domainReader.lctx.mkForall fields
        (domainReader.lctx.mkForall hypotheses body)) =
        domainReader.lctx.mkForall fields (domainReader.lctx.mkForall hypotheses body) := by
    rw [fieldArray]
    exact peelTypeAnnotations_mkForall_selected fieldIds hypothesisScope
      (by simpa only [body] using innerClosed) (by simpa only [body] using innerPeeled)
      fieldDistinct fieldAgreement.right
  have sourceEq :
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields (domainReader.lctx.mkForall hypotheses body) := by
    rw [domainEq, recursorMinorDomain, outerPeeled, outerEquality, fieldNative]
  have hypothesisCount : hypotheses.size = recursiveFields.size := by
    have count := hypothesisTrace.counts
    simpa only [Array.size_empty, Nat.zero_add, Nat.sub_zero] using count
  have arrayCount := congrArg (fun array : Array Expr => array.toList.length) hypothesisArray
  have hypothesisLength : hypotheses.size = hypothesisIds.length := by
    simpa only [Array.length_toList, List.toList_toArray, List.length_map] using arrayCount
  have suffixShape : NativeForallTail (domainReader.lctx.mkForall hypotheses body)
      hypothesisIds.length (body.abstractList hypothesisIds) := by
    rw [hypothesisArray]
    exact mkForall_selected_tail hypothesisIds hypothesisScope bodyClosed'
      hypothesisDistinct hypothesisBindings
  have suffixCount : hypothesisIds.length = recursiveFields.size - 0 := by
    simpa [hypothesisLength] using hypothesisCount
  obtain ⟨replacements, suffixTerminal, suffix⟩ :=
    GeneratedIHNativeSuffix.ofCanonicalForallTail history suffixShape suffixCount envWF
      (fun {index} {hypotheses finalHypotheses suffixReader finalReader domain source tail initial middle}
        bound head sourceExpr =>
        canonical (fields := recursiveFields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
  have suffixAtTarget := suffix.nativeArgumentsAtTarget envWF fieldWF finalWF
    (by
      rw [finalEq]
      exact (opening.extension hypothesisModel).weakening.toFVLift')
  have fieldArgs := CtorFieldModelEndpoint.nativeFieldArguments endpoint' envWF innerClosed
  have extension : IndexMLCtxExtension fieldModel
      (hypothesisIds ++ [⟨domainReader.ngen.curr⟩]) final := by
    rw [finalEq]
    exact hypothesisExtension.trans (opening.extension hypothesisModel)
  have fieldArgs := fieldArgs.weakFV envWF finalWF extension.weakening.toFVLift'
  exact ⟨fieldModel, terminal, fields, hypotheses, replacements, suffixTerminal, sourceEq,
    fieldArgs.append suffixAtTarget⟩

/- The combined field/IH producer has the same closure premise. Derive it from
   ordinary translations while retaining the syntactic peeling and canonical
   recursive-IH obligations that cannot be inferred from translation alone. -/
theorem MinorModelStep.generatedNativeFieldAndIHArgumentsOfTranslated
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyTranslated : ∀ terminal fields, ∃ bodySemantic,
      TrExpr env universes final.vlctx
        (recursorMinorBody stats infos constructor terminal fields) bodySemantic)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (suffixTerminal : Expr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) suffixTerminal := by
  have bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0 := by
    intro terminal fields
    obtain ⟨bodySemantic, translated⟩ := bodyTranslated terminal fields
    exact (final.noBV ▸ translated.closed).looseBVarRange_zero
  apply MinorModelStep.generatedNativeFieldAndIHArguments (step := step)
    (reserved := reserved) (bodyClosed := bodyClosed) (bodyPeeled := bodyPeeled)
    (envWF := envWF)
  intro fields index hypotheses finalHypotheses suffixReader finalReader domain source tail
    initial middle bound head sourceExpr
  exact canonical (fields := fields) (index := index) (hypotheses := hypotheses)
    (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
    (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
    (initial := initial) (middle := middle) bound head sourceExpr


/-- Consume the generated field/IH receipt at the actual peeled minor.  The
minor opening, source equality, binder translation and final context conversion
are explicit inputs to this semantic application bridge. -/
theorem MinorModelStep.consumeGeneratedFieldAndIHArguments
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    {fieldModel : MLCtx} {fields : Array Expr} {ihSource : Expr}
    {replacements : List Expr} {terminal : Expr}
    (receipt : NativeTelescopeArguments env universes final
      (fieldModel.lctx.mkForall fields ihSource) (fields.toList ++ replacements) terminal)
    (sourceEq : peelTypeAnnotations domain = fieldModel.lctx.mkForall fields ihSource)
    {minor : Expr} {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (envWF : env.WF) (converted : final.vlctx = virtual) :
    ∃ values terminalSemantic,
      TypedParameterApplications env universes final peeled
        (fields.toList ++ replacements) values terminalSemantic ∧
      TrExprS env universes final.vlctx (minor.mkAppList (fields.toList ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) terminalSemantic := by
  have finalWF := step.context.1
  exact opening.applyNativePeeledFieldAndIHArguments receipt sourceEq minorTranslated minorTyped
    envWF finalWF converted

set_option maxHeartbeats 1400000 in
/-- Produce the semantic body application used by one constructor rule.  The
generated field/IH receipt is consumed at the actual peeled minor opening, and
the native application is exposed in the same nested `mkAppN` shape emitted by
`recursorRuleRhs`.  The replacement terminal and semantic result remain
explicit outputs, so this theorem is a consumer seam for the later lambda/iota
rule wrapper rather than an inferred RHS equality. -/
theorem MinorModelStep.generatedConstructorRhsBody
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minor : Expr} {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (replacementTerminal : Expr)
      (values : List VExpr) (resultSemantic : VExpr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) replacementTerminal ∧
      TypedParameterApplications env universes final peeled
        (fields.toList ++ replacements) values resultSemantic ∧
      TrExprS env universes final.vlctx
        (minor.mkAppList (fields.toList ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) resultSemantic ∧
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    sourceEq, nativeReceipt⟩ := step.generatedNativeFieldAndIHArguments reserved bodyClosed
      bodyPeeled envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
  obtain ⟨values, resultSemantic, typedArguments, applicationTranslated, applicationTyped⟩ :=
    step.consumeGeneratedFieldAndIHArguments opening nativeReceipt sourceEq minorTranslated
      minorTyped envWF converted
  refine ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal, values,
    resultSemantic, sourceEq, nativeReceipt, typedArguments, applicationTranslated,
    applicationTyped, ?_⟩
  have applicationShape :
      mkAppN (mkAppN minor fields) replacements.toArray =
        minor.mkAppList (fields.toList ++ replacements) := by
    have applicationConstructor : mkApp = Expr.app := rfl
    simp only [mkAppN, ← Array.foldl_toList, Expr.mkAppList_eq_foldl,
      List.foldl_append, applicationConstructor]
  rw [applicationShape]
  exact applicationTranslated

/- The constructor-body producer can derive the same closure premise from an
   ordinary translation of each generated minor body. The peeling equation and
   all semantic application obligations remain explicit. -/
theorem MinorModelStep.generatedConstructorRhsBodyOfTranslated
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyTranslated : ∀ terminal fields, ∃ bodySemantic,
      TrExpr env universes final.vlctx
        (recursorMinorBody stats infos constructor terminal fields) bodySemantic)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minor : Expr} {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (replacementTerminal : Expr)
      (values : List VExpr) (resultSemantic : VExpr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) replacementTerminal ∧
      TypedParameterApplications env universes final peeled
        (fields.toList ++ replacements) values resultSemantic ∧
      TrExprS env universes final.vlctx
        (minor.mkAppList (fields.toList ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) resultSemantic ∧
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) := by
  have bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0 := by
    intro terminal fields
    obtain ⟨bodySemantic, translated⟩ := bodyTranslated terminal fields
    exact (final.noBV ▸ translated.closed).looseBVarRange_zero
  exact step.generatedConstructorRhsBody opening reserved bodyClosed bodyPeeled envWF
    (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
        {source} {tail} {initial middle} bound head sourceExpr =>
      canonical (fields := fields) (index := index) (hypotheses := hypotheses)
        (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
        (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
        (initial := initial) (middle := middle) bound head sourceExpr)
    minorTranslated minorTyped converted

/-- Abstract a checked constructor-rule body through the caller's actual
context extension.  The native RHS shape is an explicit premise, so this
consumer can be instantiated with a `RecursorRuleRhsReceipt` without guessing
which declarations belong to its lambda wrapper. -/
theorem MinorModelStep.abstractConstructorRhsBody
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minor : Expr} {fields : Array Expr} {replacements : List Expr} {rhs : Expr}
    {bodySemantic bodyType : VExpr}
    (rhsShape : rhs = final.lctx.mkLambda (ids.map Expr.fvar).toArray
      (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) :
    ∃ value valueType,
      TrExprS env universes base.vlctx rhs value ∧
      env.HasType universes.length base.vlctx.toCtx value valueType := by
  obtain ⟨valueTranslated, valueTyped⟩ := extension.typedValueAbstraction envWF
    step.context.1 bodyTranslated bodyTyped
  refine ⟨_, _, ?_, valueTyped⟩
  simpa only [rhsShape] using valueTranslated

/-- Consume the generated body at an actual constructor-rule receipt.  The
native receipt remains available in the result, while the replacement-array
and lambda-wrapper equalities are explicit premises for the final iota shape.
No correspondence between the generated list and the stored rule arguments is
inferred. -/
theorem MinorModelStep.abstractConstructorRuleRhs
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) :
    ∃ value valueType,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx rule.rhs value ∧
      env.HasType universes.length base.vlctx.toCtx value valueType := by
  obtain ⟨receiptFields, receiptValues, current, hframe, hconstructor, hcount, hrhs⟩ := receipt
  obtain ⟨fieldsEq, valuesEq, rhsShape⟩ :=
    receiptShape receiptFields receiptValues current hframe hconstructor hcount
  have rhsShape' : rule.rhs = final.lctx.mkLambda (ids.map Expr.fvar).toArray
      (mkAppN (mkAppN minor fields) replacements.toArray) := by
    calc
      rule.rhs = recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor := hrhs
      _ = final.lctx.mkLambda (ids.map Expr.fvar).toArray
          (mkAppN (mkAppN minor fields) replacements.toArray) := by
        simpa only [fieldsEq, valuesEq] using rhsShape
  obtain ⟨value, valueType, valueTranslated, valueTyped⟩ :=
    step.abstractConstructorRhsBody extension rhsShape' bodyTranslated bodyTyped envWF
  exact ⟨value, valueType, ⟨receiptFields, receiptValues, current, hframe, hconstructor, hcount, hrhs⟩,
    valueTranslated, valueTyped⟩

/-- Apply a checked constructor RHS through the actual typed replacement
telescope.  This is the iota consumer for the rule receipt: each native
replacement and semantic argument remains recorded by
`TypedParameterArguments`, and the terminal semantic type is returned rather
than reconstructed from the RHS shape. -/
theorem RecursorRuleRhsReceipt.applyIota
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {base : MLCtx} {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType := by
  obtain ⟨translated, typed⟩ := argumentTyping.apply rhsTranslated rhsTyped
  exact ⟨receipt, translated, typed⟩

/-- Carry a sort-arity witness through the constructor RHS iota consumer.  The
typed replacement telescope remains explicit, and the result kind is derived
from its dependent argument premises rather than reconstructed from syntax. -/
theorem RecursorRuleRhsReceipt.applyIotaKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {base : MLCtx} {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (modelWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType := by
  obtain ⟨receipt, translated, typed⟩ := receipt.applyIota rhsTranslated rhsTyped argumentTyping
  exact ⟨receipt, translated, typed, argumentTyping.resultKind envWF modelWF kind⟩

/-- Transport a checked constructor RHS iota result through an explicit model
context extension.  Native replacements stay unchanged while every semantic
argument, the RHS type, and the terminal type are lifted by the supplied
`VLCtx.FVLift'`; no context or argument correspondence is inferred. -/
theorem RecursorRuleRhsReceipt.applyIotaWeakFV
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) (resultType.lift' insertionLift) := by
  obtain ⟨translated, typed⟩ := argumentTyping.applyWeakFV
    (native := rule.rhs) rhsTranslated rhsTyped envWF targetWF insertion
  exact ⟨receipt, translated, typed⟩

/-- Transport the checked constructor RHS iota kind through an explicit
model-context extension.  The native replacement telescope is unchanged;
semantic arguments, the terminal type, and its sort-arity witness are lifted
by the caller-supplied insertion. -/
theorem RecursorRuleRhsReceipt.applyIotaWeakFVKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count (resultType.lift' insertionLift) := by
  obtain ⟨translated, typed, resultKind⟩ :=
    ElimNestedInductive.TypedParameterArguments.applyWeakFVKind argumentTyping
    (native := rule.rhs) rhsTranslated rhsTyped envWF
    kind targetWF insertion
  exact ⟨receipt, translated, typed, resultKind⟩

/- Compose the base-context iota/kind receipt with its target-context weak-FV
   transport.  Keeping both applications in one result lets a recursor-level
   consumer retain the exact base semantic before insertion as well as the
   lifted semantic after insertion. -/
theorem RecursorRuleRhsReceipt.applyIotaKindWeakFVKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  obtain ⟨baseReceipt, baseTranslated, baseTyped, baseKind⟩ := receipt.applyIotaKind
    rhsTranslated rhsTyped argumentTyping envWF baseWF kind
  obtain ⟨targetReceipt, targetTranslated, targetTyped, targetKind⟩ :=
    baseReceipt.applyIotaWeakFVKind rhsTranslated rhsTyped argumentTyping envWF targetWF
      insertion kind
  exact ⟨baseReceipt, baseTranslated, baseTyped, baseKind, targetTranslated, targetTyped,
    targetKind⟩

/- The count receipt has the same result transport once its native field/count
   witnesses are projected through the ordinary rule receipt. -/
theorem RecursorRuleRhsCountReceipt.applyIotaKindWeakFVKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (countReceipt : RecursorRuleRhsCountReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  exact countReceipt.receipt.applyIotaKindWeakFVKind rhsTranslated rhsTyped argumentTyping
    envWF baseWF kind targetWF insertion

/- The fvar receipt preserves the same consumer contract while making its
   count projection explicit. -/
theorem RecursorRuleRhsFVarReceipt.applyIotaKindWeakFVKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (fvarReceipt : RecursorRuleRhsFVarReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  exact fvarReceipt.counts.applyIotaKindWeakFVKind rhsTranslated rhsTyped argumentTyping
    envWF baseWF kind targetWF insertion

/- The checked scoped receipt has the same result transport once its
   declaration-scope witnesses are projected through the named fvar/count
   adapters.  Keep this adapter at the scoped boundary so callers that retain
   the stronger receipt need not repeat that projection. -/
theorem RecursorRuleRhsScopeReceipt.applyIotaKindWeakFVKind
    {env : VEnv} {universes : List Name}
    {stats : InductiveStats} {motives minors : Array Expr}
    {ctx : Context} {constructor : Constructor} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {base target : MLCtx} {insertionLift : Lift}
    {rhsSemantic rhsType : VExpr}
    (rhsTranslated : TrExprS env universes base.vlctx rule.rhs rhsSemantic)
    (rhsTyped : env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType)
    {replacements : List Expr} {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ElimNestedInductive.TypedParameterArguments env universes base rhsType
      replacements arguments resultType)
    (envWF : env.WF) (baseWF : base.WF env universes)
    (kind : env.SortArity universes.length base.vlctx.toCtx
      (count + replacements.length) rhsType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments rhsSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift))) ∧
      env.HasType universes.length target.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments (rhsSemantic.lift' insertionLift)
          (arguments.map (VExpr.lift' · insertionLift)))
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  exact scopeReceipt.fvars.applyIotaKindWeakFVKind rhsTranslated rhsTyped
    argumentTyping envWF baseWF kind targetWF insertion

/-- Compose the checked constructor-rule body with the typed replacement
telescope.  The caller supplies the telescope for the value produced by the
rule bridge; this keeps the RHS type, replacement list, semantic arguments,
and terminal type coupled without reconstructing any of them from syntax. -/
theorem MinorModelStep.abstractConstructorRuleRhsIota
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF)
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType) :
    ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments resultSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments resultSemantic arguments) resultType := by
  obtain ⟨value, valueType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs receipt extension receiptShape bodyTranslated bodyTyped envWF
  obtain ⟨ruleReceipt, appliedTranslated, appliedTyped⟩ :=
    ruleReceipt.applyIota rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped)
  exact ⟨value, ruleReceipt, appliedTranslated, appliedTyped⟩

/-- Compose the checked constructor-rule body with the typed replacement
telescope while carrying an explicit sort-arity witness for the terminal type.
The kind premise is indexed by the produced RHS type, so no type equality is
reconstructed from the native rule shape. -/
theorem MinorModelStep.abstractConstructorRuleRhsIotaKind
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) (modelWF : base.WF env universes)
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType) :
    ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx (rule.rhs.mkAppList replacements)
        (ElimNestedInductive.applyParameterArguments resultSemantic arguments) ∧
      env.HasType universes.length base.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments resultSemantic arguments) resultType ∧
      env.SortArity universes.length base.vlctx.toCtx count resultType := by
  obtain ⟨value, valueType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs receipt extension receiptShape bodyTranslated bodyTyped envWF
  obtain ⟨ruleReceipt, appliedTranslated, appliedTyped, resultKind⟩ :=
    ruleReceipt.applyIotaKind rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped) envWF modelWF (kind rhsTranslated rhsTyped)
  exact ⟨value, ruleReceipt, appliedTranslated, appliedTyped, resultKind⟩

/-- Transport the complete constructor-rule iota result through an explicit
model-context extension.  The body bridge and argument telescope stay
caller-supplied; only the semantic result and terminal type are lifted. -/
theorem MinorModelStep.abstractConstructorRuleRhsIotaWeakFV
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) {insertionLift : Lift}
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic (resultType.lift' insertionLift) := by
  obtain ⟨value, valueType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs receipt extension receiptShape bodyTranslated bodyTyped envWF
  obtain ⟨ruleReceipt, appliedTranslated, appliedTyped⟩ :=
    ruleReceipt.applyIotaWeakFV rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped) envWF targetWF insertion
  exact ⟨_, ruleReceipt, appliedTranslated, appliedTyped⟩

/-- Transport the complete constructor-rule iota result and its sort-arity
witness through an explicit model-context extension.  The body bridge,
replacement telescope, and base-context kind remain caller-supplied. -/
theorem MinorModelStep.abstractConstructorRuleRhsIotaWeakFVKind
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) {insertionLift : Lift}
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count (resultType.lift' insertionLift) := by
  obtain ⟨value, valueType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs receipt extension receiptShape bodyTranslated bodyTyped envWF
  obtain ⟨ruleReceipt, appliedTranslated, appliedTyped, resultKind⟩ :=
    ruleReceipt.applyIotaWeakFVKind rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped) envWF targetWF insertion (kind rhsTranslated rhsTyped)
  exact ⟨_, ruleReceipt, appliedTranslated, appliedTyped, resultKind⟩

/- Consume the scoped receipt emitted by the checked recursor pass.  Its
   fvar/count projections are the only conversion needed before invoking the
   complete weak-FV/kind bridge above; all body, telescope, typing, terminal,
   and context-extension premises stay explicit at this boundary. -/
theorem MinorModelStep.abstractScopedConstructorRuleRhsIotaWeakFVKind
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {fields : Array Expr} {replacements : List Expr} {bodySemantic bodyType : VExpr}
    (receiptShape : ∀ (receiptFields receiptValues : Array Expr) (current : Context),
      ctx.HeaderFrame current → rule.ctor = constructor.name →
      rule.nfields = receiptFields.size →
      ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
        recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
          final.lctx.mkLambda (ids.map Expr.fvar).toArray
            (mkAppN (mkAppN minor fields) replacements.toArray))
    (bodyTranslated : TrExprS env universes final.vlctx
      (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic)
    (bodyTyped : env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType)
    (envWF : env.WF) {insertionLift : Lift}
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (targetWF : target.WF env universes)
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count (resultType.lift' insertionLift) := by
  exact step.abstractConstructorRuleRhsIotaWeakFVKind scopeReceipt.fvars.counts.receipt
    extension receiptShape bodyTranslated bodyTyped envWF argumentTyping kind targetWF insertion

/- Consume the generated minor body at the scoped constructor-rule receipt.  The
   body producer supplies the actual fields, recursive replacements, semantic
   application, and typing; only the native rule shape, replacement telescope,
   kind witness, and target insertion remain caller-supplied. -/
theorem MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKind
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual)
    (receiptShape : ∀ {fields : Array Expr} {replacements : List Expr}
      {bodySemantic bodyType : VExpr},
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic →
      env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType →
      ∀ (receiptFields receiptValues : Array Expr) (current : Context),
        ctx.HeaderFrame current → rule.ctor = constructor.name →
        rule.nfields = receiptFields.size →
        ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
          recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
            final.lctx.mkLambda (ids.map Expr.fvar).toArray
              (mkAppN (mkAppN minor fields) replacements.toArray))
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ replacements : List Expr, ∃ resultSemantic,
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count (resultType.lift' insertionLift) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    values, bodySemantic, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated⟩ := step.generatedConstructorRhsBody opening reserved bodyClosed bodyPeeled
      envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
      minorTranslated minorTyped converted
  have receiptShape' := receiptShape nestedTranslated bodyTyped
  have argumentTyping' : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType := by
    intro value valueType valueTranslated valueTyped
    exact argumentTyping valueTranslated valueTyped
  have kind' : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType := by
    intro value valueType valueTranslated valueTyped
    exact kind valueTranslated valueTyped
  obtain ⟨resultSemantic, ruleReceipt, resultTranslated, resultTyped, resultKind⟩ :=
    step.abstractScopedConstructorRuleRhsIotaWeakFVKind scopeReceipt extension receiptShape'
      nestedTranslated bodyTyped envWF argumentTyping' kind' targetWF insertion
  exact ⟨replacements, resultSemantic, ruleReceipt, resultTranslated, resultTyped, resultKind⟩

/- A per-rule consumer that keeps the generated body witness alongside the
   final RHS result.  The shorter bridge above is convenient when only the
   applied rule is needed; this form is the boundary for later recursor
   semantics, where the actual field/IH values and their typed application
   must remain available rather than being reconstructed from the result. -/
theorem MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBody
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual)
    (receiptShape : ∀ {fields : Array Expr} {replacements : List Expr}
      {bodySemantic bodyType : VExpr},
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic →
      env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType →
      ∀ (receiptFields receiptValues : Array Expr) (current : Context),
        ctx.HeaderFrame current → rule.ctor = constructor.name →
        rule.nfields = receiptFields.size →
        ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
          recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
            final.lctx.mkLambda (ids.map Expr.fvar).toArray
              (mkAppN (mkAppN minor fields) replacements.toArray))
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (replacementTerminal : Expr)
      (values : List VExpr) (bodySemantic resultSemantic : VExpr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) replacementTerminal ∧
      TypedParameterApplications env universes final peeled
        (fields.toList ++ replacements) values bodySemantic ∧
      TrExprS env universes final.vlctx
        (minor.mkAppList (fields.toList ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) bodySemantic ∧
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    values, bodySemantic, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated⟩ := step.generatedConstructorRhsBody opening reserved bodyClosed bodyPeeled
      envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
      minorTranslated minorTyped converted
  have receiptShape' := receiptShape nestedTranslated bodyTyped
  have argumentTyping' : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType := by
    intro value valueType valueTranslated valueTyped
    exact argumentTyping valueTranslated valueTyped
  have kind' : ∀ {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType := by
    intro value valueType valueTranslated valueTyped
    exact kind valueTranslated valueTyped
  obtain ⟨resultSemantic, ruleReceipt, resultTranslated, resultTyped, resultKind⟩ :=
    step.abstractScopedConstructorRuleRhsIotaWeakFVKind scopeReceipt extension receiptShape'
      nestedTranslated bodyTyped envWF argumentTyping' kind' targetWF insertion
  exact ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal, values,
    bodySemantic, resultSemantic, sourceEq, nativeReceipt, typedArguments, bodyTranslated,
    bodyTyped, nestedTranslated, ruleReceipt, resultTranslated, resultTyped, resultKind⟩

/- The recursor-level rule consumer also needs the translation of the
   unapplied native rule body.  Recover it from the retained generated-body
   witness before iota application, and retain its type and kind explicitly;
   no source-RHS equality or recursive-value premise is reconstructed here. -/
theorem MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSource
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual)
    (receiptShape : ∀ {fields : Array Expr} {replacements : List Expr}
      {bodySemantic bodyType : VExpr},
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic →
      env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType →
      ∀ (receiptFields receiptValues : Array Expr) (current : Context),
        ctx.HeaderFrame current → rule.ctor = constructor.name →
        rule.nfields = receiptFields.size →
        ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
          recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
            final.lctx.mkLambda (ids.map Expr.fvar).toArray
              (mkAppN (mkAppN minor fields) replacements.toArray))
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    ∃ (fieldModel : MLCtx) (terminal : Expr) (fields hypotheses : Array Expr)
      (replacements : List Expr) (replacementTerminal : Expr)
      (values : List VExpr) (bodySemantic rhsSemantic rhsType resultSemantic : VExpr),
      peelTypeAnnotations domain =
        fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)) ∧
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields
          (domainReader.lctx.mkForall hypotheses
            (recursorMinorBody stats infos constructor terminal fields)))
        (fields.toList ++ replacements) replacementTerminal ∧
      TypedParameterApplications env universes final peeled
        (fields.toList ++ replacements) values bodySemantic ∧
      TrExprS env universes final.vlctx
        (minor.mkAppList (fields.toList ++ replacements))
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      env.HasType universes.length final.vlctx.toCtx
        (ElimNestedInductive.applyParameterArguments minorSemantic values) bodySemantic ∧
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray)
        (ElimNestedInductive.applyParameterArguments minorSemantic values) ∧
      RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule ∧
      TrExprS env universes base.vlctx rule.rhs rhsSemantic ∧
      env.HasType universes.length base.vlctx.toCtx rhsSemantic rhsType ∧
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) rhsType ∧
      TrExprS env universes target.vlctx (rule.rhs.mkAppList replacements) resultSemantic ∧
      env.HasType universes.length target.vlctx.toCtx resultSemantic
        (resultType.lift' insertionLift) ∧
      env.SortArity universes.length target.vlctx.toCtx count
        (resultType.lift' insertionLift) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    values, bodySemantic, resultSemantic, sourceEq, nativeReceipt, typedArguments,
    bodyTranslated, bodyTyped, nestedTranslated, ruleReceipt, resultTranslated, resultTyped,
    resultKind⟩ := step.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBody scopeReceipt
      extension opening reserved bodyClosed bodyPeeled envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
      minorTranslated minorTyped
      converted receiptShape argumentTyping kind targetWF insertion
  have receiptShape' := receiptShape nestedTranslated bodyTyped
  obtain ⟨rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs scopeReceipt.fvars.counts.receipt extension receiptShape'
      nestedTranslated bodyTyped
      envWF
  exact ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal, values,
    bodySemantic, rhsSemantic, rhsType, resultSemantic, sourceEq, nativeReceipt, typedArguments,
    bodyTranslated, bodyTyped, nestedTranslated, ruleReceipt, rhsTranslated, rhsTyped,
    kind rhsTranslated rhsTyped, resultTranslated, resultTyped, resultKind⟩

/- Retain the semantic value produced by the typed replacement telescope.
   This is the final shape needed by a recursor-level consumer: both the base
   and lifted applied RHS translations are exposed as exact
   `applyParameterArguments` expressions, rather than only as existential
   result semantics. -/
theorem MinorModelStep.generatedScopedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (scopeReceipt : RecursorRuleRhsScopeReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual)
    (receiptShape : ∀ {fields : Array Expr} {replacements : List Expr}
      {bodySemantic bodyType : VExpr},
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic →
      env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType →
      ∀ (receiptFields receiptValues : Array Expr) (current : Context),
        ctx.HeaderFrame current → rule.ctor = constructor.name →
        rule.nfields = receiptFields.size →
        ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
          recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
            final.lctx.mkLambda (ids.map Expr.fvar).toArray
              (mkAppN (mkAppN minor fields) replacements.toArray))
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (baseWF : base.WF env universes)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
      (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
      (constructor := constructor) (minor := minor) (rule := rule) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    values, bodySemantic, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated⟩ := step.generatedConstructorRhsBody opening reserved bodyClosed bodyPeeled
      envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
      minorTranslated minorTyped converted
  have receiptShape' := receiptShape nestedTranslated bodyTyped
  obtain ⟨rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs scopeReceipt.fvars.counts.receipt extension receiptShape'
      nestedTranslated bodyTyped
      envWF
  obtain ⟨ruleReceipt, baseResultTranslated, baseResultTyped, baseResultKind,
    resultTranslated, resultTyped, resultKind⟩ :=
    scopeReceipt.applyIotaKindWeakFVKind rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped) envWF baseWF (kind rhsTranslated rhsTyped)
      targetWF insertion
  exact ⟨infos, domainReader, domain, ids, final, base, target, count, arguments, resultType,
    insertionLift, peeled, minorSemantic, fieldModel, terminal, fields, hypotheses,
    replacements, replacementTerminal, values, bodySemantic, rhsSemantic, rhsType,
    extension, insertion, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated, ruleReceipt, rhsTranslated, rhsTyped, kind rhsTranslated rhsTyped,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated, resultTyped,
    resultKind⟩

/-- Consume the generated constructor body at an ordinary recursor-rule
receipt.  This is the recursor-level result seam: callers that have already
migrated from scoped field receipts retain the generated body/source witnesses
and obtain both the base and lifted applied RHS semantics explicitly. -/
theorem MinorModelStep.generatedConstructorRuleRhsIotaWeakFVKindWithBodyAndSourceApplied
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final base target : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    {motives minors : Array Expr} {ctx : Context} {minor : Expr} {rule : RecursorRule}
    (receipt : RecursorRuleRhsReceipt stats motives minors ctx constructor minor rule)
    {ids : List FVarId} (extension : IndexMLCtxExtension base ids final)
    {minorReader : Context} {virtual : VLCtx} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorMinorOpening env universes minorReader virtual parentName constructor
      domain rawSemantic peeled level)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (bodyClosed : ∀ terminal fields,
      (recursorMinorBody stats infos constructor terminal fields).looseBVarRange' = 0)
    (bodyPeeled : ∀ terminal fields,
      peelTypeAnnotations (recursorMinorBody stats infos constructor terminal fields) =
        recursorMinorBody stats infos constructor terminal fields)
    (envWF : env.WF)
    (canonical : ∀ {fields : Array Expr} {index : Nat} {hypotheses finalHypotheses : Array Expr}
      {suffixReader finalReader : Context} {domain : Expr}
      {source : RecursorIHDomainSource stats infos fields[index]! suffixReader domain}
      {tail : RecursorIHTrace stats fields infos (index + 1)
        (hypotheses.push (.fvar ⟨suffixReader.ngen.curr⟩))
        (recursorIHContext suffixReader fields[index]! domain) finalHypotheses finalReader}
      {initial middle : MLCtx}
      (bound : index < fields.size)
      (head : IHModelStep env universes source initial middle)
      (sourceExpr : Expr),
      CanonicalRecursiveIHInput head sourceExpr)
    {minorSemantic : VExpr}
    (minorTranslated : TrExprS env universes final.vlctx minor minorSemantic)
    (minorTyped : env.HasType universes.length final.vlctx.toCtx minorSemantic peeled)
    (converted : final.vlctx = virtual)
    (receiptShape : ∀ {fields : Array Expr} {replacements : List Expr}
      {bodySemantic bodyType : VExpr},
      TrExprS env universes final.vlctx
        (mkAppN (mkAppN minor fields) replacements.toArray) bodySemantic →
      env.HasType universes.length final.vlctx.toCtx bodySemantic bodyType →
      ∀ (receiptFields receiptValues : Array Expr) (current : Context),
        ctx.HeaderFrame current → rule.ctor = constructor.name →
        rule.nfields = receiptFields.size →
        ∃ _ : fields = receiptFields, ∃ _ : receiptValues = replacements.toArray,
          recursorRuleRhs stats motives minors receiptFields receiptValues current.lctx minor =
            final.lctx.mkLambda (ids.map Expr.fvar).toArray
              (mkAppN (mkAppN minor fields) replacements.toArray))
    {arguments : List VExpr} {resultType : VExpr}
    (argumentTyping : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      ElimNestedInductive.TypedParameterArguments env universes base valueType
        replacements arguments resultType)
    (kind : ∀ {replacements : List Expr} {value valueType},
      TrExprS env universes base.vlctx rule.rhs value →
      env.HasType universes.length base.vlctx.toCtx value valueType →
      env.SortArity universes.length base.vlctx.toCtx
        (count + replacements.length) valueType)
    (baseWF : base.WF env universes)
    (targetWF : target.WF env universes)
    {insertionLift : Lift}
    (insertion : VLCtx.FVLift' base.vlctx target.vlctx 0 insertionLift 0) :
    GeneratedConstructorRuleRhsResult (env := env) (universes := universes)
      (stats := stats) (motives := motives) (minors := minors) (ctx := ctx)
      (constructor := constructor) (minor := minor) (rule := rule) := by
  obtain ⟨fieldModel, terminal, fields, hypotheses, replacements, replacementTerminal,
    values, bodySemantic, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated⟩ := step.generatedConstructorRhsBody opening reserved bodyClosed bodyPeeled
      envWF
      (fun {fields} {index} {hypotheses finalHypotheses} {suffixReader finalReader} {domain}
          {source} {tail} {initial middle} bound head sourceExpr =>
        canonical (fields := fields) (index := index) (hypotheses := hypotheses)
          (finalHypotheses := finalHypotheses) (suffixReader := suffixReader)
          (finalReader := finalReader) (domain := domain) (source := source) (tail := tail)
          (initial := initial) (middle := middle) bound head sourceExpr)
      minorTranslated minorTyped converted
  have receiptShape' := receiptShape nestedTranslated bodyTyped
  obtain ⟨rhsSemantic, rhsType, ruleReceipt, rhsTranslated, rhsTyped⟩ :=
    step.abstractConstructorRuleRhs receipt extension receiptShape'
      nestedTranslated bodyTyped
      envWF
  obtain ⟨ruleReceipt, baseResultTranslated, baseResultTyped, baseResultKind,
    resultTranslated, resultTyped, resultKind⟩ :=
    ruleReceipt.applyIotaKindWeakFVKind rhsTranslated rhsTyped
      (argumentTyping rhsTranslated rhsTyped) envWF baseWF (kind rhsTranslated rhsTyped)
      targetWF insertion
  exact ⟨infos, domainReader, domain, ids, final, base, target, count, arguments, resultType,
    insertionLift, peeled, minorSemantic, fieldModel, terminal, fields, hypotheses,
    replacements, replacementTerminal, values, bodySemantic, rhsSemantic, rhsType,
    extension, insertion, sourceEq, nativeReceipt, typedArguments, bodyTranslated, bodyTyped,
    nestedTranslated, ruleReceipt, rhsTranslated, rhsTyped, kind rhsTranslated rhsTyped,
    baseResultTranslated, baseResultTyped, baseResultKind, resultTranslated, resultTyped,
    resultKind⟩

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

/- A translated field body already carries the closure fact required by the
   native telescope producer. Keep this adapter at the producer boundary so
   callers do not have to restate `looseBVarRange' = 0` after constructing the
   semantic body witness. -/
theorem MinorModelStep.nativeFieldArgumentsOfTranslated
    {env : VEnv} {universes : List Name} {parentName : Name}
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    {reader domainReader : Context} {domain : Expr}
    {source : RecursorMinorDomainSource stats infos constructor reader domain domainReader}
    {initial final : MLCtx}
    (step : MinorModelStep env universes parentName source initial final)
    (envWF : env.WF) {body : Expr} {bodySemantic : VExpr}
    (translated : TrExpr env universes final.vlctx body bodySemantic) :
    ∃ (fieldModel : MLCtx) (fields : Array Expr),
      NativeTelescopeArguments env universes final
        (fieldModel.lctx.mkForall fields body) fields.toList body := by
  have bodyClosed : body.looseBVarRange' = 0 :=
    (final.noBV ▸ translated.closed).looseBVarRange_zero
  exact step.nativeFieldArguments envWF bodyClosed

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
