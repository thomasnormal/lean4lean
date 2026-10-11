import Lean4Lean.Verify.InductiveConstructorSemanticReceipts
import Lean4Lean.Verify.InductiveHeaderKinds
import Lean4Lean.Verify.InductiveReturnTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open ElimNestedInductive (ParameterPrefix ContextReserved)
open private selectedParameterBound absentParameterBound from Lean4Lean.Verify.InductiveConstructorDomainTrace
open private relatedMemberRight from Lean4Lean.Verify.InductiveConstructorSemanticReceipts

theorem _root_.Lean4Lean.TrConstructor.forallWF
    (translated : TrConstructor environment universes constructor semantic)
    (binder : constructor.type.isForall = true) : semantic.toVConstant.WF environment := by
  rcases constructor with ⟨constructorName, constructorType⟩
  rcases semantic with ⟨⟨universeCount, semanticType⟩, semanticName⟩
  obtain ⟨_, count, translated⟩ := translated
  change universes.length = universeCount at count
  change constructorType.isForall = true at binder
  cases constructorType <;> simp only [Expr.isForall, Bool.false_eq_true] at binder
  cases translated with
  | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
    simpa only [VConstant.WF, VLCtx.toCtx, ← count] using domainTyped.forallE bodyTyped

theorem _root_.Lean4Lean.TrConstructor.sortArityWF
    (translated : TrConstructor environment universes constructor semantic)
    (environmentWF : environment.WF)
    (kind : environment.SortArity universes.length [] 0 semantic.type) :
    semantic.toVConstant.WF environment := by
  have typed := kind.isType environmentWF (by exact trivial)
  simpa only [VConstant.WF, translated.2.1] using typed

theorem _root_.Lean4Lean.TrConstructor.typehoodWF
    (translated : TrConstructor environment universes constructor semantic)
    (typed : environment.IsType universes.length [] semantic.type) :
    semantic.toVConstant.WF environment := by
  simpa only [VConstant.WF, translated.2.1] using typed

theorem CanonicalAnnotationConstants.mono (constants : CanonicalAnnotationConstants environment)
    (increase : environment ≤ extended) : CanonicalAnnotationConstants extended :=
  ⟨increase.constants constants.outParam, increase.constants constants.semiOutParam,
    increase.constants constants.optParam, increase.constants constants.autoParam⟩

theorem CanonicalAnnotationDefinitions.mono (definitions : CanonicalAnnotationDefinitions environment)
    (increase : environment ≤ extended) : CanonicalAnnotationDefinitions extended :=
  ⟨increase.defeqs definitions.outParam, increase.defeqs definitions.semiOutParam,
    increase.defeqs definitions.optParam, increase.defeqs definitions.autoParam,
    increase.constants definitions.syntaxConstant⟩

theorem CheckedConstructorDomainReceipts.requiresBinder
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    {trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal}
    (receipts : CheckedConstructorDomainReceipts environment universes trace source target finalSource finalTarget)
    (growth : finalTarget.length = target.length + stats.params.size) (positive : 0 < stats.params.size) :
    type.isForall = true := by
  cases trace with
  | terminal => cases receipts <;> first | rfl | omega
  | parameter => rfl
  | field => rfl

theorem ConstructorSemanticReceipts.parameterizedTypesWF
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) (positive : 0 < stats.params.size) :
    ∀ header ∈ receipts.declaration.types, ∀ constructor ∈ header.ctors,
      constructor.toVConstant.WF stage.semantic := by
  intro header member constructor present
  obtain ⟨sourceHeader, sourceMember, headerTranslated⟩ :=
    relatedMemberRight receipts.translated.2.2 member
  obtain ⟨sourceConstructor, sourcePresent, constructorTranslated⟩ :=
    relatedMemberRight headerTranslated.2.2.2 present
  obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp sourceMember)
  obtain ⟨finalReader, finalIndex, terminal, finalTarget, trace, domains, agreement, growth⟩ :=
    receipts.domains parent bound sourceConstructor sourcePresent
  exact constructorTranslated.forallWF (domains.requiresBinder growth positive)

theorem AcceptedConstructorTrace.isType
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    {environment : VEnv} {universes : List Name} {context : VLCtx} {semantic : VExpr}
    (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (translated : TrExprS environment universes context type semantic)
    (headerKind : ∀ {headerSemantic},
      TrExprS environment universes context stats.indConsts[parent]! headerSemantic →
      ∃ headerType, environment.HasType universes.length context.toCtx headerSemantic headerType ∧
        environment.SortArity universes.length context.toCtx
          (stats.params.size + stats.nindices[parent]!) headerType) :
    environment.IsType universes.length context.toCtx semantic := by
  cases trace with
  | terminal notForall valid =>
    exact isValidIndAppIdx.isType environmentWF contextWF valid translated headerKind
  | parameter | field =>
    cases translated with
    | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
      exact domainTyped.forallE bodyTyped

theorem ConstructorSemanticReceipts.typesWF
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (headerKinds : ∀ parent, parent < types.size → ∀ {headerSemantic},
      TrExprS stage.semantic root.lparams [] stats.indConsts[parent]! headerSemantic →
      ∃ headerType, stage.semantic.HasType root.lparams.length [] headerSemantic headerType ∧
        stage.semantic.SortArity root.lparams.length []
          (stats.params.size + stats.nindices[parent]!) headerType) :
    ∀ header ∈ receipts.declaration.types, ∀ constructor ∈ header.ctors,
      constructor.toVConstant.WF stage.semantic := by
  intro header member constructor present
  obtain ⟨sourceHeader, sourceMember, headerTranslated⟩ :=
    relatedMemberRight receipts.translated.2.2 member
  obtain ⟨sourceConstructor, sourcePresent, constructorTranslated⟩ :=
    relatedMemberRight headerTranslated.2.2.2 present
  obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp sourceMember)
  obtain ⟨finalReader, finalIndex, terminal, finalTarget, trace, domains, agreement, growth⟩ :=
    receipts.domains parent bound sourceConstructor sourcePresent
  have environmentWF := VEnv.addInductHeaders.wf root.Ewf
    (fun header member => (receipts.headersWF header member).2) receipts.registered
  exact constructorTranslated.typehoodWF
    (trace.isType (context := []) (universes := root.lparams) environmentWF trivial
      constructorTranslated.2.2 (headerKinds parent bound))

theorem AcceptedConstructorTrace.isTypeOfContextualKinds
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    {environment : VEnv} {universes : List Name} {semantic : VExpr}
    (environmentWF : environment.WF)
    (translated : TrExprS environment universes [] type semantic)
    (headerKind : ∀ {headerSemantic},
      TrExprS environment universes [] stats.indConsts[parent]! headerSemantic →
      ∃ headerType context, environment.HasType universes.length [] headerSemantic headerType ∧
        OnCtx context (environment.IsType universes.length) ∧
        environment.SortArity universes.length context
          (stats.params.size + stats.nindices[parent]!) headerType) :
    environment.IsType universes.length [] semantic := by
  cases trace with
  | terminal notForall valid =>
    exact isValidIndAppIdx.isTypeOfContextualKinds environmentWF valid translated headerKind
  | parameter | field =>
    cases translated with
    | forallE domainTyped bodyTyped domainTranslated bodyTranslated =>
      exact domainTyped.forallE bodyTyped

theorem ConstructorSemanticReceipts.typesWFOfHeaders
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe)
    (headerKinds : ∀ parent, parent < types.size → ∃ header ∈ receipts.declaration.types,
      stats.indConsts[parent]! = .const header.name stats.levels ∧
        stage.semantic.SortArity header.uvars []
          (stats.params.size + stats.nindices[parent]!) header.type) :
    ∀ header ∈ receipts.declaration.types, ∀ constructor ∈ header.ctors,
      constructor.toVConstant.WF stage.semantic := by
  apply receipts.typesWF
  intro parent bound headerSemantic translated
  obtain ⟨header, member, head, kind⟩ := headerKinds parent bound
  have environmentWF := VEnv.addInductHeaders.wf root.Ewf
    (fun header member => (receipts.headersWF header member).2) receipts.registered
  exact TrExprS.constantKind environmentWF
    (VEnv.addInductHeaders.constants receipts.registered member) kind (head ▸ translated)

theorem ConstructorSemanticReceipts.contextualHeaderKinds
    {stage : HeaderAxiomContinuation root original 0 types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) (parent : Nat) (bound : parent < types.size) :
    ∃ header ∈ receipts.declaration.types,
      stats.indConsts[parent]! = .const header.name stats.levels ∧
      stage.semantic.SortArity header.uvars stage.before.model.checker.vlctx.toCtx
        (stats.params.size + stats.nindices[parent]!) header.type := by
  obtain ⟨incomplete, member, head, kind⟩ := stage.before.contextualHeaderKind parent bound
  obtain ⟨complete, member, signature⟩ := relatedMemberRight receipts.headerSignatures member
  have name := congrArg VConstVal.name signature
  have constant := congrArg VConstVal.toVConstant signature
  have universes := congrArg VConstant.uvars constant
  have type := congrArg VConstant.type constant
  refine ⟨complete, member, ?_, ?_⟩
  · simpa only [name] using head
  · simpa only [universes, type] using kind.mono (VEnv.addInductHeaders.le receipts.registered)

theorem ConstructorSemanticReceipts.constructorTypesWF
    {stage : HeaderAxiomContinuation root original nparams types stats reader actual}
    (receipts : ConstructorSemanticReceipts stage isUnsafe) :
    ∀ header ∈ receipts.declaration.types, ∀ constructor ∈ header.ctors,
      constructor.toVConstant.WF stage.semantic := by
  by_cases positive : 0 < stats.params.size
  · exact receipts.parameterizedTypesWF positive
  intro header member constructor present
  obtain ⟨sourceHeader, sourceMember, headerTranslated⟩ :=
    relatedMemberRight receipts.translated.2.2 member
  obtain ⟨sourceConstructor, sourcePresent, constructorTranslated⟩ :=
    relatedMemberRight headerTranslated.2.2.2 present
  obtain ⟨parent, bound, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp sourceMember)
  have nonempty : types.size ≠ 0 := by omega
  have zero : nparams = 0 := by
    have count := stage.before.parameterCount
    simp only [InductiveStats.ParamsCount, if_neg nonempty] at count
    omega
  subst nparams
  obtain ⟨finalReader, finalIndex, terminal, finalTarget, trace, domains, agreement, growth⟩ :=
    receipts.domains parent bound sourceConstructor sourcePresent
  have environmentWF := VEnv.addInductHeaders.wf root.Ewf
    (fun header member => (receipts.headersWF header member).2) receipts.registered
  apply constructorTranslated.typehoodWF
  apply trace.isTypeOfContextualKinds environmentWF constructorTranslated.2.2
  intro headerSemantic translated
  obtain ⟨matched, matchedMember, head, kind⟩ := receipts.contextualHeaderKinds parent bound
  have headerUniverses : matched.uvars = root.lparams.length :=
    (receipts.headersWF matched matchedMember).1.trans receipts.translated.1.symm
  have contextWF : OnCtx stage.before.model.checker.vlctx.toCtx (stage.semantic.IsType matched.uvars) := by
    rw [headerUniverses]
    have beforeWF : OnCtx stage.before.model.checker.vlctx.toCtx (root.venv.IsType root.lparams.length) := by
      simpa only [stage.before.sameEnv, stage.before.sameUniverses] using
        stage.before.model.checker.Δwf.toCtx
    exact beforeWF.mono fun typed => typed.mono (VEnv.addInductHeaders.le receipts.registered)
  exact TrExprS.contextualConstantKind (VEnv.addInductHeaders.constants receipts.registered matchedMember)
    contextWF kind (head ▸ translated)

def ConstructorReaderModels (initial : TypeChecker.VContext) (sourceSemantic : VExpr)
    (stats : InductiveStats) (index : Nat) (reader : Context) (finalIndex : Nat) (terminal : Expr) : Prop :=
  ∃ (checker : TypeChecker.VContext) (identifiers : List FVarId) (semantic : VExpr),
    checker.venv = initial.venv ∧ checker.lparams = initial.lparams ∧
    HeaderCheckerAligned checker reader ∧ ({} : TypeChecker.VState).WF checker ∧
    ParameterPrefix initial.mlctx checker.mlctx identifiers ∧
    identifiers.length = (finalIndex - stats.params.size) - (index - stats.params.size) ∧
    checker.TrExprS terminal semantic ∧ (initial.IsType sourceSemantic → checker.IsType semantic)

theorem acceptedConstructorDomainSort (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    {domain sort : Expr} {semantic : VExpr} (translated : checker.TrExprS domain semantic)
    (accepted : (monadLift (TypeChecker.ensureType domain) : M Expr) reader = .ok sort) :
    ∃ level semanticLevel, sort = .sort level ∧ VLevel.ofLevel checker.lparams level = some semanticLevel ∧
      checker.HasType semantic (.sort semanticLevel) := by
  have nativeAccepted : (Prod.fst <$> TypeChecker.ensureType domain
      checker.toContext ({} : TypeChecker.VState).toState) = .ok sort := by
    rw [aligned]
    exact accepted
  generalize checked : TypeChecker.ensureType domain
    checker.toContext ({} : TypeChecker.VState).toState = returned at nativeAccepted
  cases returned with
  | error exception => simp at nativeAccepted
  | ok returned =>
    obtain ⟨result, final⟩ := returned
    change Except.ok result = .ok sort at nativeAccepted
    cases nativeAccepted
    obtain ⟨_, _, _, _, resultSemantic, resultTranslated, level, semanticLevel, sorted, levels, typed⟩ :=
      TypeChecker.ensureType.WF translated initialWF sort final checked
    have equality := translated.uniq checker.Ewf
      (.refl checker.Ewf.ordered checker.Δwf) resultTranslated
    exact ⟨level, semanticLevel, sorted, levels,
      typed.defeqU_l checker.Ewf checker.Δwf.toCtx equality.symm⟩

theorem AcceptedConstructorTrace.checkerModels
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameters : HeaderParameterModels stats checker.vlctx)
    {semantic : VExpr} (translated : checker.TrExprS type semantic) :
    ConstructorReaderModels checker semantic stats index finalReader finalIndex terminal := by
  induction trace generalizing checker semantic with
  | terminal notForall valid =>
    exact ⟨checker, [], semantic, rfl, rfl, aligned, initialWF, .nil, by simp, translated, id⟩
  | @parameter index parameter reader stored domain body finalReader finalIndex terminal name binder
      selected storedCall equalCall tail induction =>
    have bound := selectedParameterBound selected
    have member : parameter ∈ stats.params := by
      have same : stats.params[index] = parameter := by
        simpa only [Array.getElem?_eq_getElem bound, Option.some.injEq] using selected
      exact same ▸ Array.getElem_mem bound
    obtain ⟨identifier, equation, present⟩ := parameters parameter member
    obtain ⟨declaration, lookup⟩ := checker.trlctx.find?_eq_some.mpr present
    have lookup : reader.lctx.find? identifier = some declaration := by
      simpa only [checker.lctx_eq, congrArg TypeChecker.Context.lctx aligned] using lookup
    obtain ⟨openedSemantic, opened, openedTyped⟩ := translatedReusedHeaderParameterOpening checker reader
      aligned initialWF lookup translated (by simpa only [equation] using storedCall) equalCall
    obtain ⟨finalChecker, identifiers, terminalSemantic, environment, universes, finalAligned, finalWF,
      history, count, terminalTranslated, terminalTyped⟩ := induction checker aligned initialWF reserved different
        constants definitions parameters (by simpa only [equation] using opened)
    refine ⟨finalChecker, identifiers, terminalSemantic, environment, universes, finalAligned, finalWF,
      history, ?_, terminalTranslated, fun _ => terminalTyped openedTyped⟩
    omega
  | @field index domain reader sort name binder body finalReader finalIndex terminal
      notParameter domainChecked universeAccepted positive tail induction =>
    obtain ⟨peeled, nextChecker, environment, universes, context, nextAligned, nextWF,
      openedSemantic, opened, openedTyped⟩ := translatedHeaderOpening checker reader aligned initialWF reserved
        different constants definitions translated
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [context]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have nextParameters := parameters.mono head.insertion.fvars_sublist.subset
    obtain ⟨finalChecker, identifiers, terminalSemantic, finalEnv, finalUniverses, finalAligned, finalWF,
      history, count, terminalTranslated, terminalTyped⟩ := induction nextChecker nextAligned nextWF
        pushed.reserved different (environment ▸ constants) (environment ▸ definitions) nextParameters opened
    have afterParameters := absentParameterBound notParameter
    have monotone := tail.index_le
    refine ⟨finalChecker, ⟨reader.ngen.curr⟩ :: identifiers, terminalSemantic,
      finalEnv.trans environment, finalUniverses.trans universes, finalAligned, finalWF,
      ?_, ?_, terminalTranslated, fun _ => terminalTyped openedTyped⟩
    · simpa only [List.singleton_append] using head.trans history
    · simp only [List.length_cons]
      omega

theorem AcceptedConstructorTrace.zeroParameterKind
    {stats : InductiveStats} {isUnsafe : Bool} {parent index finalIndex : Nat}
    {reader finalReader : Context} {type terminal : Expr}
    (trace : AcceptedConstructorTrace stats isUnsafe parent reader index type finalReader finalIndex terminal)
    (zero : stats.params = #[])
    (checker : TypeChecker.VContext) (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv)
    (parameters : HeaderParameterModels stats checker.vlctx)
    {semantic : VExpr} (translated : checker.TrExprS type semantic)
    (anchor : ∀ {anchorChecker : TypeChecker.VContext} {anchorReader : Context},
      HeaderCheckerAligned anchorChecker anchorReader →
      ({} : TypeChecker.VState).WF anchorChecker →
      {anchorSemantic : VExpr} → anchorChecker.TrExprS terminal anchorSemantic →
      anchorChecker.venv.SortArity anchorChecker.lparams.length anchorChecker.vlctx.toCtx 0 anchorSemantic) :
    checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx (finalIndex - index) semantic := by
  induction trace generalizing checker semantic with
  | terminal notForall valid =>
    simpa only [Nat.sub_self] using anchor aligned initialWF translated
  | parameter selected accepted tail induction =>
    have impossible : False := by
      simpa [zero] using (selectedParameterBound selected)
    exact impossible.elim
  | @field index domain reader sort name binder body finalReader finalIndex terminal
      notParameter domainChecked universeAccepted positive tail induction =>
    obtain ⟨peeled, nextChecker, environment, universes, context, nextAligned, nextWF,
      openedSemantic, opened, openedTyped, domainSemantic, bodySemantic, level, sourceShape,
      domainTyped, domainEquality, bodyEquality⟩ := translatedHeaderOpeningWithSemantics checker reader aligned
        initialWF reserved different constants definitions translated
    have native : checker.mlctx.lctx = reader.lctx :=
      checker.lctx_eq.trans (congrArg TypeChecker.Context.lctx aligned)
    have pushed := Context.RecursorScopeFrame.push reader (native ▸ checker.trlctx.1) reserved name binder
      (peelTypeAnnotations domain)
    have head : ParameterPrefix checker.mlctx nextChecker.mlctx [⟨reader.ngen.curr⟩] := by
      rw [context]
      simpa only [List.nil_append] using ParameterPrefix.snoc (ParameterPrefix.nil (base := checker.mlctx))
    have nextParameters := parameters.mono head.insertion.fvars_sublist.subset
    have bodyKind := induction nextChecker nextAligned nextWF pushed.reserved different
      (environment ▸ constants) (environment ▸ definitions) nextParameters opened anchor
    have bodyKind' : nextChecker.venv.SortArity nextChecker.lparams.length
        nextChecker.vlctx.toCtx (finalIndex - (index + 1)) openedSemantic := bodyKind
    have bodyEquality' : nextChecker.venv.IsDefEqU nextChecker.lparams.length
        nextChecker.vlctx.toCtx openedSemantic bodySemantic := bodyEquality
    have bodyKind := bodyKind'.defeq nextChecker.Ewf nextChecker.Δwf.toCtx bodyEquality'.symm
    have bodyKind : checker.venv.SortArity checker.lparams.length (peeled :: checker.vlctx.toCtx)
        (finalIndex - (index + 1)) bodySemantic := by
      simpa only [environment, universes, TypeChecker.VContext.vlctx, context, MLCtx.vlctx, VLCtx.toCtx] using bodyKind
    have contexts : checker.venv.IsDefEqCtx checker.lparams.length checker.vlctx.toCtx
        (peeled :: checker.vlctx.toCtx) (domainSemantic :: checker.vlctx.toCtx) :=
      .succ .zero domainEquality.symm
    have bodyKind := bodyKind.defeqCtx checker.Ewf.ordered contexts
    have domainIsType : checker.IsType domainSemantic := ⟨level, domainTyped⟩
    have bodyIsType := bodyKind.isType checker.Ewf ⟨checker.Δwf.toCtx, domainIsType⟩
    obtain ⟨sortLevel, sourceTyped⟩ := domainIsType.forallE bodyIsType
    have equality : checker.IsDefEqU semantic (.forallE domainSemantic bodySemantic) :=
      sourceShape.symm ▸ ⟨.sort sortLevel, sourceTyped⟩
    have monotone := tail.index_le
    have exactCount : finalIndex - index = (finalIndex - (index + 1)) + 1 := by omega
    rw [exactCount]
    exact .forallE domainIsType equality bodyKind

theorem TypedHeaderReader.constructorReaderModels (model : TypedHeaderReader base stats reader)
    (reserved : ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants model.checker.venv)
    (definitions : CanonicalAnnotationDefinitions model.checker.venv)
    (types : Array InductiveType) (isUnsafe : Bool) :
    (checkConstructors types stats isUnsafe reader).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ semantic finalReader finalIndex terminal,
          ∃ _trace : AcceptedConstructorTrace stats isUnsafe parent reader 0 constructor.type
            finalReader finalIndex terminal,
          model.checker.TrExprS constructor.type semantic ∧
          ConstructorReaderModels model.checker semantic stats 0 finalReader finalIndex terminal := by
  refine (checkConstructors.acceptedTraces types stats isUnsafe reader).mono ?_
  intro _ traces parent bound constructor member
  obtain ⟨result, finalReader, finalIndex, terminal, guarded, checked, trace⟩ :=
    traces parent bound constructor member
  have free := checkNoMVarNoFVar.WF reader.env constructor.name constructor.type () guarded
  obtain ⟨semantic, translated⟩ := acceptedSourceTranslation model.checker reader model.aligned model.initialWF
    (free.mono fun _ impossible => impossible.elim) checked
  exact ⟨semantic, finalReader, finalIndex, terminal, trace, translated,
    trace.checkerModels model.checker model.aligned model.initialWF reserved different constants definitions
      model.parameterModels translated⟩

theorem HeaderAxiomContinuation.shadowConstructorReaderModels
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (isUnsafe : Bool) :
    (checkConstructors types stats isUnsafe { reader with env := stage.shadow }).WF fun _ =>
      ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
        ∃ semantic finalReader finalIndex terminal,
          ∃ _trace : AcceptedConstructorTrace stats isUnsafe parent { reader with env := stage.shadow }
            0 constructor.type finalReader finalIndex terminal,
          stage.model.checker.TrExprS constructor.type semantic ∧
          ConstructorReaderModels stage.model.checker semantic stats 0 finalReader finalIndex terminal := by
  have increase := VEnv.addInductHeaders.le stage.registered
  have constants : CanonicalAnnotationConstants stage.model.checker.venv :=
    stage.semantic_eq.symm ▸ constants.mono increase
  have definitions : CanonicalAnnotationDefinitions stage.model.checker.venv :=
    stage.semantic_eq.symm ▸ definitions.mono increase
  exact stage.model.constructorReaderModels stage.before.readerReserved stage.before.readerDifferent
    constants definitions types isUnsafe

structure TypedConstructorReceipts
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual) (isUnsafe : Bool) where
  inputs : ConstructorSemanticReceipts stage isUnsafe
  constructorTypesWF : ∀ header ∈ inputs.declaration.types, ∀ constructor ∈ header.ctors,
    constructor.toVConstant.WF stage.semantic
  readers : ∀ parent, ∀ bound : parent < types.size, ∀ constructor ∈ types[parent].ctors,
    ∃ semantic finalReader finalIndex terminal,
      ∃ _trace : AcceptedConstructorTrace stats isUnsafe parent { reader with env := stage.shadow }
        0 constructor.type finalReader finalIndex terminal,
      stage.model.checker.TrExprS constructor.type semantic ∧
      ConstructorReaderModels stage.model.checker semantic stats 0 finalReader finalIndex terminal

theorem HeaderAxiomContinuation.shadowTypedConstructors
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (isUnsafe : Bool)
    (accepted : checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok ()) :
    Nonempty (TypedConstructorReceipts stage isUnsafe) := by
  obtain ⟨inputs⟩ := stage.shadowConstructorSemantics empty isUnsafe accepted
  exact ⟨⟨inputs, inputs.constructorTypesWF,
    stage.shadowConstructorReaderModels constants definitions isUnsafe () accepted⟩⟩

theorem HeaderAxiomContinuation.typedConstructors
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (empty : root.mlctx = .nil) (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv) (isUnsafe : Bool) (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure original.env)
    (recursors : NativeRecursorParentsClosed original.env) :
    (checkConstructors types stats isUnsafe { reader with env := actual }).WF fun _ =>
      Nonempty (TypedConstructorReceipts stage isUnsafe) := by
  intro result accepted
  obtain ⟨shadowAccepted, _⟩ := stage.acceptedConstructorsFromInitial isUnsafe fresh constructors recursors result accepted
  exact stage.shadowTypedConstructors empty constants definitions isUnsafe shadowAccepted

theorem checkInductiveTypes.typedConstructorAxiomContinuation
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (next : InductiveStats → Kernel.Environment → M resultType)
    (root : TypeChecker.VContext) (reader : Context) (aligned : HeaderCheckerAligned root reader)
    (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false)
    (safetyBound : root.safety ≤ if isUnsafe then .unsafe else .safe)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (checkInductiveTypes nparams types (fun stats => do
      let actual ← declareInductiveTypes stats nparams types numNested isUnsafe
      withEnv actual do
        checkConstructors types stats isUnsafe
        let final ← declareConstructors stats types isUnsafe
        withEnv final (next stats actual)) reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types stats current actual,
        NativeValueFrame actual final ∧ Nonempty (TypedConstructorReceipts stage isUnsafe) := by
  refine (checkInductiveTypes.nativeConstructorAxiomContinuation nparams types numNested isUnsafe next root reader
    aligned empty different constants definitions ordinary safetyBound constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    metadata, actualAccepted, shadowAccepted, traces⟩
  exact ⟨stats, current, actual, final, stage, retained,
    stage.shadowTypedConstructors empty constants definitions isUnsafe shadowAccepted⟩

theorem run.typedConstructorAxiomContinuation (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (root : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned root reader) (empty : root.mlctx = .nil)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants root.venv)
    (definitions : CanonicalAnnotationDefinitions root.venv)
    (ordinary : reader.allowPrimitive = false) (ordinarySafety : root.safety ≠ .partial)
    (constructors : NativeConstructorParentClosure reader.env)
    (recursors : NativeRecursorParentsClosed reader.env) :
    (run nparams types numNested reader).WF fun _ => ∃ stats current actual final,
      ∃ stage : HeaderAxiomContinuation root reader nparams types.toArray stats current actual,
        NativeValueFrame actual final ∧ Nonempty (TypedConstructorReceipts stage (reader.safety != .safe)) := by
  refine (run.nativeConstructorAxiomContinuation nparams types numNested root reader aligned empty different
    constants definitions ordinary ordinarySafety constructors recursors).mono ?_
  rintro result ⟨stats, current, actual, final, stage, fresh, shadowFresh, distinct, retained,
    metadata, actualAccepted, shadowAccepted, traces⟩
  exact ⟨stats, current, actual, final, stage, retained,
    stage.shadowTypedConstructors empty constants definitions (reader.safety != .safe) shadowAccepted⟩

end Lean4Lean.AddInductive
