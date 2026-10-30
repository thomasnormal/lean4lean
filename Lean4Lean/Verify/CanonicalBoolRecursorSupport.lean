import Lean4Lean.Verify.PrimitiveInductiveModel
import Lean4Lean.Verify.InductiveParentContextTranslation
import Lean4Lean.Verify.InductiveMinorPassTranslationCPS

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem canonicalBoolStopParentSupport
    {stats : InductiveStats} {reader : Context}
    {trace : RecursorIndexTrace stats (.sort (.succ .zero)) 0 #[] reader
      (.sort (.succ .zero)) 0 #[] reader}
    (head : stats.indConsts[0]! = .const ``Bool [])
    (params : stats.params = #[]) :
    ParentModelTranslationSupport canonicalBoolModel [`u] stats 0 trace := by
  cases trace with
  | stop notForall =>
    intro model modelWF native
    refine ⟨.sort (.succ .zero), .sort (by rfl), .stop notForall, .stop notForall, ?_⟩
    intro finalVirtual finalSemantic history
    cases history with
    | stop _ correspondence translated =>
      cases translated with
      | sort mapped =>
        rw [head, params]
        refine ⟨.const ``Bool [], .succ .zero, ?_, ?_, rfl, ?_⟩
        · exact TrExprS.const (ci := {uvars := 0, type := .sort (.succ .zero)})
            (us := []) (us' := []) canonicalBoolModel.headers.1 rfl rfl
        · exact VEnv.HasType.const
            (ci := {uvars := 0, type := .sort (.succ .zero)})
            (ls := []) canonicalBoolModel.headers.1 (by simp) rfl
        · change UniformAnnotationUniverse [`u] (.const ``Bool []) (.succ .zero)
          simp [UniformAnnotationUniverse]

theorem canonicalBoolMinorSourceSupport
    {stats : InductiveStats} {infos : Array RecInfo} {constructor : Constructor}
    (constructorType : constructor.type = .const ``Bool [])
    (constructorName : constructor.name = ``Bool.false ∨ constructor.name = ``Bool.true)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motive : ∃ fvar, infos[0]!.motive = .fvar fvar)
    {reader domainReader : Context} {domain : Expr}
    (source : RecursorMinorDomainSource stats infos constructor reader domain domainReader)
    (model : MLCtx) (modelWF : model.WF canonicalBoolModel [`u])
    (native : model.lctx = reader.lctx)
    (motiveSupport : ∀ {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ fieldModel, CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorSourceTranslationSupport canonicalBoolModel [`u] source model := by
  rcases constructor with ⟨constructorName', constructorType'⟩
  simp only at constructorType constructorName source ⊢
  cases constructorType
  intro terminal finalIndex fields recursiveFields fieldReader hypotheses
    fieldTrace hypothesisTrace domainEq
  have originalFieldTrace := fieldTrace
  cases fieldTrace with
  | stop terminalNotForall =>
    cases hypothesisTrace with
    | stop complete =>
      have headLookup : (canonicalBoolModel : VEnv).constants constructorName' =
          some ({uvars := 0, type := .const ``Bool []} : VConstant) := by
        rcases constructorName with rfl | rfl
        · exact canonicalBoolModel.headers.2.1
        · exact canonicalBoolModel.headers.2.2
      rw [params, levels]
      refine ⟨.const ``Bool [], .const constructorName' [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact TrExprS.const (ci := {uvars := 0, type := .sort (.succ .zero)})
          (us := []) (us' := []) canonicalBoolModel.headers.1 rfl rfl
      · exact TrExprS.const (ci := {uvars := 0, type := .const ``Bool []})
          (us := []) (us' := []) headLookup rfl rfl
      · exact VEnv.HasType.const (ci := {uvars := 0, type := .const ``Bool []})
          (ls := []) headLookup (by simp) rfl
      · exact .stop terminalNotForall
      · exact .stop complete
      · intro virtual semanticDomain _ translated typed
        obtain ⟨level, typed⟩ := typed
        refine ⟨level, typed, ?_⟩
        have emptyForall : ∀ body : Expr, reader.lctx.mkForall #[] body = body := by
          intro body
          simp only [Lean.LocalContext.mkForall, Lean.LocalContext.mkBinding,
            Array.size_empty, Nat.foldRev_zero, Expr.abstractRange_eq]
          have abstractEmpty : body.abstract #[] = body := by
            have h := Expr.abstract_eq body []
            simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil body 0)
          rw [abstractEmpty]
        rw [domainEq, recursorMinorDomain, recursorMinorBody, emptyForall, emptyForall,
          boolIndices]
        obtain ⟨fvar, motive⟩ := motive
        simp only [motive, params, levels, mkAppN, Array.foldl_empty]
        simp [UniformAnnotationUniverse]
      · intro fieldModel endpoint
        exact motiveSupport originalFieldTrace fieldModel endpoint
    | step bound source tail => simpa using bound

/- A canonical Bool constructor has no fields.  Its field endpoint therefore
   leaves the parent model unchanged, so a translated and typed parent motive
   can be reused for the IH application.  The endpoint supplies a canonical
   Bool terminal translation; the same constant shape normalizes every
   terminal translation accepted by the support contract. -/
theorem canonicalBoolCtorFieldEndpointIHMotiveApplicationSupport
    {stats : InductiveStats} {infos : Array RecInfo}
    {terminal : Expr} {finalIndex : Nat} {fields recursiveFields : Array Expr}
    {reader fieldReader : Context} {model fieldModel : MLCtx}
    {semantic motiveSemantic : VExpr} {motive : FVarId}
    {level : VLevel}
    {fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
      terminal finalIndex fields recursiveFields fieldReader}
    (endpoint : CtorFieldModelEndpoint canonicalBoolModel [`u]
      fieldTrace model fieldModel semantic)
    (fieldsEq : fields = #[])
    (terminalEq : terminal = .const ``Bool [])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motiveEq : infos[0]!.motive = .fvar motive)
    (motiveTranslated : TrExprS canonicalBoolModel [`u] model.vlctx
      (.fvar motive) motiveSemantic)
    (motiveTyped : canonicalBoolModel.HasType 1 model.vlctx.toCtx motiveSemantic
      (.forallE (.const ``Bool []) (.sort level))) :
    IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal := by
  obtain ⟨endpointTerminalSemantic, endpointTerminalTranslated⟩ := endpoint.terminalTranslation
  obtain ⟨_, _, _, _, _, _, ids, extension, selected⟩ := endpoint
  have idsNil : ids = [] := by
    have mapped : ids.map Expr.fvar = [] := by
      simpa only [fieldsEq, Array.toList_empty] using selected.symm
    exact List.map_eq_nil_iff.mp mapped
  have idsLength : ids.length = 0 := by simp only [idsNil, List.length_nil]
  have fieldModelEq : fieldModel = model := by
    induction extension with
    | nil => rfl
    | push earlier id name domain semantic bi =>
      simp only [List.length_append, List.length_singleton] at idsLength
      omega
  subst fieldModel
  intro terminalSemantic' terminalTranslated'
  rw [terminalEq] at endpointTerminalTranslated terminalTranslated'
  cases endpointTerminalTranslated with
  | const _ levels _ =>
    simp at levels
    cases levels
    cases terminalTranslated' with
    | const _ levels _ =>
      simp at levels
      cases levels
      refine ⟨motiveSemantic, level, ?_, ?_⟩
      · simpa only [terminalEq, boolIndices, motiveEq, mkAppN, Array.foldl_empty,
          List.map_nil, List.toArray] using motiveTranslated
      · simpa only [List.length_cons, List.length_nil, Nat.zero_add] using motiveTyped

/- The translated parent step stores the motive as the newest virtual binder.
   This projection exposes its source fvar translation and typing at the final
   parent model.  The native motive source is reduced here to the canonical
   Bool telescope; the universe on the translated whole Pi type is kept
   separate from the universe of the motive body. -/
theorem canonicalBoolParentMotiveFVarPremises
    {stats : InductiveStats} {elimLevel : Level} {indices : Array Expr}
    {indexReader : Context} {indexVirtual : VLCtx} {initial final : MLCtx}
    {ids : List FVarId}
    (step : RecursorParentModelStep canonicalBoolModel [`u] stats #[canonicalBoolType]
      elimLevel 0 indices indexReader indexVirtual initial final ids)
    (params : stats.params = #[])
    (indConsts : stats.indConsts = #[.const ``Bool []])
    (indicesEq : indices = #[]) :
    ∃ (bodyLevel : VLevel),
      TrExprS canonicalBoolModel [`u] final.vlctx
        (.fvar ⟨(recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats 0 indices)).ngen.curr⟩) (.bvar 0) ∧
      canonicalBoolModel.HasType 1 final.vlctx.toCtx (.bvar 0)
        (.forallE (.const ``Bool []) (.sort bodyLevel)) := by
  obtain ⟨rawSemantic, peeled, majorLevel, motiveSemantic, motiveTypeLevel,
    majorOpening, motiveOpening, finalWF, finalNative, finalConverted, extension, idsEq⟩ := step
  obtain rfl := indicesEq
  have majorDomain : recursorMajorDomain stats 0 #[] = .const ``Bool [] := by
    simp only [recursorMajorDomain, params, indConsts, mkAppN]
    rfl
  let majorReader := recursorIndexContext indexReader `t .default (.const ``Bool [])
  have majorFrame : indexReader.RecursorScopeFrame majorReader := by
    simpa only [majorReader, majorDomain] using majorOpening.2.2.2.2.2.2.2
  have majorWF : majorReader.lctx.WF := majorFrame.wf
  let majorDecl : LocalDecl := .cdecl indexReader.lctx.decls.size
    ⟨indexReader.ngen.curr⟩ `t (.const ``Bool []) .default .default
  have majorMem : majorDecl ∈ majorReader.lctx.toList := by
    simp only [majorDecl, majorReader, recursorIndexContext,
      LocalContext.mkLocalDecl_toList, List.mem_cons]
    exact Or.inl trivial
  have majorLookup : majorReader.lctx.find? ⟨indexReader.ngen.curr⟩ = some majorDecl := by
    show majorReader.lctx.find? majorDecl.fvarId = some majorDecl
    exact majorWF.find?_of_mem majorMem
  have emptyForall : ∀ body : Expr, majorReader.lctx.mkForall #[] body = body := by
    intro body
    simp only [Lean.LocalContext.mkForall, Lean.LocalContext.mkBinding,
      Array.size_empty, Nat.foldRev_zero, Expr.abstractRange_eq]
    have abstractEmpty : body.abstract #[] = body := by
      have h := Expr.abstract_eq body []
      simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil body 0)
    rw [abstractEmpty]
  have singleton : majorReader.lctx.mkForall #[.fvar ⟨indexReader.ngen.curr⟩]
      (.sort elimLevel) = .forallE `t (.const ``Bool []) (.sort elimLevel) .default := by
    simp only [Lean.LocalContext.mkForall, Lean.LocalContext.mkBinding, Expr.abstractRange_eq]
    change Nat.foldRev 1 _ ((Expr.sort elimLevel).abstract #[.fvar ⟨indexReader.ngen.curr⟩]) = _
    rw [Nat.foldRev_succ, Nat.foldRev_zero]
    have hindex0 : (#[(.fvar ⟨indexReader.ngen.curr⟩)] : Array Expr)[0] =
        .fvar ⟨indexReader.ngen.curr⟩ := by rfl
    have hlookupFVar : majorReader.lctx.findFVar? (.fvar ⟨indexReader.ngen.curr⟩) = some majorDecl := by
      change majorReader.lctx.find? ⟨indexReader.ngen.curr⟩ = some majorDecl
      exact majorLookup
    rw [hindex0, hlookupFVar]
    simp only [majorDecl, Expr.abstractRange_eq]
    have constAbstract : (Expr.const ``Bool []).abstract #[] = Expr.const ``Bool [] := by
      have h := Expr.abstract_eq (Expr.const ``Bool []) []
      simpa only [List.map_nil] using h.trans (Expr.abstractFVars_nil _ 0)
    have sortAbstract : (Expr.sort elimLevel).abstract
        #[.fvar ⟨indexReader.ngen.curr⟩] = Expr.sort elimLevel := by
      have h := Expr.abstract_eq (Expr.sort elimLevel) [⟨indexReader.ngen.curr⟩]
      have h' : (Expr.sort elimLevel).abstract #[.fvar ⟨indexReader.ngen.curr⟩] =
          (Expr.sort elimLevel).abstractFVars [⟨indexReader.ngen.curr⟩] := by simpa using h
      rw [h']
      simp [Expr.abstractFVars]
    simp [constAbstract, sortAbstract]
  have translated := motiveOpening.1.1
  simp only [recursorMotiveDomain, majorDomain] at translated
  change TrExprS canonicalBoolModel [`u] _
    (peelTypeAnnotations (majorReader.lctx.mkForall #[]
      (majorReader.lctx.mkForall #[.fvar ⟨indexReader.ngen.curr⟩]
        (.sort elimLevel)))) motiveSemantic at translated
  rw [emptyForall, singleton] at translated
  simp only [peelTypeAnnotations] at translated
  have motiveLookup : final.vlctx.find? (.inr
      ⟨(recursorIndexContext indexReader `t .default
        (recursorMajorDomain stats 0 #[])).ngen.curr⟩) =
      some (.bvar 0, motiveSemantic.lift) := by
    rw [finalConverted]
    simpa only [recursorMotiveVirtualContext] using
      (VLCtx.find?_vlam_self
        (fv := ⟨(recursorIndexContext indexReader `t .default
          (recursorMajorDomain stats 0 #[])).ngen.curr⟩)
        (deps := (recursorMotiveDomain elimLevel #[]
          (.fvar ⟨indexReader.ngen.curr⟩)
          (recursorIndexContext indexReader `t .default
            (recursorMajorDomain stats 0 #[]))).fvarsList)
        (ty := motiveSemantic)
        (Δ := recursorMajorVirtualContext stats 0 #[] indexReader indexVirtual peeled))
  cases translated with
  | forallE hA hB hAT hBT =>
    cases hAT with
    | const henv hlevels hlen =>
      cases hBT with
      | @sort u' hlevel =>
        simp [VLevel.ofLevel] at hlevels
        cases hlevels
        refine ⟨hlevel, .fvar motiveLookup, ?_⟩
        have typed := finalWF.tr.wf.find?_wf canonicalBoolModel.wf.ordered motiveLookup
        simpa only [VExpr.lift, VExpr.liftN, Nat.zero_add,
          List.length_cons, List.length_nil] using typed

end Lean4Lean.AddInductive

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

theorem canonicalBoolMinorTraceSupport
    {stats : InductiveStats} {infos finalInfos : Array RecInfo}
    {reader finalReader : Context}
    (trace : RecursorMinorTrace stats ``Bool 0 infos
      [({name := ``Bool.false, type := .const ``Bool []} : Constructor),
       {name := ``Bool.true, type := .const ``Bool []}] reader finalInfos finalReader)
    (params : stats.params = #[]) (levels : stats.levels = [])
    (indConsts : stats.indConsts = #[.const ``Bool []]) (nindices : stats.nindices = #[0])
    (boolIndices : getIIndices stats (.const ``Bool []) = (0, #[]))
    (motives : ∀ {infos : Array RecInfo}, ∃ fvar, infos[0]!.motive = .fvar fvar)
    (motiveSupport : ∀ {infos : Array RecInfo} {reader : Context}
      {terminal finalIndex fields recursiveFields fieldReader semantic},
      (fieldTrace : RecursorCtorFieldTrace stats (.const ``Bool []) 0 #[] #[] reader
        terminal finalIndex fields recursiveFields fieldReader) →
      ∀ (model : MLCtx) (fieldModel : MLCtx), CtorFieldModelEndpoint canonicalBoolModel [`u]
        fieldTrace model fieldModel semantic →
        IHMotiveApplicationSupport canonicalBoolModel [`u] stats infos fieldModel.vlctx terminal) :
    MinorTraceTranslationSupport canonicalBoolModel [`u] trace := by
  cases trace with
  | step source tail =>
    refine .step source tail ?_ ?_
    · intro model modelWF native
      have motiveProof : ∃ fvar, infos[0]!.motive = .fvar fvar := motives
      exact canonicalBoolMinorSourceSupport rfl (Or.inl rfl) params levels indConsts nindices
        boolIndices motiveProof source model modelWF native (by
          exact fun fieldTrace fieldModel endpoint =>
            motiveSupport fieldTrace model fieldModel endpoint)
    · cases tail with
      | step source tail =>
        refine .step source tail ?_ ?_
        · intro model modelWF native
          exact canonicalBoolMinorSourceSupport (source := source) rfl (Or.inr rfl) params levels indConsts nindices
            boolIndices (@motives _) model modelWF native (by
          exact fun fieldTrace fieldModel endpoint =>
            motiveSupport fieldTrace model fieldModel endpoint)
        · cases tail
          exact MinorTraceTranslationSupport.stop

end Lean4Lean.AddInductive
