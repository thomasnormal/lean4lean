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
