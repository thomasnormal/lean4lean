import Lean4Lean.Verify.InductiveNativeAlignment
import Lean4Lean.Verify.StagedLeaves
import Lean4Lean.Verify.TypeChecker.ScopedDelta
import Lean4Lean.Verify.TypeChecker.ScopedInferType
import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.TypeChecker.InferType

namespace Lean4Lean.Tests.InductiveNativeAlignment

open Lean Lean4Lean Lean4Lean.NativeInductive

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    {first second : Expr} {firstSemantic secondSemantic : VExpr}
    (lookup : ∀ {name ci ci'}, context.env.find? name = some ci →
      context.venv.constants name = some ci' → ci.name = name ∧
        TrConstant context.safety context.venv ci ci')
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (TypeChecker.Inner.lazyDeltaReductionStep first second).ScopeWF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) :=
  TypeChecker.Inner.lazyDeltaReductionStep.scopeWFOf lookup firstTranslation secondTranslation

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    {first second : Expr} {firstSemantic secondSemantic : VExpr}
    (lookup : ∀ {name ci ci'}, context.env.find? name = some ci →
      context.venv.constants name = some ci' → ci.name = name ∧
        TrConstant context.safety context.venv ci ci')
    (firstTranslation : context.TrExprS first firstSemantic)
    (secondTranslation : context.TrExprS second secondSemantic) :
    (TypeChecker.Inner.lazyDeltaReductionStep first second).WF context state
      (fun result _ => result.WF context firstSemantic secondSemantic true) :=
  TypeChecker.Inner.lazyDeltaReductionStep.WFOf lookup firstTranslation secondTranslation

example {context : TypeChecker.VContext} {state : TypeChecker.VState}
    {expression : Expr} {inferOnly : Bool}
    (lookup : ∀ {name ci}, context.env.find? name = some ci → context.safety ≤ ci.safety →
      ∃ ci', context.venv.constants name = some ci' ∧
        TrConstant context.safety context.venv ci ci')
    (freeVariables : expression.FVarsIn (· ∈ context.vlctx.fvars))
    (translated : inferOnly = true → ∃ semantic, context.TrExprS expression semantic) :
    (TypeChecker.Inner.inferType' expression inferOnly).ScopeWF context state fun type _ =>
      ∃ semantic semanticType, context.TrTyping expression type semantic semanticType :=
  TypeChecker.Inner.inferType'.scopeWFOf lookup freeVariables translated

example {context : TypeChecker.VContext} {name : Name} {levels : List Level}
    {inferOnly : Bool}
    (lookup : ∀ {constantName ci}, context.env.find? constantName = some ci →
      context.safety ≤ ci.safety →
      ∃ ci', context.venv.constants constantName = some ci' ∧
        TrConstant context.safety context.venv ci ci')
    (lookupUnique : ∀ {constantName ci ci'}, context.env.find? constantName = some ci →
      context.venv.constants constantName = some ci' →
      ci.name = constantName ∧ TrConstant context.safety context.venv ci ci')
    (levelsNoMVar : ∀ level ∈ levels, level.hasMVar' = false)
    (translated : inferOnly = true →
      ∃ model, context.TrExprS (.const name levels) model) :
    (TypeChecker.Inner.inferConstant context.toContext name levels inferOnly).WF fun result =>
      ∃ model type, context.TrTyping (.const name levels) result model type :=
  TypeChecker.Inner.inferConstant.WFOf lookup lookupUnique levelsNoMVar translated

example {context : TypeChecker.VContext} {expression : Expr} {semantic : VExpr}
    (value : ∀ {name ci value}, context.env.find? name = some ci →
      context.safety ≤ ci.safety → ci.deltaValue? = some value →
      TrExpr context.venv ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length)))
    (lookupUnique : ∀ {name ci ci'}, context.env.find? name = some ci →
      context.venv.constants name = some ci' →
      ci.name = name ∧ TrConstant context.safety context.venv ci ci')
    (translated : context.TrExprS expression semantic) :
    (TypeChecker.Inner.unfoldDefinitionCore expression).WF context {}
      (fun result _ => TypeChecker.Inner.UnfoldDefinition.WF context expression expression semantic result) :=
  TypeChecker.Inner.unfoldDefinitionCore.WFOf value lookupUnique translated

example {ctx : TypeChecker.Context} {semantic : VEnv} {scope : VLCtx} {Q : Bool}
    (checker : CheckerEnvInductive ctx.safety ctx.env semantic Q)
    (hscope : scope.WF semantic ctx.lparams.length) (hnoBV : scope.NoBV)
    (hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (hinfer : inferOnly = true →
      ∃ model, TrExprS semantic ctx.lparams scope (.const name levels) model) :
    (TypeChecker.Inner.inferConstant ctx name levels inferOnly).WF fun result =>
      ∃ model type, TrTyping semantic ctx.lparams scope (.const name levels) result model type :=
  TypeChecker.Inner.inferConstant.checkerInductive checker hscope hnoBV hlevels hinfer

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned .safe constants env) :
    Aligned .safe resultConstants result :=
  evidence.aligned haligned

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned .unsafe constants env) :
    Aligned .unsafe resultConstants result :=
  evidence.aligned haligned

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned .safe constants env) :
    Aligned .safe evidence.constructorConstants evidence.constructorEnv :=
  haligned.addInductEvidence (evidence.to_addInductEvidence haligned.map_wf)

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (safety : DefinitionSafety) (hconstants : constants.WF) :
    AddInductEvidence safety constants env decl evidence.constructorConstants
      evidence.constructorEnv :=
  evidence.to_addInductEvidence_at safety hconstants

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.headerEnv.WF :=
  evidence.headerEnvWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.constructorEnv.WF :=
  evidence.constructorEnvWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    AddInductWithRecursorsEvidence .safe constants env decl
      evidence.constructorConstants evidence.constructorEnv
      (evidence.recursors.map (·.info)) (evidence.recursors.map (·.model))
      resultConstants result :=
  evidence.to_addInductWithRecursorsEvidence hconstants hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result :=
  (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).to_addInductWithRecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    env ≤ result :=
  (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).le

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) : result.WF :=
  evidence.resultWF henv hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : evidence.constructorEnv.WF)
    (hsource : ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF evidence.constructorEnv :=
  evidence.recursorWF_of_sourceTypehood henv hsource

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) :
    ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic :=
  evidence.sourceTypehood_of_recursorWF hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : evidence.constructorEnv.WF) :
    (∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) ↔
    (∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF evidence.constructorEnv) :=
  evidence.sourceTypehood_iff_recursorWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result ∧
      result.WF :=
  evidence.registrationWF henv hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hsource : ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result ∧
      result.WF :=
  evidence.registrationWF_of_sourceTypehood henv hsource

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    VDecl.WF env (.induct decl) evidence.constructorEnv :=
  evidence.inductiveDeclWF

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) :
    evidence.constructorEnv.WF :=
  evidence.inductiveHistoryWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    {Q : Bool} (history : TrEnvInductive .safe constants Q env)
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    TrEnvInductive .safe resultConstants Q result :=
  evidence.to_trEnvInductive history hconstants hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    {Q : Bool} (history : TrEnvInductive .safe constants Q env)
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    (∃ ci, resultConstants.find? name = some ci ∧ .safe ≤ ci.safety) ↔
      ∃ ci, result.constants name = some ci := by
  exact (evidence.to_trEnvInductive history hconstants hrecursors).find?_iff

example {env : VEnv} {native : Kernel.Environment} {Q : Bool}
    (history : TrEnvInductive .safe native.constants Q env)
    (hvalues : ∀ {name ci value}, native.constants.find? name = some ci →
      DefinitionSafety.safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr env ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe native env Q := by
  refine ⟨history, ?_⟩
  exact hvalues

example {env : VEnv} {native : Kernel.Environment} {Q : Bool}
    (checker : CheckerEnvInductive .safe native env Q)
    (history : TrEnvInductive .safe native.constants Q env) :
    CheckerEnvInductive .safe native env Q :=
  checker.of_valueFrame history (NativeValueFrame.refl history.map_wf) .rfl

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    {native resultNative : Kernel.Environment} {Q : Bool}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (history : TrEnvInductive .safe native.constants Q env)
    (hmap : native.constants = constants) (hresultMap : resultNative.constants = resultConstants)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv)
    (hvalues : ∀ (name : Name) (ci : ConstantInfo) {value},
      resultNative.constants.find? name = some ci →
      .safe ≤ ci.safety → ci.safety = .safe → ci.value? = some value →
      TrExpr result ci.levelParams [] value
        (.const ci.name (VLevel.params ci.levelParams.length))) :
    CheckerEnvInductive .safe resultNative result Q :=
  evidence.toCheckerEnvInductive native resultNative history hmap hresultMap hconstants hrecursors hvalues

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    {native : Kernel.Environment} {Q : Bool}
    (history : TrEnvInductive .safe native.constants Q env)
    (name : Name) (ci : ConstantInfo) (h : native.find? name = some ci)
    (hs : .safe ≤ ci.safety) :
    ∃ ci', env.constants name = some ci' ∧ TrConstant .safe env ci ci' :=
  history.env_find? h hs

example {env env' : VEnv} {declaration : VDecl}
    (henv : env.WF) (hdecl : VDecl.WF env declaration env') : env'.WF :=
  VEnv.WF.decl henv hdecl

end Lean4Lean.Tests.InductiveNativeAlignment
