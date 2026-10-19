import Lean4Lean.Theory.Typing.QuotPatternSoundness
import Lean4Lean.Theory.Typing.RewriteMetadata

namespace Lean4Lean.VEnv

variable {environment extended : VEnv} {name : Lean.Name} {constant : VConstant}
  {definition : VDefVal}

inductive RewriteRule (environment : VEnv) : (pattern : Pattern) → pattern.RHS × pattern.Check → Prop where
  | delta {definition : VDefVal} (closed : definition.value.Closed)
      (registered : environment.defeqs definition.toDefEq) :
      RewriteRule environment (.const definition.name) (.fixed definition.value closed, .true)
  | quot (registered : environment.defeqs quotDefEq) :
      RewriteRule environment quotLiftPattern (quotLiftPatternResult, quotLiftPatternCheck)

theorem RewriteRule.simple (rule : RewriteRule environment pattern result) :
    ∃ simple : SimplePattern, pattern = simple.toPattern := by
  cases rule with
  | delta => exact ⟨.defn _, rfl⟩
  | quot => exact ⟨.iota ``Quot.lift 5 ``Quot.mk 3, rfl⟩

theorem RewriteRule.sound (environmentWF : environment.WF)
    (localsWF : OnCtx locals (environment.IsType universes))
    (rule : RewriteRule environment pattern result)
    (matched : pattern.Matches expression levels values)
    (typed : environment.HasType universes locals expression resultType)
    (checked : result.2.OK (environment.IsDefEqU universes locals) levels values) :
    environment.IsDefEqU universes locals expression (result.1.apply levels values) := by
  cases rule with
  | @delta definition closed registered =>
    let .const := matched
    obtain ⟨constant, found, levelsWF, arity⟩ := typed.const_inv environmentWF.ordered localsWF
    rw [environmentWF.rewriteMetadata.lookup registered] at found
    cases found
    have equation := IsDefEq.extra registered levelsWF arity (Γ := locals)
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id arity, Pattern.RHS.apply]
      using equation.toU
  | quot registered =>
    exact (quotLiftPattern.sound environmentWF localsWF registered matched typed checked).toU

theorem RewriteRule.equation {equation : VDefEq} {levels : List VLevel}
    (environmentWF : environment.WF)
    (registered : environment.defeqs equation)
    (arity : levels.length = equation.uvars) :
    Pattern.Equation (RewriteRule environment) (environment.IsDefEqU universes) locals
      (equation.lhs.instL levels) (equation.rhs.instL levels) := by
  rcases environmentWF.rewriteMetadata.classify registered with rfl | ⟨definition, rfl⟩
  · exact quotDefEq.patternEquation (.quot registered)
  · have closed : definition.value.Closed :=
      (environmentWF.ordered.defEqWF registered).2.closedN environmentWF.ordered trivial
    change levels.length = definition.uvars at arity
    have certificate := Pattern.Equation.rule (equal := environment.IsDefEqU universes)
      (locals := locals) (RewriteRule.delta closed registered)
      (Pattern.Matches.const (c := definition.name) (ls := levels)) True.intro
    simpa only [VDefVal.toDefEq, VExpr.instL, VLevel.inst_map_id arity, Pattern.RHS.apply]
      using certificate

end Lean4Lean.VEnv
