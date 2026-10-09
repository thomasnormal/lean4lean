import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean.AddInductive

def unaryAnnotationDefinition (name : Name) : VDefEq where
  uvars := 1
  lhs := .const name [.param 0]
  rhs := .lam (.sort (.param 0)) (.bvar 0)
  type := .forallE (.sort (.param 0)) (.sort (.param 0))

def optParamDefinition : VDefEq where
  uvars := 1
  lhs := .const ``_root_.optParam [.param 0]
  rhs := .lam (.sort (.param 0)) (.lam (.bvar 0) (.bvar 1))
  type := .forallE (.sort (.param 0)) (.forallE (.bvar 0) (.sort (.param 0)))

def autoParamDefinition : VDefEq where
  uvars := 1
  lhs := .const ``_root_.autoParam [.param 0]
  rhs := .lam (.sort (.param 0)) (.lam (.const ``Lean.Syntax []) (.bvar 1))
  type := .forallE (.sort (.param 0))
    (.forallE (.const ``Lean.Syntax []) (.sort (.param 0)))

structure CanonicalAnnotationDefinitions (environment : VEnv) : Prop where
  outParam : environment.defeqs (unaryAnnotationDefinition ``_root_.outParam)
  semiOutParam : environment.defeqs (unaryAnnotationDefinition ``_root_.semiOutParam)
  optParam : environment.defeqs optParamDefinition
  autoParam : environment.defeqs autoParamDefinition
  syntaxConstant : environment.constants ``Lean.Syntax =
    some { uvars := 0, type := .sort (.succ .zero) }

theorem unaryAnnotation_isDefEq {environment : VEnv} {universeCount : Nat}
    {context : List VExpr} {name : Name} {level : VLevel} {carrier : VExpr}
    (definition : environment.defeqs (unaryAnnotationDefinition name))
    (levelFits : level.WF universeCount)
    (carrierTyping : environment.HasType universeCount context carrier (.sort level)) :
    environment.IsDefEq universeCount context (.app (.const name [level]) carrier)
      carrier (.sort level) := by
  have delta := VEnv.IsDefEq.extra (Γ := context) definition
    (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelFits)
    rfl
  simp only [unaryAnnotationDefinition, VExpr.instL, VLevel.inst,
    List.getD_cons_zero, List.map_cons, List.map_nil] at delta
  have applied := VEnv.IsDefEq.appDF delta carrierTyping
  have body : environment.HasType universeCount (.sort level :: context) (.bvar 0)
      (.sort level) := VEnv.IsDefEq.bvar .zero
  have reduced := VEnv.IsDefEq.beta body carrierTyping
  simpa [VExpr.inst, VExpr.instVar] using applied.trans reduced

theorem CanonicalAnnotationDefinitions.outParam_isDefEq {environment : VEnv}
    (definitions : CanonicalAnnotationDefinitions environment)
    {universeCount : Nat} {context : List VExpr} {level : VLevel} {carrier : VExpr}
    (levelFits : level.WF universeCount)
    (carrierTyping : environment.HasType universeCount context carrier (.sort level)) :
    environment.IsDefEq universeCount context
      (.app (.const ``_root_.outParam [level]) carrier) carrier (.sort level) :=
  unaryAnnotation_isDefEq definitions.outParam levelFits carrierTyping

theorem CanonicalAnnotationDefinitions.semiOutParam_isDefEq {environment : VEnv}
    (definitions : CanonicalAnnotationDefinitions environment)
    {universeCount : Nat} {context : List VExpr} {level : VLevel} {carrier : VExpr}
    (levelFits : level.WF universeCount)
    (carrierTyping : environment.HasType universeCount context carrier (.sort level)) :
    environment.IsDefEq universeCount context
      (.app (.const ``_root_.semiOutParam [level]) carrier) carrier (.sort level) :=
  unaryAnnotation_isDefEq definitions.semiOutParam levelFits carrierTyping

theorem CanonicalAnnotationDefinitions.optParam_isDefEq {environment : VEnv}
    (definitions : CanonicalAnnotationDefinitions environment)
    (ordered : environment.Ordered)
    {universeCount : Nat} {context : List VExpr} {level : VLevel}
    {carrier extra : VExpr}
    (levelFits : level.WF universeCount)
    (carrierTyping : environment.HasType universeCount context carrier (.sort level))
    (extraTyping : environment.HasType universeCount context extra carrier) :
    environment.IsDefEq universeCount context
      (.app (.app (.const ``_root_.optParam [level]) carrier) extra)
      carrier (.sort level) := by
  have delta := VEnv.IsDefEq.extra (Γ := context) definitions.optParam
    (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelFits)
    rfl
  simp only [optParamDefinition, VExpr.instL, VLevel.inst,
    List.getD_cons_zero, List.map_cons, List.map_nil] at delta
  have binderTyping : environment.HasType universeCount (.sort level :: context)
      (.bvar 0) (.sort level) := VEnv.IsDefEq.bvar .zero
  have bodyTyping : environment.HasType universeCount
      (.bvar 0 :: .sort level :: context) (.bvar 1) (.sort level) :=
    VEnv.IsDefEq.bvar (.succ .zero)
  have lambdaTyping := VEnv.IsDefEq.lamDF binderTyping bodyTyping
  have firstReduction := VEnv.IsDefEq.beta lambdaTyping carrierTyping
  have first := (VEnv.IsDefEq.appDF delta carrierTyping).trans firstReduction
  simp [VExpr.inst, VExpr.instVar] at first
  have liftedTyping : environment.HasType universeCount (carrier :: context)
      carrier.lift (.sort level) := by
    simpa only [VExpr.liftN] using carrierTyping.weakN ordered (.one (A := carrier))
  have secondReduction := VEnv.IsDefEq.beta liftedTyping extraTyping
  simpa only [VExpr.inst, VExpr.inst_lift] using
    (VEnv.IsDefEq.appDF first extraTyping).trans secondReduction

theorem CanonicalAnnotationDefinitions.autoParam_isDefEq {environment : VEnv}
    (definitions : CanonicalAnnotationDefinitions environment)
    (ordered : environment.Ordered)
    {universeCount : Nat} {context : List VExpr} {level : VLevel}
    {carrier extra : VExpr}
    (levelFits : level.WF universeCount)
    (carrierTyping : environment.HasType universeCount context carrier (.sort level))
    (extraTyping : environment.HasType universeCount context extra (.const ``Lean.Syntax [])) :
    environment.IsDefEq universeCount context
      (.app (.app (.const ``_root_.autoParam [level]) carrier) extra)
      carrier (.sort level) := by
  have delta := VEnv.IsDefEq.extra (Γ := context) definitions.autoParam
    (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelFits)
    rfl
  simp only [autoParamDefinition, VExpr.instL, VLevel.inst,
    List.getD_cons_zero, List.map_cons, List.map_nil] at delta
  have syntaxTyping : environment.HasType universeCount (.sort level :: context)
      (.const ``Lean.Syntax []) (.sort (.succ .zero)) := by
    simpa only [VExpr.instL] using
      VEnv.HasType.const definitions.syntaxConstant (by simp) rfl
  have bodyTyping : environment.HasType universeCount
      (.const ``Lean.Syntax [] :: .sort level :: context) (.bvar 1) (.sort level) :=
    VEnv.IsDefEq.bvar (.succ .zero)
  have lambdaTyping := VEnv.IsDefEq.lamDF syntaxTyping bodyTyping
  have firstReduction := VEnv.IsDefEq.beta lambdaTyping carrierTyping
  have first := (VEnv.IsDefEq.appDF delta carrierTyping).trans firstReduction
  simp [VExpr.inst, VExpr.instVar] at first
  have liftedTyping : environment.HasType universeCount (.const ``Lean.Syntax [] :: context)
      carrier.lift (.sort level) := by
    simpa only [VExpr.liftN] using
      carrierTyping.weakN ordered (.one (A := .const ``Lean.Syntax []))
  have secondReduction := VEnv.IsDefEq.beta liftedTyping extraTyping
  simpa only [VExpr.inst, VExpr.inst_lift] using
    (VEnv.IsDefEq.appDF first extraTyping).trans secondReduction

end Lean4Lean.AddInductive
