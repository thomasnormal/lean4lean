import Lean4Lean.Verify.InductiveAnnotationTyping
import Lean4Lean.Verify.Typing.Lemmas

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

structure CanonicalAnnotationConstants (env : VEnv) : Prop where
  outParam : env.constants ``_root_.outParam =
    some { uvars := 1, type := (unaryAnnotationDefinition ``_root_.outParam).type }
  semiOutParam : env.constants ``_root_.semiOutParam =
    some { uvars := 1, type := (unaryAnnotationDefinition ``_root_.semiOutParam).type }
  optParam : env.constants ``_root_.optParam =
    some { uvars := 1, type := optParamDefinition.type }
  autoParam : env.constants ``_root_.autoParam =
    some { uvars := 1, type := autoParamDefinition.type }

def UniformAnnotationUniverse (universes : List Name) (source : Expr) (level : VLevel) : Prop :=
  match source with
  | .app (.const name levels) carrier =>
    if name = ``_root_.outParam ∨ name = ``_root_.semiOutParam then
      levels.mapM (VLevel.ofLevel universes) = some [level] ∧
        UniformAnnotationUniverse universes carrier level
    else True
  | .app (.app (.const name levels) carrier) _ =>
    if name = ``_root_.optParam ∨ name = ``_root_.autoParam then
      levels.mapM (VLevel.ofLevel universes) = some [level] ∧
        UniformAnnotationUniverse universes carrier level
    else True
  | _ => True
termination_by structural source

private theorem annotationArgument_hasType {env : VEnv} {uvars : Nat}
    {context : List VExpr} {function argument domain body canonicalDomain canonicalBody : VExpr}
    (envWF : env.WF) (contextWF : OnCtx context (env.IsType uvars))
    (functionTyped : env.HasType uvars context function (.forallE domain body))
    (canonicalTyped : env.HasType uvars context function (.forallE canonicalDomain canonicalBody))
    (argumentTyped : env.HasType uvars context argument domain) :
    env.HasType uvars context argument canonicalDomain := by
  obtain ⟨_, functionTypes⟩ := functionTyped.uniq envWF contextWF canonicalTyped
  obtain ⟨_, domainTypes⟩ := (functionTypes.toU.forallE_inv envWF contextWF).1
  exact domainTypes.defeq argumentTyped

private theorem annotationLevels_singleton {universes : List Name} {levels : List Level}
    {semanticLevels : List VLevel} {level : VLevel}
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (uniform : levels.mapM (VLevel.ofLevel universes) = some [level]) :
    ∃ sourceLevel, levels = [sourceLevel] ∧ semanticLevels = [level] ∧ level.WF universes.length := by
  have lengths := (List.mapM_eq_some.mp uniform).length_eq
  obtain ⟨sourceLevel, sourceLevels⟩ := List.length_eq_one_iff.mp
    (by simpa only [List.length_cons, List.length_nil] using lengths)
  exact ⟨sourceLevel, sourceLevels, Option.some.inj (mapped.symm.trans uniform),
    VLevel.WF.of_mapM_ofLevel uniform level (by simp only [List.mem_singleton])⟩

private theorem peelTypeAnnotations_unchanged {source : Expr}
    (notUnary : ∀ name levels carrier, source = .app (.const name levels) carrier → False)
    (notBinary : ∀ name levels carrier extra,
      source = .app (.app (.const name levels) carrier) extra → False) :
    AddInductive.peelTypeAnnotations source = source := by
  cases source <;> try rfl
  case app function argument =>
    cases function <;> try rfl
    case const name levels => exact False.elim (notUnary name levels argument rfl)
    case app function carrier =>
      cases function <;> try rfl
      case const name levels => exact False.elim (notBinary name levels carrier argument rfl)

theorem TypedAnnotationSpine.ofTrExprS {env : VEnv} {universes : List Name} {context : VLCtx}
    {source : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF) (contextWF : OnCtx context.toCtx (env.IsType universes.length))
    (constants : CanonicalAnnotationConstants env)
    (uniform : UniformAnnotationUniverse universes source level)
    (translated : TrExprS env universes context source semantic)
    (typed : env.HasType universes.length context.toCtx semantic (.sort level)) :
    TypedAnnotationSpine (TrExprS env universes context) env universes.length context.toCtx
      source semantic level := by
  induction source using AddInductive.peelTypeAnnotations.induct generalizing semantic with
  | case1 name levels carrier recognized carrierInduction =>
    simp only [UniformAnnotationUniverse, recognized, ↓reduceIte] at uniform
    obtain ⟨uniformLevels, uniformCarrier⟩ := uniform
    have original := translated
    cases translated with
    | app functionTyped carrierTyped functionTranslated carrierTranslated =>
      cases functionTranslated with
      | const lookup mapped arity =>
        obtain ⟨sourceLevel, sourceLevels, semanticLevels, levelWF⟩ :=
          annotationLevels_singleton mapped uniformLevels
        cases sourceLevels
        cases semanticLevels
        rcases recognized with recognized | recognized
        · subst name
          have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.outParam
            (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
          simp only [unaryAnnotationDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
          have carrierTyping := annotationArgument_hasType envWF contextWF
            functionTyped canonicalTyped carrierTyped
          exact .outParam sourceLevel levelWF original
            (carrierInduction uniformCarrier carrierTranslated carrierTyping)
        · subst name
          have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.semiOutParam
            (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
          simp only [unaryAnnotationDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
          have carrierTyping := annotationArgument_hasType envWF contextWF
            functionTyped canonicalTyped carrierTyped
          exact .semiOutParam sourceLevel levelWF original
            (carrierInduction uniformCarrier carrierTranslated carrierTyping)
  | case2 name levels carrier unrecognized =>
    exact .base
      (by simp only [AddInductive.peelTypeAnnotations, unrecognized, ↓reduceIte]) translated typed
  | case3 name levels carrier extra recognized carrierInduction =>
    simp only [UniformAnnotationUniverse, recognized, ↓reduceIte] at uniform
    obtain ⟨uniformLevels, uniformCarrier⟩ := uniform
    have original := translated
    cases translated with
    | app functionTyped extraTyped functionTranslated extraTranslated =>
      cases functionTranslated with
      | app innerFunctionTyped carrierTyped innerFunctionTranslated carrierTranslated =>
        cases innerFunctionTranslated with
        | const lookup mapped arity =>
          obtain ⟨sourceLevel, sourceLevels, semanticLevels, levelWF⟩ :=
            annotationLevels_singleton mapped uniformLevels
          cases sourceLevels
          cases semanticLevels
          rcases recognized with recognized | recognized
          · subst name
            have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.optParam
              (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
            simp only [optParamDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
            have carrierTyping := annotationArgument_hasType envWF contextWF
              innerFunctionTyped canonicalTyped carrierTyped
            have canonicalApplied := canonicalTyped.app carrierTyping
            simp [VExpr.inst, VExpr.instVar] at canonicalApplied
            have extraTyping := annotationArgument_hasType envWF contextWF
              functionTyped canonicalApplied extraTyped
            exact .optParam sourceLevel levelWF original extraTyping
              (carrierInduction uniformCarrier carrierTranslated carrierTyping)
          · subst name
            have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.autoParam
              (ls := [level]) (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
            simp only [autoParamDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero, List.map_nil] at canonicalTyped
            have carrierTyping := annotationArgument_hasType envWF contextWF
              innerFunctionTyped canonicalTyped carrierTyped
            have canonicalApplied := canonicalTyped.app carrierTyping
            simp only [VExpr.inst] at canonicalApplied
            have extraTyping := annotationArgument_hasType envWF contextWF
              functionTyped canonicalApplied extraTyped
            exact .autoParam sourceLevel levelWF original extraTyping
              (carrierInduction uniformCarrier carrierTranslated carrierTyping)
  | case4 name levels carrier extra unrecognized =>
    exact .base
      (by simp only [AddInductive.peelTypeAnnotations, unrecognized, ↓reduceIte]) translated typed
  | case5 expression notUnary notBinary =>
    exact .base (peelTypeAnnotations_unchanged notUnary notBinary) translated typed

end Lean4Lean.AddInductive
