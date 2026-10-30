import Lean4Lean.Verify.InductiveAnnotationTranslation
import Lean4Lean.Verify.ConstructorHeaders
import Lean4Lean.Verify.InductiveEliminationLevel
import Lean4Lean.Theory.InductiveHeaders
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean
open Lean hiding Environment Exception
open AddInductive

/- A semantic environment for canonical primitive translation must expose the
   prelude annotation interface even when the native fixture starts empty.
   Keeping this environment separate from the native checker environment makes
   that model-side obligation explicit. -/
def canonicalAnnotationModel : VEnv where
  constants name :=
    if name = ``_root_.outParam then
      some { uvars := 1, type := (unaryAnnotationDefinition ``_root_.outParam).type }
    else if name = ``_root_.semiOutParam then
      some { uvars := 1, type := (unaryAnnotationDefinition ``_root_.semiOutParam).type }
    else if name = ``_root_.optParam then some { uvars := 1, type := optParamDefinition.type }
    else if name = ``_root_.autoParam then some { uvars := 1, type := autoParamDefinition.type }
    else if name = ``Lean.Syntax then
      some { uvars := 0, type := .sort (.succ .zero) }
    else none
  defeqs definition := definition = unaryAnnotationDefinition ``_root_.outParam ∨
    definition = unaryAnnotationDefinition ``_root_.semiOutParam ∨
    definition = optParamDefinition ∨ definition = autoParamDefinition

theorem canonicalAnnotationModel.constants :
    CanonicalAnnotationConstants canonicalAnnotationModel := by
  constructor <;> rfl

theorem canonicalAnnotationModel.definitions :
    CanonicalAnnotationDefinitions canonicalAnnotationModel := by
  constructor <;> simp [canonicalAnnotationModel]

private def annotationOutValue : VDefVal :=
  ⟨⟨⟨1, (unaryAnnotationDefinition ``_root_.outParam).type⟩, ``_root_.outParam⟩,
    (unaryAnnotationDefinition ``_root_.outParam).rhs⟩
private def annotationSemiValue : VDefVal :=
  ⟨⟨⟨1, (unaryAnnotationDefinition ``_root_.semiOutParam).type⟩, ``_root_.semiOutParam⟩,
    (unaryAnnotationDefinition ``_root_.semiOutParam).rhs⟩
private def annotationOptValue : VDefVal :=
  ⟨⟨⟨1, optParamDefinition.type⟩, ``_root_.optParam⟩, optParamDefinition.rhs⟩
private def annotationAutoValue : VDefVal :=
  ⟨⟨⟨1, autoParamDefinition.type⟩, ``_root_.autoParam⟩, autoParamDefinition.rhs⟩
private def annotationSyntaxValue : VConstVal :=
  ⟨⟨0, .sort (.succ .zero)⟩, ``Lean.Syntax⟩

private def annotationSyntaxBase : VEnv where
  constants n := if n = annotationSyntaxValue.name then some annotationSyntaxValue.toVConstant else none
  defeqs _ := False

private def annotationAutoBase : VEnv where
  constants n :=
    if n = annotationAutoValue.name then some annotationAutoValue.toVConstant
    else annotationSyntaxBase.constants n
  defeqs _ := False

private def annotationOptBase : VEnv where
  constants n :=
    if n = annotationOptValue.name then some annotationOptValue.toVConstant
    else annotationAutoBase.constants n
  defeqs _ := False

private def annotationSemiBase : VEnv where
  constants n :=
    if n = annotationSemiValue.name then some annotationSemiValue.toVConstant
    else annotationOptBase.constants n
  defeqs _ := False

private def annotationBase : VEnv where
  constants n :=
    if n = annotationOutValue.name then some annotationOutValue.toVConstant
    else annotationSemiBase.constants n
  defeqs _ := False

private def annotationAutoEnv : VEnv :=
  annotationAutoBase.addDefEq annotationAutoValue.toDefEq
private def annotationOptEnv : VEnv :=
  (annotationOptBase.addDefEq annotationAutoValue.toDefEq).addDefEq annotationOptValue.toDefEq
private def annotationSemiEnv : VEnv :=
  ((annotationSemiBase.addDefEq annotationAutoValue.toDefEq).addDefEq annotationOptValue.toDefEq).addDefEq
    annotationSemiValue.toDefEq
private def annotationEnv : VEnv :=
  (((annotationBase.addDefEq annotationAutoValue.toDefEq).addDefEq annotationOptValue.toDefEq).addDefEq
    annotationSemiValue.toDefEq).addDefEq annotationOutValue.toDefEq

private theorem addAnnotationSyntax : VEnv.empty.addConst annotationSyntaxValue.name
    annotationSyntaxValue.toVConstant = some annotationSyntaxBase := by
  have hnone : VEnv.empty.constants annotationSyntaxValue.name = none := by rfl
  unfold VEnv.addConst
  rw [hnone]
  simp only [Option.some.injEq]
  apply VEnv.ext
  · funext n
    simp [VEnv.empty, annotationSyntaxBase, annotationSyntaxValue, eq_comm]
    rfl
  · rfl

private theorem addAnnotationAuto : annotationSyntaxBase.addConst annotationAutoValue.name
    annotationAutoValue.toVConstant = some annotationAutoBase := by
  have hnone : annotationSyntaxBase.constants annotationAutoValue.name = none := by
    simp [annotationSyntaxBase, annotationAutoValue, annotationSyntaxValue, eq_comm]
  unfold VEnv.addConst
  rw [hnone]
  simp only [Option.some.injEq]
  apply VEnv.ext
  · funext n
    simp [annotationAutoBase, annotationSyntaxBase, annotationAutoValue, annotationSyntaxValue, eq_comm]
    rfl
  · rfl

private theorem addAnnotationOpt : annotationAutoEnv.addConst annotationOptValue.name
    annotationOptValue.toVConstant = some (annotationOptBase.addDefEq annotationAutoValue.toDefEq) := by
  have hnone : annotationAutoEnv.constants annotationOptValue.name = none := by
    simp [VEnv.addDefEq, annotationAutoEnv, annotationOptBase, annotationAutoBase,
      annotationOptValue, annotationAutoValue, annotationSyntaxBase, annotationSyntaxValue, eq_comm]
  unfold VEnv.addConst
  rw [hnone]
  simp only [Option.some.injEq]
  apply VEnv.ext
  · funext n
    simp [VEnv.addDefEq, annotationOptBase, annotationAutoBase, annotationSyntaxBase,
      annotationOptValue, annotationAutoValue, annotationSyntaxValue, eq_comm]
    rfl
  · rfl

private theorem addAnnotationSemi : annotationOptEnv.addConst annotationSemiValue.name
    annotationSemiValue.toVConstant = some ((annotationSemiBase.addDefEq annotationAutoValue.toDefEq).addDefEq
      annotationOptValue.toDefEq) := by
  have hnone : annotationOptEnv.constants annotationSemiValue.name = none := by
    simp [VEnv.addDefEq, annotationOptEnv, annotationOptBase, annotationAutoBase, annotationSemiValue,
      annotationOptValue, annotationAutoValue, annotationSyntaxBase, annotationSyntaxValue, eq_comm]
  unfold VEnv.addConst
  rw [hnone]
  simp only [Option.some.injEq]
  apply VEnv.ext
  · funext n
    simp [VEnv.addDefEq, annotationSemiBase, annotationOptBase, annotationAutoBase, annotationSyntaxBase,
      annotationSemiValue, annotationOptValue, annotationAutoValue, annotationSyntaxValue, eq_comm]
    rfl
  · rfl

private theorem addAnnotationOut : annotationSemiEnv.addConst annotationOutValue.name
    annotationOutValue.toVConstant = some (((annotationBase.addDefEq annotationAutoValue.toDefEq).addDefEq
      annotationOptValue.toDefEq).addDefEq annotationSemiValue.toDefEq) := by
  have hnone : annotationSemiEnv.constants annotationOutValue.name = none := by
    simp [VEnv.addDefEq, annotationSemiEnv, annotationBase, annotationSemiBase, annotationOptBase,
      annotationAutoBase, annotationOutValue, annotationSemiValue, annotationOptValue, annotationAutoValue,
      annotationSyntaxBase, annotationSyntaxValue, eq_comm]
  unfold VEnv.addConst
  rw [hnone]
  simp only [Option.some.injEq]
  apply VEnv.ext
  · funext n
    simp [VEnv.addDefEq, annotationBase, annotationSemiBase, annotationOptBase, annotationAutoBase,
      annotationSyntaxBase, annotationOutValue, annotationSemiValue, annotationOptValue, annotationAutoValue,
      annotationSyntaxValue, eq_comm]
    rfl
  · rfl

private theorem annotationSyntaxWF : VConstant.WF VEnv.empty annotationSyntaxValue.toVConstant := by
  exact ⟨_, .sort (by decide)⟩

private theorem annotationAutoWF : annotationAutoValue.WF annotationSyntaxBase := by
  change annotationSyntaxBase.HasType 1 []
    ((VExpr.sort (.param 0)).lam ((VExpr.const ``Lean.Syntax []).lam (.bvar 1)))
    ((VExpr.sort (.param 0)).forallE ((VExpr.const ``Lean.Syntax []).forallE (.sort (.param 0))))
  apply VEnv.HasType.lam
  · exact VEnv.HasType.sort (by decide)
  · apply VEnv.HasType.lam (u := .succ .zero)
    · apply VEnv.HasType.const' (ci := annotationSyntaxValue.toVConstant)
      · simp [annotationSyntaxBase, annotationSyntaxValue, eq_comm]
      · intro l hl
        cases hl
      · rfl
      · rfl
    · exact VEnv.HasType.bvar (.succ .zero)

private theorem annotationOptWF : annotationOptValue.WF annotationAutoEnv := by
  change annotationAutoEnv.HasType 1 []
    ((VExpr.sort (.param 0)).lam ((VExpr.bvar 0).lam (VExpr.bvar 1)))
    ((VExpr.sort (.param 0)).forallE ((VExpr.bvar 0).forallE (.sort (.param 0))))
  type_tac

private theorem annotationSemiWF : annotationSemiValue.WF annotationOptEnv := by
  simp only [annotationSemiValue, unaryAnnotationDefinition]
  type_tac

private theorem annotationOutWF : annotationOutValue.WF annotationSemiEnv := by
  simp only [annotationOutValue, unaryAnnotationDefinition]
  type_tac

private theorem annotationEnv.wf : annotationEnv.WF := by
  refine ⟨[.def annotationOutValue, .def annotationSemiValue, .def annotationOptValue,
    .def annotationAutoValue, .axiom annotationSyntaxValue], ?_⟩
  refine .decl (.def (ci := annotationOutValue) annotationOutWF addAnnotationOut) ?_
  refine .decl (.def (ci := annotationSemiValue) annotationSemiWF addAnnotationSemi) ?_
  refine .decl (.def (ci := annotationOptValue) annotationOptWF addAnnotationOpt) ?_
  refine .decl (.def (ci := annotationAutoValue) annotationAutoWF addAnnotationAuto) ?_
  refine .decl ?_ (.empty : VEnv.WF' [] VEnv.empty)
  constructor
  · exact annotationSyntaxWF
  · exact addAnnotationSyntax

private theorem annotationEnv.eqCanonical : annotationEnv = canonicalAnnotationModel := by
  apply VEnv.ext
  · funext n
    simp [annotationEnv, annotationBase, annotationSemiBase, annotationOptBase, annotationAutoBase,
      annotationSyntaxBase, canonicalAnnotationModel, annotationOutValue, annotationSemiValue,
      annotationOptValue, annotationAutoValue, annotationSyntaxValue, eq_comm]
    rfl
  · funext definition
    simp [annotationEnv, annotationBase, VEnv.addDefEq, canonicalAnnotationModel, annotationOutValue, annotationSemiValue,
      annotationOptValue, annotationAutoValue]
    rfl

theorem canonicalAnnotationModel.wf : canonicalAnnotationModel.WF := by
  rw [← annotationEnv.eqCanonical]
  exact annotationEnv.wf

def canonicalBoolHeaderModel : VEnv :=
  (canonicalAnnotationModel.addInductHeaders boolInductDecl.types).getD canonicalAnnotationModel

theorem canonicalBoolHeaderModel.added :
    canonicalAnnotationModel.addInductHeaders boolInductDecl.types = some canonicalBoolHeaderModel := rfl

def canonicalBoolModel : VEnv :=
  (canonicalBoolHeaderModel.addConstructorHeaders
    (boolInductDecl.types.flatMap (fun type => type.ctors))).getD canonicalBoolHeaderModel

theorem canonicalBoolModel.added :
    canonicalBoolHeaderModel.addConstructorHeaders
      (boolInductDecl.types.flatMap (fun type => type.ctors)) = some canonicalBoolModel := rfl

theorem canonicalBoolModel.wf : canonicalBoolModel.WF := by
  have headerWF : canonicalBoolHeaderModel.WF :=
    VEnv.addInductHeaders.wf canonicalAnnotationModel.wf
      (fun header hmem => (boolInductDecl.headersWF header hmem).2)
      canonicalBoolHeaderModel.added
  exact VEnv.addConstructorHeaders.wf headerWF
    (boolInductDecl.constructorWF canonicalBoolHeaderModel.added) canonicalBoolModel.added

theorem canonicalBoolModel.constants :
    CanonicalAnnotationConstants canonicalBoolModel := by
  constructor <;> simp [canonicalBoolModel, canonicalBoolHeaderModel, canonicalAnnotationModel,
    VEnv.addInductHeaders, VEnv.addConstructorHeaders, VEnv.addConst, boolInductDecl]

theorem canonicalBoolModel.definitions :
    CanonicalAnnotationDefinitions canonicalBoolModel := by
  constructor <;> simp [canonicalBoolModel, canonicalBoolHeaderModel, canonicalAnnotationModel,
    VEnv.addInductHeaders, VEnv.addConstructorHeaders, VEnv.addConst, boolInductDecl]

theorem canonicalBoolModel.headers :
    (canonicalBoolModel : VEnv).constants ``Bool = some
        ({ uvars := 0, type := .sort (.succ .zero) } : VConstant) ∧
      (canonicalBoolModel : VEnv).constants ``Bool.false = some
        ({ uvars := 0, type := .const ``Bool [] } : VConstant) ∧
      (canonicalBoolModel : VEnv).constants ``Bool.true = some
        ({ uvars := 0, type := .const ``Bool [] } : VConstant) := by
  constructor
  · rfl
  constructor <;> rfl

/- The native recursor worker chooses either `.zero` or a fresh parameter.  The
   generic elimination-level proof specializes directly to the parameter-free
   canonical context, so callers can obtain the exact `VLevel` mapping once
   they retain the successful `getElimLevel` result. -/
theorem canonicalEliminationLevelMapping
    {stats : InductiveStats} {types : Array InductiveType} {reader : AddInductive.Context}
    {level : Level} (lparams : reader.lparams = [])
    (result : getElimLevel stats types reader = .ok level) :
    (getRecLevelParams level reader.lparams).Nodup ∧
      VLevel.ofLevel (getRecLevelParams level reader.lparams) level =
        some (if level.isParam then .param 0 else .zero) := by
  apply (getElimLevel.recLevelParams stats types reader (by simp [lparams])) level
  exact result

end Lean4Lean
