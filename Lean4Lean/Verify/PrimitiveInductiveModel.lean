import Lean4Lean.Verify.InductiveAnnotationTranslation
import Lean4Lean.Verify.ConstructorHeaders
import Lean4Lean.Verify.InductiveEliminationLevel
import Lean4Lean.Theory.InductiveHeaders

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
