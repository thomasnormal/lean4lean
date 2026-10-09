import Lean4Lean.Verify.InductiveAnnotationSemantics
import Lean4Lean.Inductive.Annotation

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def SourceHasType (translation : Expr → VExpr → Prop) (env : VEnv) (uvars : Nat)
    (context : List VExpr) (source : Expr) (type : VExpr) : Prop :=
  ∃ semantic, translation source semantic ∧ env.HasType uvars context semantic type

inductive TypedAnnotationSpine (translation : Expr → VExpr → Prop) (env : VEnv)
    (uvars : Nat) (context : List VExpr) : Expr → VExpr → VLevel → Prop where
  | base {source semantic level}
      (unchanged : peelTypeAnnotations source = source)
      (translated : translation source semantic)
      (typed : env.HasType uvars context semantic (.sort level)) :
      TypedAnnotationSpine translation env uvars context source semantic level
  | outParam {sourceCarrier carrier level} (sourceLevel : Level)
      (levelWF : level.WF uvars)
      (translated : translation (.app (.const ``_root_.outParam [sourceLevel]) sourceCarrier)
        (.app (.const ``_root_.outParam [level]) carrier))
      (carrierSpine : TypedAnnotationSpine translation env uvars context sourceCarrier carrier level) :
      TypedAnnotationSpine translation env uvars context
        (.app (.const ``_root_.outParam [sourceLevel]) sourceCarrier)
        (.app (.const ``_root_.outParam [level]) carrier) level
  | semiOutParam {sourceCarrier carrier level} (sourceLevel : Level)
      (levelWF : level.WF uvars)
      (translated : translation (.app (.const ``_root_.semiOutParam [sourceLevel]) sourceCarrier)
        (.app (.const ``_root_.semiOutParam [level]) carrier))
      (carrierSpine : TypedAnnotationSpine translation env uvars context sourceCarrier carrier level) :
      TypedAnnotationSpine translation env uvars context
        (.app (.const ``_root_.semiOutParam [sourceLevel]) sourceCarrier)
        (.app (.const ``_root_.semiOutParam [level]) carrier) level
  | optParam {sourceCarrier carrier sourceExtra extra level} (sourceLevel : Level)
      (levelWF : level.WF uvars)
      (translated : translation
        (.app (.app (.const ``_root_.optParam [sourceLevel]) sourceCarrier) sourceExtra)
        (.app (.app (.const ``_root_.optParam [level]) carrier) extra))
      (extraTyped : env.HasType uvars context extra carrier)
      (carrierSpine : TypedAnnotationSpine translation env uvars context sourceCarrier carrier level) :
      TypedAnnotationSpine translation env uvars context
        (.app (.app (.const ``_root_.optParam [sourceLevel]) sourceCarrier) sourceExtra)
        (.app (.app (.const ``_root_.optParam [level]) carrier) extra) level
  | autoParam {sourceCarrier carrier sourceExtra extra level} (sourceLevel : Level)
      (levelWF : level.WF uvars)
      (translated : translation
        (.app (.app (.const ``_root_.autoParam [sourceLevel]) sourceCarrier) sourceExtra)
        (.app (.app (.const ``_root_.autoParam [level]) carrier) extra))
      (extraTyped : env.HasType uvars context extra (.const ``Lean.Syntax []))
      (carrierSpine : TypedAnnotationSpine translation env uvars context sourceCarrier carrier level) :
      TypedAnnotationSpine translation env uvars context
        (.app (.app (.const ``_root_.autoParam [sourceLevel]) sourceCarrier) sourceExtra)
        (.app (.app (.const ``_root_.autoParam [level]) carrier) extra) level

theorem TypedAnnotationSpine.translation {translation : Expr → VExpr → Prop} {env : VEnv}
    {uvars : Nat} {context : List VExpr} {source : Expr} {semantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine translation env uvars context source semantic level) :
    translation source semantic := by
  cases spine with
  | base _ translated _ => exact translated
  | outParam _ _ translated _ => exact translated
  | semiOutParam _ _ translated _ => exact translated
  | optParam _ _ translated _ _ => exact translated
  | autoParam _ _ translated _ _ => exact translated

theorem TypedAnnotationSpine.peelTypeAnnotations {translation : Expr → VExpr → Prop}
    {env : VEnv} {uvars : Nat} {context : List VExpr} {source : Expr} {semantic : VExpr}
    {level : VLevel}
    (spine : TypedAnnotationSpine translation env uvars context source semantic level)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered) :
    ∃ peeled, translation (AddInductive.peelTypeAnnotations source) peeled ∧
      env.IsDefEq uvars context semantic peeled (.sort level) := by
  induction spine with
  | base unchanged translated typed =>
    refine ⟨_, ?_, typed⟩
    rw [unchanged]
    exact translated
  | outParam sourceLevel levelWF _ _ carrierResult =>
    obtain ⟨peeled, translated, related⟩ := carrierResult
    refine ⟨peeled, ?_, ?_⟩
    · simpa only [AddInductive.peelTypeAnnotations, true_or, ↓reduceIte] using translated
    · exact (definitions.outParam_isDefEq levelWF related.hasType.1).trans related
  | semiOutParam sourceLevel levelWF _ _ carrierResult =>
    obtain ⟨peeled, translated, related⟩ := carrierResult
    refine ⟨peeled, ?_, ?_⟩
    · simpa only [AddInductive.peelTypeAnnotations, or_true, ↓reduceIte] using translated
    · exact (definitions.semiOutParam_isDefEq levelWF related.hasType.1).trans related
  | optParam sourceLevel levelWF _ extraTyped _ carrierResult =>
    obtain ⟨peeled, translated, related⟩ := carrierResult
    refine ⟨peeled, ?_, ?_⟩
    · simpa only [AddInductive.peelTypeAnnotations, true_or, ↓reduceIte] using translated
    · exact (definitions.optParam_isDefEq ordered levelWF related.hasType.1 extraTyped).trans related
  | autoParam sourceLevel levelWF _ extraTyped _ carrierResult =>
    obtain ⟨peeled, translated, related⟩ := carrierResult
    refine ⟨peeled, ?_, ?_⟩
    · simpa only [AddInductive.peelTypeAnnotations, or_true, ↓reduceIte] using translated
    · exact (definitions.autoParam_isDefEq ordered levelWF related.hasType.1 extraTyped).trans related

theorem TypedAnnotationSpine.peeledHasType {translation : Expr → VExpr → Prop} {env : VEnv}
    {uvars : Nat} {context : List VExpr} {source : Expr} {semantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine translation env uvars context source semantic level)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered) :
    SourceHasType translation env uvars context (AddInductive.peelTypeAnnotations source) (.sort level) := by
  obtain ⟨peeled, translated, related⟩ := spine.peelTypeAnnotations definitions ordered
  exact ⟨peeled, translated, related.hasType.2⟩

theorem TypedAnnotationSpine.sourceHasType {translation : Expr → VExpr → Prop} {env : VEnv}
    {uvars : Nat} {context : List VExpr} {source : Expr} {semantic : VExpr} {level : VLevel}
    (spine : TypedAnnotationSpine translation env uvars context source semantic level)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered) :
    SourceHasType translation env uvars context source (.sort level) := by
  obtain ⟨_, _, related⟩ := spine.peelTypeAnnotations definitions ordered
  exact ⟨semantic, spine.translation, related.hasType.1⟩

theorem TypedAnnotationSpine.inhabitantConversion {translation : Expr → VExpr → Prop}
    {env : VEnv} {uvars : Nat} {context : List VExpr} {source : Expr} {semantic inhabitant : VExpr}
    {level : VLevel}
    (spine : TypedAnnotationSpine translation env uvars context source semantic level)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered)
    (inhabitantTyped : env.HasType uvars context inhabitant semantic) :
    ∃ peeled, translation (AddInductive.peelTypeAnnotations source) peeled ∧
      env.HasType uvars context inhabitant peeled := by
  obtain ⟨peeled, translated, related⟩ := spine.peelTypeAnnotations definitions ordered
  exact ⟨peeled, translated, related.defeq inhabitantTyped⟩

end Lean4Lean.AddInductive
