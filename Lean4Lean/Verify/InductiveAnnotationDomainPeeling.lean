import Lean4Lean.Verify.InductiveAnnotationTranslation

namespace Lean4Lean
open Lean hiding Environment Exception
open AddInductive
open private annotationArgument_hasType peelTypeAnnotations_unchanged
  from Lean4Lean.Verify.InductiveAnnotationTranslation

private theorem annotationLevels_ofArity {universes : List Name} {levels : List Level}
    {semanticLevels : List VLevel}
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = 1) :
    ∃ level, semanticLevels = [level] ∧ level.WF universes.length := by
  have lengths := (List.mapM_eq_some.mp mapped).length_eq
  obtain ⟨level, semanticSingleton⟩ := List.length_eq_one_iff.mp (lengths.symm.trans arity)
  exact ⟨level, semanticSingleton,
    VLevel.WF.of_mapM_ofLevel mapped level (by simp only [semanticSingleton, List.mem_singleton])⟩

theorem TrExprS.peeledDomain {env : VEnv} {universes : List Name} {context : VLCtx}
    {source : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF) (contextWF : OnCtx context.toCtx (env.IsType universes.length))
    (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (translated : TrExprS env universes context source semantic)
    (typed : env.HasType universes.length context.toCtx semantic (.sort level)) :
    ∃ peeled, TrExprS env universes context (peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) := by
  induction source using AddInductive.peelTypeAnnotations.induct generalizing semantic level with
  | case1 name levels carrier recognized carrierInduction =>
    cases translated with
    | app functionTyped carrierTyped functionTranslated carrierTranslated =>
      cases functionTranslated with
      | const lookup mapped arity =>
        rcases recognized with recognized | recognized
        · subst name
          have arityOne : levels.length = 1 := by
            simpa only [Option.some.inj (lookup.symm.trans constants.outParam)] using arity
          obtain ⟨annotationLevel, semanticLevels, levelWF⟩ := annotationLevels_ofArity mapped arityOne
          cases semanticLevels
          have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.outParam
            (ls := [annotationLevel])
            (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
          simp only [unaryAnnotationDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
          have carrierTyping := annotationArgument_hasType envWF contextWF
            functionTyped canonicalTyped carrierTyped
          obtain ⟨peeled, peeledTranslated, carrierEquality⟩ :=
            carrierInduction carrierTranslated carrierTyping
          refine ⟨peeled, ?_, ?_⟩
          · simpa only [AddInductive.peelTypeAnnotations, ↓reduceIte] using peeledTranslated
          · exact ((definitions.outParam_isDefEq levelWF carrierTyping).trans
              carrierEquality).toU.of_l envWF contextWF typed
        · subst name
          have arityOne : levels.length = 1 := by
            simpa only [Option.some.inj (lookup.symm.trans constants.semiOutParam)] using arity
          obtain ⟨annotationLevel, semanticLevels, levelWF⟩ := annotationLevels_ofArity mapped arityOne
          cases semanticLevels
          have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.semiOutParam
            (ls := [annotationLevel])
            (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
          simp only [unaryAnnotationDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
          have carrierTyping := annotationArgument_hasType envWF contextWF
            functionTyped canonicalTyped carrierTyped
          obtain ⟨peeled, peeledTranslated, carrierEquality⟩ :=
            carrierInduction carrierTranslated carrierTyping
          refine ⟨peeled, ?_, ?_⟩
          · simpa only [AddInductive.peelTypeAnnotations, ↓reduceIte] using peeledTranslated
          · exact ((definitions.semiOutParam_isDefEq levelWF carrierTyping).trans
              carrierEquality).toU.of_l envWF contextWF typed
  | case2 name levels carrier unrecognized =>
    exact ⟨_, by simpa only [AddInductive.peelTypeAnnotations, unrecognized, ↓reduceIte] using translated, typed⟩
  | case3 name levels carrier extra recognized carrierInduction =>
    cases translated with
    | app functionTyped extraTyped functionTranslated extraTranslated =>
      cases functionTranslated with
      | app innerFunctionTyped carrierTyped innerFunctionTranslated carrierTranslated =>
        cases innerFunctionTranslated with
        | const lookup mapped arity =>
          rcases recognized with recognized | recognized
          · subst name
            have arityOne : levels.length = 1 := by
              simpa only [Option.some.inj (lookup.symm.trans constants.optParam)] using arity
            obtain ⟨annotationLevel, semanticLevels, levelWF⟩ := annotationLevels_ofArity mapped arityOne
            cases semanticLevels
            have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.optParam
              (ls := [annotationLevel])
              (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
            simp only [optParamDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero] at canonicalTyped
            have carrierTyping := annotationArgument_hasType envWF contextWF
              innerFunctionTyped canonicalTyped carrierTyped
            have canonicalApplied := canonicalTyped.app carrierTyping
            simp [VExpr.inst, VExpr.instVar] at canonicalApplied
            have extraTyping := annotationArgument_hasType envWF contextWF
              functionTyped canonicalApplied extraTyped
            obtain ⟨peeled, peeledTranslated, carrierEquality⟩ :=
              carrierInduction carrierTranslated carrierTyping
            refine ⟨peeled, ?_, ?_⟩
            · simpa only [AddInductive.peelTypeAnnotations, ↓reduceIte] using peeledTranslated
            · exact ((definitions.optParam_isDefEq envWF.ordered levelWF carrierTyping
                extraTyping).trans carrierEquality).toU.of_l envWF contextWF typed
          · subst name
            have arityOne : levels.length = 1 := by
              simpa only [Option.some.inj (lookup.symm.trans constants.autoParam)] using arity
            obtain ⟨annotationLevel, semanticLevels, levelWF⟩ := annotationLevels_ofArity mapped arityOne
            cases semanticLevels
            have canonicalTyped := VEnv.HasType.const (Γ := context.toCtx) constants.autoParam
              (ls := [annotationLevel])
              (by simpa only [List.mem_singleton] using fun _ equality => equality ▸ levelWF) rfl
            simp only [autoParamDefinition, VExpr.instL, VLevel.inst, List.getD_cons_zero, List.map_nil] at canonicalTyped
            have carrierTyping := annotationArgument_hasType envWF contextWF
              innerFunctionTyped canonicalTyped carrierTyped
            have canonicalApplied := canonicalTyped.app carrierTyping
            simp only [VExpr.inst] at canonicalApplied
            have extraTyping := annotationArgument_hasType envWF contextWF
              functionTyped canonicalApplied extraTyped
            obtain ⟨peeled, peeledTranslated, carrierEquality⟩ :=
              carrierInduction carrierTranslated carrierTyping
            refine ⟨peeled, ?_, ?_⟩
            · simpa only [AddInductive.peelTypeAnnotations, ↓reduceIte] using peeledTranslated
            · exact ((definitions.autoParam_isDefEq envWF.ordered levelWF carrierTyping
                extraTyping).trans carrierEquality).toU.of_l envWF contextWF typed
  | case4 name levels carrier extra unrecognized =>
    exact ⟨_, by simpa only [AddInductive.peelTypeAnnotations, unrecognized, ↓reduceIte] using translated, typed⟩
  | case5 expression notUnary notBinary =>
    exact ⟨_, by simpa only [peelTypeAnnotations_unchanged notUnary notBinary] using translated, typed⟩

theorem TrExprS.peeledDomainHasType {env : VEnv} {universes : List Name} {context : VLCtx}
    {source : Expr} {semantic : VExpr} {level : VLevel}
    (envWF : env.WF) (contextWF : OnCtx context.toCtx (env.IsType universes.length))
    (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (translated : TrExprS env universes context source semantic)
    (typed : env.HasType universes.length context.toCtx semantic (.sort level)) :
    SourceHasType (TrExprS env universes context) env universes.length context.toCtx
      (peelTypeAnnotations source) (.sort level) := by
  obtain ⟨peeled, peeledTranslated, equality⟩ :=
    translated.peeledDomain envWF contextWF constants definitions typed
  exact ⟨peeled, peeledTranslated, equality.hasType.2⟩

theorem TrExprS.peeledAnonymousBodyTranslation {env : VEnv} {universes : List Name}
    {context : VLCtx} {source body : Expr} {semantic bodySemantic : VExpr} {level : VLevel}
    (envWF : env.WF) (contextWF : context.WF env universes.length)
    (constants : CanonicalAnnotationConstants env)
    (definitions : CanonicalAnnotationDefinitions env)
    (translated : TrExprS env universes context source semantic)
    (typed : env.HasType universes.length context.toCtx semantic (.sort level))
    (bodyTranslation : TrExprS env universes ((none, .vlam semantic) :: context) body bodySemantic) :
    ∃ peeled, TrExprS env universes context (peelTypeAnnotations source) peeled ∧
      env.IsDefEq universes.length context.toCtx semantic peeled (.sort level) ∧
      VLCtx.IsDefEq env universes.length ((none, .vlam semantic) :: context)
        ((none, .vlam peeled) :: context) ∧
      TrExpr env universes ((none, .vlam peeled) :: context) body bodySemantic := by
  obtain ⟨peeled, peeledTranslated, equality⟩ :=
    translated.peeledDomain envWF contextWF.toCtx constants definitions typed
  have contextEquality : VLCtx.IsDefEq env universes.length
      ((none, .vlam semantic) :: context) ((none, .vlam peeled) :: context) :=
    .cons (.refl envWF.ordered contextWF) nofun (.vlam equality)
  exact ⟨peeled, peeledTranslated, equality, contextEquality,
    bodyTranslation.defeqDFC' envWF contextEquality⟩

end Lean4Lean
