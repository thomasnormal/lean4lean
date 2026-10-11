import Lean4Lean.Verify.InductiveHeaderNormalizationTransport

namespace Lean4Lean
open Lean hiding Environment Exception

theorem HeaderAxiomLookupAgreement.stableInductiveParent
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (parent : Name) (header : InductiveVal)
    (present : shadow.find? parent = some (.inductInfo header)) : actual.find? parent = shadow.find? parent := by
  rcases agreement parent with same | ⟨_, changedHeader, _, shadowLookup⟩
  · exact same
  · rw [shadowLookup] at present
    dsimp only [headerAxiomInfo] at present
    cases Option.some.inj present

theorem HeaderAxiomLookupAgreement.stableOriginalInductiveParent
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (frame : NativeValueFrame original shadow)
    (parent : Name) (header : InductiveVal) (present : original.constants.find? parent = some (.inductInfo header)) :
    actual.find? parent = shadow.find? parent := by
  apply agreement.stableInductiveParent parent header
  simpa only [Kernel.Environment.find?, frame.map_wf.find?'_eq_find?] using frame.lookups present

theorem HeaderAxiomLookupAgreement.structureLike
    (_agreement : HeaderAxiomLookupAgreement changed actual shadow) (parent : Name)
    (stable : actual.find? parent = shadow.find? parent) : actual.isStructureLike parent = shadow.isStructureLike parent := by
  simp only [Kernel.Environment.isStructureLike, stable]

theorem HeaderAxiomLookupAgreement.firstConstructor
    (_agreement : HeaderAxiomLookupAgreement changed actual shadow) (parent : Name)
    (stable : actual.find? parent = shadow.find? parent) : getFirstCtor actual parent = getFirstCtor shadow parent := by
  simp only [getFirstCtor, stable]

theorem HeaderAxiomLookupAgreement.nullaryConstructor
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (type : Expr) (parameters : Nat)
    (stable : actual.find? type.getAppFn.constName! = shadow.find? type.getAppFn.constName!) :
    mkNullaryCtor actual type parameters = mkNullaryCtor shadow type parameters := by
  unfold mkNullaryCtor
  conv => lhs; rw [Expr.withApp_getAppFn]
  conv => rhs; rw [Expr.withApp_getAppFn]
  apply Expr.withApp_rel
  intro head arguments
  cases found : type.getAppFn <;> try rfl
  rename_i parent levels
  have same := agreement.firstConstructor parent (by simpa only [found, Expr.constName!] using stable)
  dsimp only
  rw [same]

theorem HeaderAxiomLookupAgreement.structureExpansion
    (agreement : HeaderAxiomLookupAgreement changed actual shadow) (type expression : Expr)
    (stable : actual.find? type.getAppFn.constName! = shadow.find? type.getAppFn.constName!) :
    expandEtaStruct actual type expression = expandEtaStruct shadow type expression := by
  unfold expandEtaStruct
  conv => lhs; rw [Expr.withApp_getAppFn]
  conv => rhs; rw [Expr.withApp_getAppFn]
  apply Expr.withApp_rel
  intro head arguments
  cases found : type.getAppFn <;> try rfl
  rename_i parent levels
  have same := agreement.firstConstructor parent (by simpa only [found, Expr.constName!] using stable)
  dsimp only
  rw [same]
  cases first : getFirstCtor shadow parent with
  | none => rfl
  | some constructor =>
    dsimp only
    rcases agreement constructor with sameLookup | ⟨_, header, actualLookup, shadowLookup⟩
    · rw [sameLookup]
    · rw [actualLookup, shadowLookup]
      rfl

theorem toCtorWhenStruct.headerAxiomNormalizationTransport
    (normalize : Expr → TypeChecker.RecM Expr)
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (expression : Expr)
    (stable : actualContext.env.find? parent = shadowContext.env.find? parent)
    (typeNormalization : actualContext.env.isStructureLike parent = true →
      (expression.isConstructorApp?' actualContext.env).isSome = false →
      TypeChecker.M.SuccessTransport
        ((do normalize (← TypeChecker.Inner.inferType expression true)) actualMethods)
        ((do normalize (← TypeChecker.Inner.inferType expression true)) shadowMethods) actualContext shadowContext state)
    (sortNormalization : actualContext.env.isStructureLike parent = true →
      (expression.isConstructorApp?' actualContext.env).isSome = false → ∀ type finalState,
      ((do normalize (← TypeChecker.Inner.inferType expression true)) actualMethods) actualContext state = .ok (type, finalState) →
      type.getAppFn.isConstOf parent = true → TypeChecker.M.SuccessTransport
        ((do normalize (← TypeChecker.Inner.inferType type true)) actualMethods)
        ((do normalize (← TypeChecker.Inner.inferType type true)) shadowMethods) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport
      (toCtorWhenStruct actualContext.env normalize TypeChecker.Inner.inferType parent expression actualMethods)
      (toCtorWhenStruct shadowContext.env normalize TypeChecker.Inner.inferType parent expression shadowMethods)
      actualContext shadowContext state := by
  have structureSame := agreement.structureLike parent stable
  have constructorSame := agreement.constructorApp expression
  unfold toCtorWhenStruct
  rw [← structureSame, ← constructorSame]
  by_cases structureLike : actualContext.env.isStructureLike parent = true
  · by_cases constructor : (expression.isConstructorApp?' actualContext.env).isSome = true
    · simp only [structureLike, constructor, Bool.not_true, Bool.false_or, if_true]
      exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    · have notConstructor : (expression.isConstructorApp?' actualContext.env).isSome = false :=
        Bool.eq_false_iff.mpr constructor
      simp only [structureLike, notConstructor, Bool.not_true, Bool.false_or, Bool.false_eq_true, if_false]
      simp only [pure_bind, ← bind_assoc]
      dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind,
        TypeChecker.Inner.inferType, TypeChecker.Inner.whnf]
      apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ (typeNormalization structureLike notConstructor)
      intro type finalState accepted
      by_cases matching : type.getAppFn.isConstOf parent = true
      · simp only [matching, Bool.not_true, Bool.false_eq_true, if_false]
        try simp only [pure_bind, ← bind_assoc]
        dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.pure, Except.pure, Except.bind,
          TypeChecker.Inner.inferType, TypeChecker.Inner.whnf]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (sortNormalization structureLike notConstructor type finalState accepted matching)
        intro sort normalizedState _
        have parentName : type.getAppFn.constName! = parent := by
          cases found : type.getAppFn <;> simp only [found, Expr.isConstOf, Bool.false_eq_true] at matching
          rename_i name levels
          simpa only [Expr.constName!, beq_iff_eq] using matching
        have expansionSame := agreement.structureExpansion type expression (by simpa only [parentName] using stable)
        rw [expansionSame]
        cases sorted : sort == Expr.prop <;> intro result acceptedResult <;> exact acceptedResult
      · have notMatching := Bool.eq_false_iff.mpr matching
        simp only [notMatching, Bool.not_false, if_true]
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  · have notStructure := Bool.eq_false_iff.mpr structureLike
    simp only [notStructure, Bool.not_false, Bool.true_or, if_true]
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem toCtorWhenStruct.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (parent : Name) (expression : Expr)
    (stable : actualContext.env.find? parent = shadowContext.env.find? parent)
    (typeNormalization : actualContext.env.isStructureLike parent = true →
      (expression.isConstructorApp?' actualContext.env).isSome = false →
      TypeChecker.M.SuccessTransport
        (do actualMethods.whnf (← actualMethods.inferType expression true))
        (do shadowMethods.whnf (← shadowMethods.inferType expression true)) actualContext shadowContext state)
    (sortNormalization : actualContext.env.isStructureLike parent = true →
      (expression.isConstructorApp?' actualContext.env).isSome = false → ∀ type finalState,
      (do actualMethods.whnf (← actualMethods.inferType expression true)) actualContext state = .ok (type, finalState) →
      type.getAppFn.isConstOf parent = true → TypeChecker.M.SuccessTransport
        (do actualMethods.whnf (← actualMethods.inferType type true))
        (do shadowMethods.whnf (← shadowMethods.inferType type true)) actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport
      (toCtorWhenStruct actualContext.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType parent expression actualMethods)
      (toCtorWhenStruct shadowContext.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType parent expression shadowMethods)
      actualContext shadowContext state :=
  toCtorWhenStruct.headerAxiomNormalizationTransport TypeChecker.Inner.whnf
    actualMethods shadowMethods actualContext shadowContext agreement state parent expression stable typeNormalization sortNormalization

theorem toCtorWhenK.headerAxiomNormalizationTransport
    (normalize : Expr → TypeChecker.RecM Expr)
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (info : RecursorVal) (expression : Expr)
    (isK : info.k = true)
    (stable : actualContext.env.find? info.getMajorInduct = shadowContext.env.find? info.getMajorInduct)
    (typeNormalization : TypeChecker.M.SuccessTransport
      ((do normalize (← TypeChecker.Inner.inferType expression true)) actualMethods)
      ((do normalize (← TypeChecker.Inner.inferType expression true)) shadowMethods) actualContext shadowContext state)
    (constructorComparison : ∀ type finalState constructor,
      ((do normalize (← TypeChecker.Inner.inferType expression true)) actualMethods) actualContext state = .ok (type, finalState) →
      type.getAppFn.constName! = info.getMajorInduct → mkNullaryCtor actualContext.env type info.numParams = some constructor →
      TypeChecker.M.SuccessTransport
        (do TypeChecker.Inner.isDefEq type (← actualMethods.inferType constructor true) actualMethods)
        (do TypeChecker.Inner.isDefEq type (← shadowMethods.inferType constructor true) shadowMethods)
        actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport
      (toCtorWhenK actualContext.env normalize TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
        info expression actualMethods)
      (toCtorWhenK shadowContext.env normalize TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
        info expression shadowMethods) actualContext shadowContext state := by
  unfold toCtorWhenK
  simp only [isK, if_true, pure_bind, ← bind_assoc]
  dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType, TypeChecker.Inner.whnf]
  apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _ typeNormalization
  intro type finalState accepted
  cases found : type.getAppFn <;> try exact TypeChecker.M.SuccessTransport.pure _ _ _ _
  rename_i parent levels
  by_cases matching : parent = info.getMajorInduct
  · subst parent
    simp only [bne_iff_ne, ne_self_iff_false, if_false]
    have parentName : type.getAppFn.constName! = info.getMajorInduct := by simp only [found, Expr.constName!]
    have constructorSame := agreement.nullaryConstructor type info.numParams (by simpa only [parentName] using stable)
    have finish : TypeChecker.M.SuccessTransport
        ((match mkNullaryCtor actualContext.env type info.numParams with
          | some constructor => do
            let equal ← ReaderT.bind (TypeChecker.Inner.inferType constructor) (TypeChecker.Inner.isDefEq type)
            pure (if equal then constructor else expression)
          | none => pure expression) actualMethods)
        ((match mkNullaryCtor shadowContext.env type info.numParams with
          | some constructor => do
            let equal ← ReaderT.bind (TypeChecker.Inner.inferType constructor) (TypeChecker.Inner.isDefEq type)
            pure (if equal then constructor else expression)
          | none => pure expression) shadowMethods) actualContext shadowContext finalState := by
      rw [← constructorSame]
      cases selected : mkNullaryCtor actualContext.env type info.numParams with
      | none => exact TypeChecker.M.SuccessTransport.pure _ _ _ _
      | some constructor =>
        dsimp only [Bind.bind, ReaderT.bind, TypeChecker.Inner.inferType]
        apply TypeChecker.M.SuccessTransport.bind _ _ _ _ _ _ _
          (constructorComparison type finalState constructor accepted parentName selected)
        intro equal comparedState _
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    by_cases metavariables : type.hasExprMVar = true
    · simp only [metavariables, if_true, Std.Legacy.Range.forIn'_eq_forIn'_range',
        ← apply_ite, List.forIn'_pure]
      generalize scan : (forIn' (m := Id) (_ : List Nat)
        (⟨none, PUnit.unit⟩ : MProd (Option Expr) PUnit) _) = scanned
      rcases scanned with ⟨result, ignored⟩
      cases result with
      | none =>
        rw [← constructorSame] at finish ⊢
        cases chosen : mkNullaryCtor actualContext.env type info.numParams <;> simp only [chosen] at finish ⊢
        all_goals
          dsimp only [Bind.bind, ReaderT.bind, Pure.pure, ReaderT.pure, StateT.pure, StateT.bind,
            Except.pure, Except.bind] at finish ⊢
          exact finish
      | some result =>
        exact TypeChecker.M.SuccessTransport.pure _ _ _ _
    · have noMetavariables := Bool.eq_false_iff.mpr metavariables
      simp only [noMetavariables, Bool.false_eq_true, if_false]
      simp only [← apply_ite]
      rw [← constructorSame] at finish ⊢
      cases chosen : mkNullaryCtor actualContext.env type info.numParams <;>
        (simp only [chosen] at finish ⊢; exact finish)
  · have different : (parent != info.getMajorInduct) = true := by simpa only [bne_iff_ne] using matching
    simp only [different, if_true]
    exact TypeChecker.M.SuccessTransport.pure _ _ _ _

theorem toCtorWhenK.headerAxiomTransport
    (actualMethods shadowMethods : TypeChecker.Methods) (actualContext shadowContext : TypeChecker.Context)
    (agreement : HeaderAxiomLookupAgreement changed actualContext.env shadowContext.env)
    (state : TypeChecker.State) (info : RecursorVal) (expression : Expr)
    (isK : info.k = true)
    (stable : actualContext.env.find? info.getMajorInduct = shadowContext.env.find? info.getMajorInduct)
    (typeNormalization : TypeChecker.M.SuccessTransport
      (do actualMethods.whnf (← actualMethods.inferType expression true))
      (do shadowMethods.whnf (← shadowMethods.inferType expression true)) actualContext shadowContext state)
    (constructorComparison : ∀ type finalState constructor,
      (do actualMethods.whnf (← actualMethods.inferType expression true)) actualContext state = .ok (type, finalState) →
      type.getAppFn.constName! = info.getMajorInduct → mkNullaryCtor actualContext.env type info.numParams = some constructor →
      TypeChecker.M.SuccessTransport
        (do TypeChecker.Inner.isDefEq type (← actualMethods.inferType constructor true) actualMethods)
        (do TypeChecker.Inner.isDefEq type (← shadowMethods.inferType constructor true) shadowMethods)
        actualContext shadowContext finalState) :
    TypeChecker.M.SuccessTransport
      (toCtorWhenK actualContext.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
        info expression actualMethods)
      (toCtorWhenK shadowContext.env TypeChecker.Inner.whnf TypeChecker.Inner.inferType TypeChecker.Inner.isDefEq
        info expression shadowMethods) actualContext shadowContext state :=
  toCtorWhenK.headerAxiomNormalizationTransport TypeChecker.Inner.whnf
    actualMethods shadowMethods actualContext shadowContext agreement state info expression isK stable typeNormalization constructorComparison

end Lean4Lean
