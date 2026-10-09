import Lean4Lean.Verify.InductiveBinderPrefixes
import Lean4Lean.Verify.InductiveIndexRenaming

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem BinderDeclaredAt.fvar {ctx : Context} {value domain : Expr} {name : Name} {bi : BinderInfo}
    (declared : BinderDeclaredAt ctx value name domain bi) : ∃ id, value = .fvar id := by
  obtain ⟨decl, _, hexpr, _, _, _⟩ := declared
  exact ⟨decl.fvarId, hexpr.symm⟩

inductive BinderIndexCorrespondence :
    List (FVarId × FVarId) → List BinderStep → List BinderStep → List (FVarId × FVarId) → Prop where
  | nil (pairs : List (FVarId × FVarId)) : BinderIndexCorrespondence pairs [] [] pairs
  | parameter {pairs finalPairs : List (FVarId × FVarId)} {left right : List BinderStep}
      (name : Name) (bi : BinderInfo) (leftDomain rightDomain value : Expr)
      (rawDomain : IndexRenaming pairs leftDomain rightDomain)
      (localDomain : ConsumedIndexRenaming pairs leftDomain.consumeTypeAnnotations rightDomain.consumeTypeAnnotations)
      (tail : BinderIndexCorrespondence pairs left right finalPairs) :
      BinderIndexCorrespondence pairs
        ({ role := .parameter, name, domain := leftDomain, bi, value } :: left)
        ({ role := .parameter, name, domain := rightDomain, bi, value } :: right) finalPairs
  | index {pairs finalPairs : List (FVarId × FVarId)} {left right : List BinderStep}
      (name : Name) (bi : BinderInfo) (leftDomain rightDomain : Expr) (leftId rightId : FVarId)
      (rawDomain : IndexRenaming pairs leftDomain rightDomain)
      (localDomain : ConsumedIndexRenaming pairs leftDomain.consumeTypeAnnotations rightDomain.consumeTypeAnnotations)
      (tail : BinderIndexCorrespondence (pairs ++ [(leftId, rightId)]) left right finalPairs) :
      BinderIndexCorrespondence pairs
        ({ role := .index, name, domain := leftDomain, bi, value := .fvar leftId } :: left)
        ({ role := .index, name, domain := rightDomain, bi, value := .fvar rightId } :: right) finalPairs

theorem BinderIndexCorrespondence.finalPairs {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderIndexCorrespondence pairs left right finalPairs) :
    finalPairs = pairs ++ List.zip
      ((BinderStep.indexValues left).map Expr.fvarId!) ((BinderStep.indexValues right).map Expr.fvarId!) := by
  induction correspondence with
  | nil pairs => exact (List.append_nil pairs).symm
  | parameter name bi leftDomain rightDomain value rawDomain localDomain tail ih =>
    simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain localDomain tail ih =>
    simpa only [BinderStep.indexValues, ↓reduceIte, List.map_cons, Expr.fvarId!,
      List.zip_cons_cons, List.append_assoc, List.singleton_append] using ih

private theorem indexDeclaredTail {ctx : Context} {step : BinderStep} {steps : List BinderStep}
    (declared : BinderStepsIndexDeclared ctx (step :: steps)) : BinderStepsIndexDeclared ctx steps :=
  fun next hnext hrole => declared next (List.mem_cons_of_mem step hnext) hrole

theorem OpenedTelescope.relatedIndexCorrespondence {pairs : List (FVarId × FVarId)}
    {leftType rightType leftTerminal rightTerminal : Expr} {left right : List BinderStep}
    {leftCtx rightCtx : Context} (leftOpened : OpenedTelescope leftType left leftTerminal)
    (rightOpened : OpenedTelescope rightType right rightTerminal)
    (related : IndexRenaming pairs leftType rightType)
    (hroles : left.map BinderStep.role = right.map BinderStep.role)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right)
    (leftDeclared : BinderStepsIndexDeclared leftCtx left)
    (rightDeclared : BinderStepsIndexDeclared rightCtx right) :
    ∃ finalPairs, BinderIndexCorrespondence pairs left right finalPairs ∧
      IndexRenaming finalPairs leftTerminal rightTerminal := by
  induction leftOpened generalizing pairs rightType right rightTerminal with
  | sort level =>
    cases related with
    | sort level =>
      cases rightOpened
      exact ⟨pairs, .nil pairs, .sort level⟩
  | @bind role name domain bi value body terminal steps opened ih =>
    cases rightOpened with
    | sort level => cases related
    | @bind rightRole rightName rightDomain rightBi rightValue rightBody rightTerminal rightSteps rightOpened =>
      cases related with
      | forallE name bi domains bodies =>
        simp only [List.map_cons, List.cons.injEq] at hroles
        obtain ⟨hrole, hroles⟩ := hroles
        subst rightRole
        cases role with
        | parameter =>
          simp only [BinderStep.parameterValues, ↓reduceIte, List.cons.injEq] at hparams
          obtain ⟨hvalue, hparams⟩ := hparams
          subst rightValue
          obtain ⟨finalPairs, tail, hterminal⟩ := ih rightOpened
            (bodies.instantiate1 (IndexRenaming.refl pairs value)) hroles hparams
            (indexDeclaredTail leftDeclared) (indexDeclaredTail rightDeclared)
          exact ⟨finalPairs, .parameter name bi domain rightDomain value domains (.ofRaw domains) tail,
            hterminal⟩
        | index =>
          change BinderStep.parameterValues steps = BinderStep.parameterValues rightSteps at hparams
          obtain ⟨leftId, hleftValue⟩ := (leftDeclared _ (List.mem_cons_self ..) rfl).fvar
          obtain ⟨rightId, hrightValue⟩ := (rightDeclared _ (List.mem_cons_self ..) rfl).fvar
          change value = .fvar leftId at hleftValue
          change rightValue = .fvar rightId at hrightValue
          subst value rightValue
          have hextended : pairs ⊆ pairs ++ [(leftId, rightId)] := List.subset_append_left _ _
          have hvalues : IndexRenaming (pairs ++ [(leftId, rightId)]) (.fvar leftId) (.fvar rightId) :=
            .fvar (.inr (List.mem_append_right _ (List.mem_cons_self ..)))
          obtain ⟨finalPairs, tail, hterminal⟩ := ih rightOpened
            ((bodies.mono hextended).instantiate1 hvalues) hroles hparams
            (indexDeclaredTail leftDeclared) (indexDeclaredTail rightDeclared)
          exact ⟨finalPairs, .index name bi domain rightDomain leftId rightId domains (.ofRaw domains) tail,
            hterminal⟩

theorem OpenedTelescope.pairedIndices {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} {leftCtx rightCtx : Context}
    (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal)
    (hroles : left.map BinderStep.role = right.map BinderStep.role)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right)
    (leftDeclared : BinderStepsIndexDeclared leftCtx left)
    (rightDeclared : BinderStepsIndexDeclared rightCtx right) :
    ∃ pairs, BinderIndexCorrespondence [] left right pairs ∧
      pairs = List.zip ((BinderStep.indexValues left).map Expr.fvarId!)
        ((BinderStep.indexValues right).map Expr.fvarId!) ∧
      IndexRenaming pairs leftTerminal rightTerminal := by
  obtain ⟨pairs, correspondence, hterminal⟩ := leftOpened.relatedIndexCorrespondence rightOpened
    (IndexRenaming.refl [] type) hroles hparams leftDeclared rightDeclared
  exact ⟨pairs, correspondence, by simpa only [List.nil_append] using correspondence.finalPairs, hterminal⟩

theorem OpenedTelescope.indexCorrespondence {type leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} {leftCtx rightCtx : Context}
    (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal)
    (hroles : left.map BinderStep.role = right.map BinderStep.role)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right)
    (leftDeclared : BinderStepsIndexDeclared leftCtx left)
    (rightDeclared : BinderStepsIndexDeclared rightCtx right) :
    ∃ pairs, BinderIndexCorrespondence [] left right pairs := by
  obtain ⟨pairs, correspondence, _, _⟩ := leftOpened.pairedIndices rightOpened hroles hparams
    leftDeclared rightDeclared
  exact ⟨pairs, correspondence⟩

end Lean4Lean.AddInductive
