import Lean4Lean.Verify.InductiveIndexLookupOpening
import Lean4Lean.Verify.InductiveBinderCorrespondence

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

inductive BinderLookupCorrespondence :
    List (FVarId × FVarId) → List BinderStep → List BinderStep → List (FVarId × FVarId) → Prop where
  | nil (pairs : List (FVarId × FVarId)) : BinderLookupCorrespondence pairs [] [] pairs
  | parameter {pairs finalPairs : List (FVarId × FVarId)} {left right : List BinderStep}
      (name : Name) (bi : BinderInfo) (leftDomain rightDomain value : Expr)
      (rawDomain : IndexLookupRenaming pairs leftDomain rightDomain)
      (tail : BinderLookupCorrespondence pairs left right finalPairs) :
      BinderLookupCorrespondence pairs
        ({ role := .parameter, name, domain := leftDomain, bi, value } :: left)
        ({ role := .parameter, name, domain := rightDomain, bi, value } :: right) finalPairs
  | index {pairs finalPairs : List (FVarId × FVarId)} {left right : List BinderStep}
      (name : Name) (bi : BinderInfo) (leftDomain rightDomain : Expr) (leftId rightId : FVarId)
      (rawDomain : IndexLookupRenaming pairs leftDomain rightDomain)
      (tail : BinderLookupCorrespondence (pairs ++ [(leftId, rightId)]) left right finalPairs) :
      BinderLookupCorrespondence pairs
        ({ role := .index, name, domain := leftDomain, bi, value := .fvar leftId } :: left)
        ({ role := .index, name, domain := rightDomain, bi, value := .fvar rightId } :: right) finalPairs

theorem BinderLookupCorrespondence.toIndexCorrespondence {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs) :
    BinderIndexCorrespondence pairs left right finalPairs := by
  induction correspondence with
  | nil pairs => exact .nil pairs
  | parameter name bi leftDomain rightDomain value rawDomain tail ih =>
    exact .parameter name bi leftDomain rightDomain value rawDomain.related (.ofRaw rawDomain.related) ih
  | index name bi leftDomain rightDomain leftId rightId rawDomain tail ih =>
    exact .index name bi leftDomain rightDomain leftId rightId rawDomain.related (.ofRaw rawDomain.related) ih

theorem BinderLookupCorrespondence.finalPairs {pairs finalPairs : List (FVarId × FVarId)}
    {left right : List BinderStep} (correspondence : BinderLookupCorrespondence pairs left right finalPairs) :
    finalPairs = pairs ++ List.zip
      ((BinderStep.indexValues left).map Expr.fvarId!) ((BinderStep.indexValues right).map Expr.fvarId!) :=
  correspondence.toIndexCorrespondence.finalPairs

private theorem indexDeclaredTail {ctx : Context} {step : BinderStep} {steps : List BinderStep}
    (declared : BinderStepsIndexDeclared ctx (step :: steps)) : BinderStepsIndexDeclared ctx steps :=
  fun next hnext hrole => declared next (List.mem_cons_of_mem step hnext) hrole

private theorem withinMono {ids extended : List FVarId} {value : Expr}
    (within : IndexFVarsWithin ids value) (hids : ids ⊆ extended) : IndexFVarsWithin extended value :=
  IndexFVarsWithin.of_subset (List.Subset.trans (IndexFVarsWithin.iff_subset.mp within) hids)

private theorem withinInstantiateFVar {ids : List FVarId} {value : Expr} {id : FVarId}
    (within : IndexFVarsWithin ids value) (hmem : id ∈ ids) :
    IndexFVarsWithin ids (value.instantiate1 (.fvar id)) := by
  apply IndexFVarsWithin.of_subset
  intro next hnext
  rw [Expr.instantiate1_eq] at hnext
  obtain heq | hold := ElimNestedInductive.instantiate1_fvar_mem value id 0 next hnext
  · exact heq ▸ hmem
  · exact IndexFVarsWithin.iff_subset.mp within hold

private theorem sourceFresh {pairs rest : List (FVarId × FVarId)} {source target : FVarId}
    (injection : IndexPairInjection (pairs ++ (source, target) :: rest)) : source ∉ pairs.map Prod.fst := by
  have hdistinct : (pairs.map Prod.fst ++ source :: rest.map Prod.fst).Nodup := by
    simpa only [List.map_append, List.map_cons] using injection.1
  exact fun hmem => (List.nodup_append.mp hdistinct).2.2 source hmem source (List.mem_cons_self ..) rfl

theorem OpenedTelescope.relatedLookupIndexCorrespondence {pairs : List (FVarId × FVarId)}
    {params : List FVarId} {leftType rightType leftTerminal rightTerminal : Expr}
    {left right : List BinderStep} {leftCtx rightCtx : Context}
    (leftOpened : OpenedTelescope leftType left leftTerminal)
    (rightOpened : OpenedTelescope rightType right rightTerminal)
    (related : IndexLookupRenaming pairs leftType rightType)
    (hroles : left.map BinderStep.role = right.map BinderStep.role)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right)
    (leftDeclared : BinderStepsIndexDeclared leftCtx left)
    (rightDeclared : BinderStepsIndexDeclared rightCtx right)
    (injection : IndexPairInjection (pairs ++ List.zip
      ((BinderStep.indexValues left).map Expr.fvarId!) ((BinderStep.indexValues right).map Expr.fvarId!)))
    (support : IndexParameterSupport (pairs ++ List.zip
      ((BinderStep.indexValues left).map Expr.fvarId!) ((BinderStep.indexValues right).map Expr.fvarId!)) params)
    (shapes : ∀ value ∈ BinderStep.parameterValues left, ∃ id ∈ params, value = .fvar id)
    (within : IndexFVarsWithin (params ++ pairs.map Prod.fst) leftType) :
    ∃ finalPairs, BinderLookupCorrespondence pairs left right finalPairs ∧
      IndexLookupRenaming finalPairs leftTerminal rightTerminal := by
  induction leftOpened generalizing pairs rightType right rightTerminal with
  | sort level =>
    change Expr.sort level = rightType at related
    subst rightType
    cases rightOpened
    exact ⟨pairs, .nil pairs, rfl⟩
  | @bind role name domain bi value body terminal steps opened ih =>
    cases rightOpened with
    | sort level => cases related
    | @bind rightRole rightName rightDomain rightBi rightValue rightBody rightTerminal rightSteps rightOpened =>
      simp only [IndexLookupRenaming, indexRenameExpr, Expr.forallE.injEq] at related
      obtain ⟨rfl, hdomain, hbody, rfl⟩ := related
      simp only [List.map_cons, List.cons.injEq] at hroles
      obtain ⟨rfl, hroles⟩ := hroles
      cases role with
      | parameter =>
        simp only [BinderStep.parameterValues, ↓reduceIte, List.cons.injEq] at hparams
        obtain ⟨rfl, hparams⟩ := hparams
        obtain ⟨id, hid, rfl⟩ := shapes value (List.mem_cons_self ..)
        have hpairSupport : IndexParameterSupport pairs params := by
          intro next hnext hmem
          apply support next hnext
          rw [List.map_append]
          exact List.mem_append_left _ hmem
        have hnextWithin := withinInstantiateFVar within.2 (List.mem_append_left _ hid)
        obtain ⟨finalPairs, tail, hterminal⟩ := ih rightOpened
          ((show IndexLookupRenaming pairs body rightBody from hbody).instantiate1
            (.fixedParameter hpairSupport hid)) hroles hparams
          (indexDeclaredTail leftDeclared) (indexDeclaredTail rightDeclared)
          (by simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using injection)
          (by simpa only [BinderStep.indexValues, BinderRole.noConfusion, ↓reduceIte] using support)
          (fun next hnext => shapes next (List.mem_cons_of_mem _ hnext)) hnextWithin
        exact ⟨finalPairs, .parameter name bi domain rightDomain (.fvar id) hdomain tail, hterminal⟩
      | index =>
        change BinderStep.parameterValues steps = BinderStep.parameterValues rightSteps at hparams
        obtain ⟨leftId, hleftValue⟩ := (leftDeclared _ (List.mem_cons_self ..) rfl).fvar
        obtain ⟨rightId, hrightValue⟩ := (rightDeclared _ (List.mem_cons_self ..) rfl).fvar
        change value = .fvar leftId at hleftValue
        change rightValue = .fvar rightId at hrightValue
        subst value rightValue
        simp only [BinderStep.indexValues, ↓reduceIte, List.map_cons, Expr.fvarId!,
          List.zip_cons_cons] at injection support
        have hfresh := sourceFresh injection
        have hnotParam : leftId ∉ params := by
          intro hid
          exact support leftId hid (List.mem_map.mpr
            ⟨(leftId, rightId), List.mem_append_right _ (List.mem_cons_self ..), rfl⟩)
        have avoids := within.2.avoids (by simp only [List.mem_append]; exact not_or.mpr ⟨hnotParam, hfresh⟩)
        have hnextWithin : IndexFVarsWithin (params ++ (pairs ++ [(leftId, rightId)]).map Prod.fst)
            (body.instantiate1 (.fvar leftId)) := by
          apply withinInstantiateFVar (withinMono within.2 ?_) ?_
          · intro next hnext
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [← List.append_assoc]
            exact List.mem_append_left _ hnext
          · simp
        obtain ⟨finalPairs, tail, hterminal⟩ := ih rightOpened
          ((show IndexLookupRenaming pairs body rightBody from hbody).openFreshIndex avoids hfresh)
          hroles hparams (indexDeclaredTail leftDeclared) (indexDeclaredTail rightDeclared)
          (by simpa only [List.append_assoc, List.singleton_append] using injection)
          (by simpa only [List.append_assoc, List.singleton_append] using support) shapes hnextWithin
        exact ⟨finalPairs, .index name bi domain rightDomain leftId rightId hdomain tail, hterminal⟩

theorem OpenedTelescope.lookupIndexCorrespondence {params : List FVarId}
    {type leftTerminal rightTerminal : Expr} {left right : List BinderStep} {leftCtx rightCtx : Context}
    (leftOpened : OpenedTelescope type left leftTerminal)
    (rightOpened : OpenedTelescope type right rightTerminal)
    (hroles : left.map BinderStep.role = right.map BinderStep.role)
    (hparams : BinderStep.parameterValues left = BinderStep.parameterValues right)
    (leftDeclared : BinderStepsIndexDeclared leftCtx left)
    (rightDeclared : BinderStepsIndexDeclared rightCtx right)
    (injection : IndexPairInjection (List.zip ((BinderStep.indexValues left).map Expr.fvarId!)
      ((BinderStep.indexValues right).map Expr.fvarId!)))
    (support : IndexParameterSupport (List.zip ((BinderStep.indexValues left).map Expr.fvarId!)
      ((BinderStep.indexValues right).map Expr.fvarId!)) params)
    (shapes : ∀ value ∈ BinderStep.parameterValues left, ∃ id ∈ params, value = .fvar id)
    (within : IndexFVarsWithin params type) :
    ∃ pairs, BinderLookupCorrespondence [] left right pairs ∧
      pairs = List.zip ((BinderStep.indexValues left).map Expr.fvarId!)
        ((BinderStep.indexValues right).map Expr.fvarId!) ∧ IndexLookupRenaming pairs leftTerminal rightTerminal := by
  have hinitial : IndexLookupRenaming [] type type := indexRenameExpr_fixedParameters
    (by intro id _ hmem; cases hmem) within
  obtain ⟨pairs, correspondence, hterminal⟩ := leftOpened.relatedLookupIndexCorrespondence rightOpened
    hinitial hroles hparams leftDeclared rightDeclared (by simpa using injection) (by simpa using support)
    shapes (by simpa using within)
  exact ⟨pairs, correspondence, by simpa using correspondence.finalPairs, hterminal⟩

end Lean4Lean.AddInductive
