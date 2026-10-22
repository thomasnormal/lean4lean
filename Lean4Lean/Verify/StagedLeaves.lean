import Lean4Lean.Verify.OrdinaryInterfaces

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem checkLevel.checker {ctx : Context} (hlevel : level.hasMVar' = false) :
    (checkLevel ctx level).WF fun _ => ∃ translated, VLevel.ofLevel ctx.lparams level = some translated := by
  simp [checkLevel]
  split
  · exact .throw
  · refine .pure ?_
    exact Level.getUndefParam_none hlevel (by rename_i hparams; simpa using hparams)

theorem envGet.lookup (env : Kernel.Environment) (name : Name) :
    (env.get name).WF fun info => env.find? name = some info := by
  simp [Kernel.Environment.get]
  split
  · exact .pure ‹_›
  · exact .throw

theorem inferConstant.checkerOf {ctx : Context} {semantic : VEnv} {scope : VLCtx}
    (hwf : semantic.WF)
    (hlookup : ∀ {name ci}, ctx.env.find? name = some ci → ctx.safety ≤ ci.safety →
      ∃ ci', semantic.constants name = some ci' ∧ TrConstant ctx.safety semantic ci ci')
    (huniq : ∀ {name ci ci'}, ctx.env.find? name = some ci → semantic.constants name = some ci' →
      ci.name = name ∧ TrConstant ctx.safety semantic ci ci')
    (hscope : scope.WF semantic ctx.lparams.length) (hnoBV : scope.NoBV)
    (hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (hinfer : inferOnly = true → ∃ model, TrExprS semantic ctx.lparams scope (.const name levels) model) :
    (inferConstant ctx name levels inferOnly).WF fun result =>
      ∃ model type, TrTyping semantic ctx.lparams scope (.const name levels) result model type := by
  simp [inferConstant]
  refine (envGet.lookup ctx.env name).bind fun info hfind => ?_
  have checkedLevels : (levels.foldlM (fun _ level => checkLevel ctx level) PUnit.unit).WF fun _ =>
      ∃ translated, levels.Forall₂ (VLevel.ofLevel ctx.lparams · = some ·) translated := by
    clear hinfer
    induction levels with
    | nil => exact .pure ⟨_, .nil⟩
    | cons level levels ih =>
      simp at hlevels
      refine (checkLevel.checker hlevels.1).bind fun ⟨⟩ ⟨translated, htranslated⟩ => ?_
      exact (ih hlevels.2).le fun _ ⟨_, hrest⟩ => ⟨_, .cons htranslated hrest⟩
  split
  · rename_i harity
    have translatedResult {model}
        (hmodel : TrExprS semantic ctx.lparams scope (.const name levels) model) :
        ∃ model type, TrTyping semantic ctx.lparams scope (.const name levels)
          (info.instantiateTypeLevelParams levels) model type := by
      let .const hconstant htranslated hlength := id hmodel
      have ⟨_, _, hparams, htype⟩ := huniq hfind hconstant
      have levelModels := List.mapM_eq_some.mp htranslated
      have instantiated := htype.instL hwf (Δ := []) trivial htranslated (hparams.trans hlength.symm)
      have weakened := instantiated.weakFV hwf (.from_nil hnoBV) hscope
      rw [(hwf.ordered.closedC hconstant).instL.liftN_eq (Nat.le_refl _)] at weakened
      obtain ⟨_, htranslation, hequality⟩ := weakened
      refine ⟨_, _, ?_, hmodel, htranslation,
        .defeqU_r hwf hscope hequality.symm ?_⟩
      · intro _ _ _
        exact instantiated.fvarsIn.mono nofun
      · exact .const hconstant (.of_mapM_ofLevel htranslated)
          ((Lean4Lean.List.Forall₂.length_eq levelModels).symm.trans hlength)
    split
    · split
      · exact .throw
      · rename_i hunsafe
        generalize haction : _ <$> (_ : Except Exception _) = action
        generalize hpost : (fun result : Expr => _) = post
        suffices info.isPartial = false ∨ ctx.safety ≠ .safe → action.WF post by
          split
          · split
            · exact .throw
            · apply this
              rename_i hpartial
              simpa [Decidable.or_iff_not_imp_left, ConstantInfo.isPartial] using hpartial
          · exact this (.inl (ConstantInfo.isPartial.eq_2 _ ‹_›))
        subst haction hpost
        intro hpartialAllowed
        refine checkedLevels.map fun _ ⟨_, htranslated⟩ => ?_
        have ⟨_, hconstant, _, hparams, _⟩ := hlookup hfind (by
          revert hunsafe hpartialAllowed
          simp [ConstantInfo.safety]
          split <;> simp +contextual [*]
          split <;> simp [DefinitionSafety.le_safe, *]
          cases ctx.safety <;> decide)
        exact translatedResult (.const hconstant (List.mapM_eq_some.mpr htranslated)
          (harity.symm.trans hparams))
    · simp_all
      obtain ⟨_, hmodel⟩ := hinfer
      exact .pure (translatedResult hmodel)
  · exact .throw

theorem inferConstant.checker {ctx : Context} {semantic : VEnv} {scope : VLCtx}
    (hchecker : CheckerEnv ctx.safety ctx.env semantic)
    (hscope : scope.WF semantic ctx.lparams.length) (hnoBV : scope.NoBV)
    (hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (hinfer : inferOnly = true → ∃ model, TrExprS semantic ctx.lparams scope (.const name levels) model) :
    (inferConstant ctx name levels inferOnly).WF fun result =>
      ∃ model type, TrTyping semantic ctx.lparams scope (.const name levels) result model type :=
  inferConstant.checkerOf hchecker.wf hchecker.find? hchecker.find?_uniq hscope hnoBV hlevels hinfer

theorem inferConstant.checkerInductive {ctx : Context} {semantic : VEnv} {scope : VLCtx}
    (hchecker : CheckerEnvInductive ctx.safety ctx.env semantic Q)
    (hscope : scope.WF semantic ctx.lparams.length) (hnoBV : scope.NoBV)
    (hlevels : ∀ level ∈ levels, level.hasMVar' = false)
    (hinfer : inferOnly = true → ∃ model, TrExprS semantic ctx.lparams scope (.const name levels) model) :
    (inferConstant ctx name levels inferOnly).WF fun result =>
      ∃ model type, TrTyping semantic ctx.lparams scope (.const name levels) result model type :=
  inferConstant.checkerOf hchecker.history.wf hchecker.find? hchecker.find?_uniq hscope hnoBV hlevels hinfer

theorem infer_sort.checker (hlevel : VLevel.ofLevel lparams level = some translated) :
    TrTyping semantic lparams scope (.sort level) (.sort level.succ)
      (.sort translated) (.sort translated.succ) := by
  refine ⟨fun _ _ _ => (?translation).fvarsIn, .sort hlevel, ?translation, .sort (.of_ofLevel hlevel)⟩
  exact .sort (by simpa [VLevel.ofLevel])

end Lean4Lean.TypeChecker.Inner
