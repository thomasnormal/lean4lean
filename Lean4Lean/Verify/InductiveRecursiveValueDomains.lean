import Lean4Lean.Verify.InductiveRecursiveCallTranslation
import Lean4Lean.Verify.InductiveRecursorImplicitTranslation
import Lean4Lean.Verify.InductiveIHTranslation
import Lean4Lean.Verify.InductiveHeaderApplicationBatch

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)
open private originalHeaderConstantInput from Lean4Lean.Verify.InductiveHeaderApplicationBatch

/-- Reuse the actual shared declarations before checking the changed indices.
The tail is checked against the open index telescope, after the shared
parameters, motives and minors have been substituted back into the signature. -/
theorem NativeTelescopeArguments.selectedPrefix
    (envWF : env.WF) (modelWF : model.WF env universes)
    (ids : List FVarId) (distinct : ids.Nodup)
    (bindings : SelectedCDeclBindings model.lctx ids)
    (bodyClosed : body.looseBVarRange' = 0)
    (tail : NativeTelescopeArguments env universes model body arguments terminal) :
    NativeTelescopeArguments env universes model
      (model.lctx.mkForall (ids.map Expr.fvar).toArray body)
      (ids.map Expr.fvar ++ arguments) terminal :=
  (NativeTelescopeArguments.selected envWF modelWF ids distinct bindings bodyClosed).append tail

/-- Recover the raw signature from the actual stored metadata, before the
native implicit-binder pass. The signature's model and batch insertion supply
its translation and typing; a second raw-signature translation is unnecessary. -/
theorem recursorRawInputAfterInsertion
    {safety : DefinitionSafety} {before after : VEnv} {models : List VConstVal}
    {info : RecursorVal} {constant : VConstVal} {raw : Expr}
    (signature : TrConstVal safety before (.recInfo info) constant)
    (stored : info.type = raw.inferImplicit count considerRange)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some after)
    {model : MLCtx} (afterWF : after.WF) (modelWF : model.WF after universes)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length) :
    Nonempty (RecursorConstantInput after universes model.vlctx info.name levels
      (raw.instantiateLevelParams info.levelParams levels)) := by
  have translated := signature.1.2.2
  change TrExprS before info.levelParams [] info.type constant.type at translated
  rw [stored] at translated
  have rawTranslated := translated.of_inferImplicit count considerRange
  have lookup := VEnv.addConstructorHeaders.constants inserted member
  rw [← signature.2] at lookup
  exact RecursorConstantInput.ofTranslation afterWF lookup
    (rawTranslated.mono (VEnv.addConstructorHeaders.le inserted)) signature.1.2.1
    model modelWF mapped arity

/-- Calls generated inside a recursor's own universe context use the original
raw signature directly. This avoids assuming that native universe substitution
is syntactically the identity (it can normalize level expressions). -/
theorem recursorRawOriginalInputAfterInsertion
    {safety : DefinitionSafety} {before after : VEnv} {models : List VConstVal}
    {info : RecursorVal} {constant : VConstVal} {raw : Expr}
    (signature : TrConstVal safety before (.recInfo info) constant)
    (stored : info.type = raw.inferImplicit count considerRange)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some after)
    {model : MLCtx} (afterWF : after.WF) (modelWF : model.WF after info.levelParams) :
    Nonempty (RecursorConstantInput after info.levelParams model.vlctx info.name
      (info.levelParams.map Level.param) raw) := by
  have translated := signature.1.2.2
  change TrExprS before info.levelParams [] info.type constant.type at translated
  rw [stored] at translated
  have lookup := VEnv.addConstructorHeaders.constants inserted member
  rw [← signature.2] at lookup
  exact originalHeaderConstantInput afterWF lookup
    ((translated.of_inferImplicit count considerRange).mono
      (VEnv.addConstructorHeaders.le inserted)) signature.1.2.1 model modelWF

/-- The generated signature's shared prefix has the same telescope in the
rule context when those declarations have been preserved. Formal index and
major binders remain in the tail, ready for the changed actual indices. -/
theorem recursorRawType_sharedPrefix
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (full current : LocalContext) (ids : List FVarId)
    (fullScope : full.BindingScope) (currentScope : current.BindingScope)
    (shared : (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors)).toList =
      ids.map Expr.fvar)
    (distinct : ids.Nodup) (agreement : SelectedCDeclBindingAgreement full current ids)
    (closed : (full.mkForall infos[parent]!.indices
      (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))).looseBVarRange' = 0) :
    recursorRawType stats infos parent full =
      current.mkForall (ids.map Expr.fvar).toArray
        (full.mkForall infos[parent]!.indices
          (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))) := by
  let groups := [stats.params, infos.map (·.motive), infos.flatMap (·.minors)]
  have array : binderGroupArray groups = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [groups, binderGroupArray, List.foldr_cons, List.foldr_nil,
      Array.append_empty, ← Array.append_assoc, List.toList_toArray] using shared
  have selection : (binderGroupArray groups).toList = ids.map Expr.fvar := by rw [array]
  have idsEq := binderArrayIds_of_toList_eq selection
  have flattened := mkForall_groups_eq_flat groups fullScope closed
    (BinderArrayFVars.of_toList_eq selection)
    (by simpa only [idsEq] using distinct) (by simpa only [idsEq] using agreement.left)
  change recursorRawType stats infos parent full = _ at flattened
  rw [flattened, array]
  exact mkForall_congr_selected_cdecl ids fullScope currentScope closed distinct agreement

/-- The actual call levels agree with the declared recursor's own level
parameters when the checked statistics retain the original parameter levels. -/
theorem declaredRecursor_callLevels (stats : InductiveStats) (types : Array InductiveType)
    (elimination : Level) (infos : Array RecInfo) (universes : List Name)
    (full : LocalContext) (isK isUnsafe : Bool) (parent : Nat) (rules : List RecursorRule)
    (levels : stats.levels = universes.map Level.param) :
    getRecLevels elimination stats.levels =
      (declareRecursors.metadataVal stats types elimination infos universes full isK isUnsafe
        parent rules).levelParams.map Level.param := by
  rw [levels]
  cases elimination <;> rfl

/-- A generated recursive value has the native IH domain for its actual
recursive field, including all higher-order arguments. Shared argument support
comes from cdecl lookups; only changed-index support and the native signature
shape remain explicit. Neither complete-call typing nor IH-domain translation
is a premise. -/
theorem UArgModelEndpoint.recursiveValueInIHDomain
    {env before : VEnv} {universes : List Name} {models : List VConstVal}
    {safety : DefinitionSafety} {info : RecursorVal} {constant : VConstVal} {raw : Expr}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (stored : info.type = raw.inferImplicit count considerRange)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF)
    {levels : List Level} {semanticLevels : List VLevel}
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length)
    (stats : InductiveStats) (infos : Array RecInfo) (motives minors : Array Expr)
    (ids : List FVarId) (distinct : ids.Nodup)
    (shared : (stats.params ++ motives ++ minors).toList = ids.map Expr.fvar)
    (bindings : SelectedCDeclBindings final.lctx ids)
    {indexSource : Expr} (indexClosed : indexSource.looseBVarRange' = 0)
    (shape : raw.instantiateLevelParams info.levelParams levels =
      final.lctx.mkForall (ids.map Expr.fvar).toArray indexSource)
    {majorName : Name} {majorBinder : BinderInfo}
    (indices : NativeTelescopeArguments env universes final indexSource
      (getIIndices stats terminal).2.toList
      (.forallE majorName terminal
        (.app ((mkAppN infos[(getIIndices stats terminal).1]!.motive
          (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)) :
    ∃ value domain,
      TrExprS env universes initial.vlctx
        (finalReader.lctx.mkLambda arguments
          ((mkAppN (mkAppN (mkAppN (mkAppN (.const info.name levels) stats.params)
            motives) minors) (getIIndices stats terminal).2).app (mkAppN argument arguments)))
        value ∧
      TrExprS env universes initial.vlctx
        (recursorIHDomain stats infos argument terminal arguments finalReader) domain ∧
      env.HasType universes.length initial.vlctx.toCtx value domain := by
  obtain ⟨input⟩ := recursorRawInputAfterInsertion signature stored member inserted envWF
    endpoint.context.1 mapped arity
  have prefixSupport := NativeTelescopeArguments.selectedPrefix envWF endpoint.context.1 ids distinct
    bindings indexClosed indices
  rw [← shape, ← shared, ← Array.toList_append] at prefixSupport
  obtain ⟨value, domain, translated, domainTranslated, typed⟩ :=
    endpoint.recursiveValueFromInput input envWF stats motives minors
      (getIIndices stats terminal).2 prefixSupport
  refine ⟨value, domain, translated, ?_, typed⟩
  simpa only [recursorIHDomain, recursorIHBody, Expr.instantiate1',
    Expr.instantiate1'_liftLooseBVars_0, Nat.lt_irrefl, beq_self_eq_true,
    Bool.false_eq_true, if_false, if_true, Expr.liftLooseBVars_zero] using domainTranslated

set_option maxHeartbeats 800000 in
/-- In the generated universe context, actual metadata and shared-binding
preservation discharge the signature and prefix shape. Only the changed-index
arguments remain to be supplied, together with their native canonical major
and motive-result shape. -/
theorem UArgModelEndpoint.recursiveValueInGeneratedIHDomain
    {env before : VEnv} {models : List VConstVal} {safety : DefinitionSafety}
    {info : RecursorVal} {constant : VConstVal}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx}
    (endpoint : UArgModelEndpoint env info.levelParams opening initial final)
    (signature : TrConstVal safety before (.recInfo info) constant)
    (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat) (full : LocalContext)
    (stored : info.type = (recursorRawType stats infos parent full).inferImplicit 1000 false)
    (member : constant ∈ models) (inserted : before.addConstructorHeaders models = some env)
    (envWF : env.WF) (fullScope : full.BindingScope)
    (ids : List FVarId) (distinct : ids.Nodup)
    (shared : (stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors)).toList =
      ids.map Expr.fvar)
    (agreement : SelectedCDeclBindingAgreement full final.lctx ids)
    (closed : (full.mkForall infos[parent]!.indices
      (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent))).looseBVarRange' = 0)
    {majorName : Name} {majorBinder : BinderInfo}
    (indices : NativeTelescopeArguments env info.levelParams final
      (full.mkForall infos[parent]!.indices
        (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList
      (.forallE majorName terminal
        (.app ((mkAppN infos[(getIIndices stats terminal).1]!.motive
          (getIIndices stats terminal).2).liftLooseBVars' 0 1) (.bvar 0)) majorBinder)) :
    ∃ value domain,
      TrExprS env info.levelParams initial.vlctx
        (finalReader.lctx.mkLambda arguments
          ((mkAppN (mkAppN (mkAppN (mkAppN
            (.const info.name (info.levelParams.map Level.param)) stats.params)
            (infos.map (·.motive))) (infos.flatMap (·.minors))) (getIIndices stats terminal).2).app
              (mkAppN argument arguments))) value ∧
      TrExprS env info.levelParams initial.vlctx
        (recursorIHDomain stats infos argument terminal arguments finalReader) domain ∧
      env.HasType info.levelParams.length initial.vlctx.toCtx value domain := by
  obtain ⟨input⟩ := recursorRawOriginalInputAfterInsertion signature stored member inserted
    envWF endpoint.context.1
  have shape := recursorRawType_sharedPrefix stats infos parent full final.lctx ids fullScope
    endpoint.context.1.bindingScope shared distinct agreement closed
  have prefixSupport := NativeTelescopeArguments.selectedPrefix envWF endpoint.context.1 ids
    distinct agreement.right closed indices
  rw [← shape, ← shared, ← Array.toList_append] at prefixSupport
  obtain ⟨value, domain, translated, domainTranslated, typed⟩ :=
    endpoint.recursiveValueFromInput (source := recursorRawType stats infos parent full)
      (majorName := majorName) (majorBinder := majorBinder)
      input envWF stats (infos.map (·.motive))
      (infos.flatMap (·.minors)) (getIIndices stats terminal).2 prefixSupport
  refine ⟨value, domain, translated, ?_, typed⟩
  simpa only [recursorIHDomain, recursorIHBody, Expr.instantiate1',
    Expr.instantiate1'_liftLooseBVars_0, Nat.lt_irrefl, beq_self_eq_true,
    Bool.false_eq_true, if_false, if_true, Expr.liftLooseBVars_zero] using domainTranslated

/-- The recursive value can be supplied where the generated, annotation-peeled
IH binder is expected. Alignment uses translation uniqueness and the actual
opening's conversion, without assuming the value already has the IH type. -/
theorem RecursorIHOpening.acceptsValue
    {env : VEnv} {universes : List Name} {reader : Context} {model : MLCtx}
    {argument domain : Expr} {rawSemantic peeled : VExpr} {level : VLevel}
    (opening : RecursorIHOpening env universes reader model.vlctx argument domain
      rawSemantic peeled level)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (domainTranslated : TrExprS env universes model.vlctx domain semantic)
    (typed : env.HasType universes.length model.vlctx.toCtx value semantic) :
    env.HasType universes.length model.vlctx.toCtx value peeled := by
  have equality := domainTranslated.uniq envWF (.refl envWF modelWF.tr.wf)
    opening.domainTranslated
  exact (typed.defeqU_r envWF modelWF.tr.wf.toCtx equality).defeqU_r envWF
    modelWF.tr.wf.toCtx opening.domainEquality.toU

end Lean4Lean.AddInductive
