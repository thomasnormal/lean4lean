import Lean4Lean.Verify.InductiveRecursiveValueDomains

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open TypeChecker (MLCtx)

/-- A native correspondence between two telescopes, checked after each actual
argument is substituted. Domains agree; binder names/implicit annotations and
the terminal result may differ. This contains no semantic typing evidence. -/
inductive NativeTelescopeDomains : Expr → Expr → List Expr → Expr → Expr → Prop where
  | nil : NativeTelescopeDomains left right [] left right
  | cons {leftName rightName : Name} {domain leftBody rightBody argument : Expr}
      {leftBinder rightBinder : BinderInfo} {arguments : List Expr} {leftEnd rightEnd : Expr}
      (tail : NativeTelescopeDomains (leftBody.instantiate1' argument)
        (rightBody.instantiate1' argument) arguments leftEnd rightEnd) :
      NativeTelescopeDomains (.forallE leftName domain leftBody leftBinder)
        (.forallE rightName domain rightBody rightBinder)
        (argument :: arguments) leftEnd rightEnd

/-- Recover individual argument typing from an actual translated application.
Type uniqueness and Pi injectivity align each application domain with the
translated native source domain, before dependent substitution into the tail. -/
theorem NativeTelescopeDomains.argumentsFromStack
    (domains : NativeTelescopeDomains source target arguments sourceEnd targetEnd)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (sourceTranslated : TrExprS env universes model.vlctx source sourceSemantic)
    (stack : AppStack env universes model.vlctx head headSemantic arguments)
    (headTyped : env.HasType universes.length model.vlctx.toCtx headSemantic sourceSemantic) :
    NativeTelescopeArguments env universes model source arguments sourceEnd ∧
      NativeTelescopeArguments env universes model target arguments targetEnd := by
  induction domains generalizing head headSemantic sourceSemantic with
  | nil => exact ⟨.nil, .nil⟩
  | cons tail induction =>
    cases sourceTranslated with
    | forallE _ _ domainTranslated bodyTranslated =>
      cases stack with
      | app functionTyped argumentTyped functionTranslated argumentTranslated tailStack =>
        have equality := headTyped.uniqU envWF modelWF.tr.wf.toCtx functionTyped
        obtain ⟨⟨_, domainEquality⟩, _⟩ :=
          VEnv.IsDefEqU.forallE_inv envWF modelWF.tr.wf.toCtx equality
        have converted := argumentTyped.defeqU_r envWF modelWF.tr.wf.toCtx domainEquality.toU.symm
        obtain ⟨left, right⟩ := induction
          (bodyTranslated.inst envWF.ordered converted argumentTranslated)
          tailStack (headTyped.app converted)
        exact ⟨.cons domainTranslated argumentTranslated converted left,
          .cons domainTranslated argumentTranslated converted right⟩

theorem NativeTelescopeDomains.argumentsFromApplication
    (domains : NativeTelescopeDomains source target arguments sourceEnd targetEnd)
    (envWF : env.WF) (modelWF : model.WF env universes)
    (sourceTranslated : TrExprS env universes model.vlctx source sourceSemantic)
    (headTranslated : TrExprS env universes model.vlctx head headSemantic)
    (headTyped : env.HasType universes.length model.vlctx.toCtx headSemantic sourceSemantic)
    (application : TrExprS env universes model.vlctx (head.mkAppList arguments) value) :
    NativeTelescopeArguments env universes model source arguments sourceEnd ∧
      NativeTelescopeArguments env universes model target arguments targetEnd := by
  obtain ⟨actualHead, stack⟩ := AppStack.build application
  have equality := headTranslated.uniq envWF (.refl envWF modelWF.tr.wf) stack.tr
  exact domains.argumentsFromStack envWF modelWF sourceTranslated stack
    (headTyped.defeqU_l envWF modelWF.tr.wf.toCtx equality)

/-- The actual application prefix before the indices selected by `getIIndices`.
Keeping the native prefix preserves the accepted parameter expressions. -/
def familyIndexPrefix (stats : InductiveStats) (terminal : Expr) : Expr :=
  terminal.getAppFn.mkAppList (terminal.getAppArgs.toList.take stats.params.size)

theorem familyIndexPrefix_apply (stats : InductiveStats) (terminal : Expr) :
    (familyIndexPrefix stats terminal).mkAppList (getIIndices stats terminal).2.toList = terminal := by
  have indices : (getIIndices stats terminal).2.toList =
      terminal.getAppArgs.toList.drop stats.params.size := by
    simp [getIIndices, Subarray.toList_eq_drop_take, ← Array.length_toList,
      ← List.drop_eq_drop_min]
  rw [indices, familyIndexPrefix, ← Expr.mkAppList_append, List.take_append_drop,
    Expr.getAppArgs_eq, List.toList_toArray]
  exact Expr.mkAppList_getAppArgsList terminal

/-- A partial family application has its expected native index signature.
No index argument translation/typing, complete family application typing or
recursive-call typing is stored in this receipt. -/
structure FamilyIndexInput (env : VEnv) (universes : List Name) (model : MLCtx)
    (stats : InductiveStats) (terminal source : Expr) where
  type : VExpr
  sourceTranslated : TrExprS env universes model.vlctx source type
  value : VExpr
  translated : TrExprS env universes model.vlctx (familyIndexPrefix stats terminal) value
  typed : env.HasType universes.length model.vlctx.toCtx value type

/-- Recover changed-index argument support from the family application in the
actual recursive-field opening. Only a partial-family signature and a native
domain correspondence are required, rather than typed index arguments. -/
theorem UArgModelEndpoint.indexArguments
    {env : VEnv} {universes : List Name}
    {argument terminal : Expr} {arguments : Array Expr} {reader finalReader : Context}
    {opening : RecursorUArgOpeningTrace argument reader terminal arguments finalReader}
    {initial final : MLCtx} (endpoint : UArgModelEndpoint env universes opening initial final)
    (envWF : env.WF) (input : FamilyIndexInput env universes final stats terminal source)
    (domains : NativeTelescopeDomains source target (getIIndices stats terminal).2.toList
      sourceEnd targetEnd) :
    NativeTelescopeArguments env universes final target (getIIndices stats terminal).2.toList
      targetEnd := by
  obtain ⟨semantic, translated⟩ := endpoint.terminalTranslation
  rw [← familyIndexPrefix_apply stats terminal] at translated
  exact (domains.argumentsFromApplication envWF endpoint.context.1 input.sourceTranslated
    input.translated input.typed translated).2

/-- The actual field terminal supplies the changed indices' semantic typing.
The remaining family input types only the partial header; domain agreement and
canonical tail shape are native syntactic obligations. -/
theorem UArgModelEndpoint.recursiveValueInGeneratedIHDomainFromFamily
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
    {source sourceEnd : Expr}
    (family : FamilyIndexInput env info.levelParams final stats terminal source)
    (domains : NativeTelescopeDomains source
      (full.mkForall infos[parent]!.indices
        (full.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)))
      (getIIndices stats terminal).2.toList sourceEnd
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
  exact endpoint.recursiveValueInGeneratedIHDomain signature stats infos parent full stored
    member inserted envWF fullScope ids distinct shared agreement closed
    (endpoint.indexArguments envWF family domains)

end Lean4Lean.AddInductive
