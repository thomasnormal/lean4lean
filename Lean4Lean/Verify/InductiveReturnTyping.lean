import Lean4Lean.Theory.SortArity
import Lean4Lean.Verify.ConstructorParams

namespace Lean4Lean
open Lean hiding Environment Exception

theorem TrExprS.constantKind
    {environment : VEnv} {universes : List Name} {context : VLCtx}
    {name : Name} {levels : List Level} {semantic : VExpr} {constant : VConstant} {count : Nat}
    (environmentWF : environment.WF) (lookup : environment.constants name = some constant)
    (kind : environment.SortArity constant.uvars [] count constant.type)
    (translated : TrExprS environment universes context (.const name levels) semantic) :
    ∃ type, environment.HasType universes.length context.toCtx semantic type ∧
      environment.SortArity universes.length context.toCtx count type := by
  cases translated with
  | const actualLookup mapped arity =>
    cases Option.some.inj (lookup.symm.trans actualLookup)
    have levelsWF := VLevel.WF.of_mapM_ofLevel mapped
    refine ⟨_, .const lookup levelsWF ((List.mapM_eq_some.mp mapped).length_eq.symm.trans arity), ?_⟩
    have specialized := kind.instL levelsWF
    exact specialized.weak0 environmentWF

theorem TrExprS.saturatedIsType
    {environment : VEnv} {universes : List Name} {context : VLCtx}
    {function : Expr} {arguments : List Expr} {semantic : VExpr}
    (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (translated : TrExprS environment universes context (function.mkAppList arguments) semantic)
    (headKind : ∀ {functionSemantic}, TrExprS environment universes context function functionSemantic →
      ∃ functionType, environment.HasType universes.length context.toCtx functionSemantic functionType ∧
        environment.SortArity universes.length context.toCtx arguments.length functionType) :
    environment.IsType universes.length context.toCtx semantic := by
  induction arguments generalizing function semantic with
  | nil =>
    obtain ⟨functionType, typed, kind⟩ := headKind translated
    exact kind.typedIsType environmentWF contextWF.toCtx typed
  | cons argument arguments induction =>
    apply induction translated
    intro functionSemantic functionTranslated
    cases functionTranslated with
    | app functionTyped argumentTyped functionTranslated argumentTranslated =>
      obtain ⟨functionType, typed, kind⟩ := headKind functionTranslated
      exact ⟨_, functionTyped.app argumentTyped,
        kind.apply environmentWF contextWF.toCtx typed functionTyped argumentTyped⟩

namespace AddInductive

theorem isValidIndAppIdx.headerMatches (stats : InductiveStats) (type : Expr)
    (parent : Nat) (accepted : isValidIndAppIdx stats type parent = true) :
    (type.getAppFn == stats.indConsts[parent]!) = true ∧
      type.getAppArgs.size = stats.params.size + stats.nindices[parent]! := by
  simp only [isValidIndAppIdx, Expr.withApp_eq] at accepted
  dsimp only [Id.run] at accepted
  split at accepted
  · rename_i guards
    simpa using guards
  · simp at accepted

theorem isValidIndAppIdx.isType
    {environment : VEnv} {universes : List Name} {context : VLCtx}
    {stats : InductiveStats} {source : Expr} {parent : Nat} {semantic : VExpr}
    (environmentWF : environment.WF) (contextWF : context.WF environment universes.length)
    (accepted : isValidIndAppIdx stats source parent = true)
    (translated : TrExprS environment universes context source semantic)
    (headerKind : ∀ {headerSemantic},
      TrExprS environment universes context stats.indConsts[parent]! headerSemantic →
      ∃ headerType, environment.HasType universes.length context.toCtx headerSemantic headerType ∧
        environment.SortArity universes.length context.toCtx
          (stats.params.size + stats.nindices[parent]!) headerType) :
    environment.IsType universes.length context.toCtx semantic := by
  obtain ⟨headMatches, argumentCount⟩ := isValidIndAppIdx.headerMatches stats source parent accepted
  apply TrExprS.saturatedIsType environmentWF contextWF
    (Expr.mkAppList_getAppArgsList source ▸ translated)
  intro headerSemantic headerTranslated
  obtain ⟨headerType, typed, kind⟩ := headerKind (headerTranslated.eqv headMatches)
  refine ⟨headerType, typed, ?_⟩
  simpa only [← argumentCount, Expr.getAppArgs_eq, List.size_toArray] using kind

end AddInductive
end Lean4Lean
