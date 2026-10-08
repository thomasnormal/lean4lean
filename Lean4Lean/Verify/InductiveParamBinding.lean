import Lean4Lean.Verify.InductiveParamValidity

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

def paramForall (decls : List LocalDecl) (params : Array Expr) (body : Expr) : Expr :=
  decls.foldr (fun decl result =>
    .forallE decl.userName (decl.type.abstractRange decl.index params) result decl.binderInfo)
      (body.abstract params)

theorem arity_abstract1 (type : Expr) (fvar : FVarId) (index depth : Nat) :
    AddInductive.declareConstructors.arity index (type.abstract1 fvar depth) =
      AddInductive.declareConstructors.arity index type := by
  induction type generalizing index depth with
  | fvar => simp only [Expr.abstract1]; split <;> rfl
  | forallE name domain body bi ihDomain ihBody => exact ihBody (index + 1) (depth + 1)
  | _ => rfl

theorem arity_abstractFVars (type : Expr) (ids : List FVarId) (index depth : Nat) :
    AddInductive.declareConstructors.arity index (type.abstractFVars ids depth) =
      AddInductive.declareConstructors.arity index type := by
  induction type generalizing index depth with
  | fvar id =>
    simp only [Expr.abstractFVars]
    cases Expr.abstractFVarIndex id ids <;> rfl
  | forallE name domain body bi ihDomain ihBody => exact ihBody (index + 1) (depth + 1)
  | _ => rfl

theorem arity_abstract (type : Expr) (ids : List FVarId) (index : Nat) :
    AddInductive.declareConstructors.arity index (type.abstract (ids.map Expr.fvar).toArray) =
      AddInductive.declareConstructors.arity index type := by
  rw [Expr.abstract_eq]
  exact arity_abstractFVars type ids index 0

theorem paramForall.arity (decls : List LocalDecl) (params : Array Expr) (body : Expr) :
    AddInductive.declareConstructors.arity 0 (paramForall decls params body) =
      decls.length + AddInductive.declareConstructors.arity 0 (body.abstract params) := by
  induction decls with
  | nil => exact (Nat.zero_add _).symm
  | cons decl decls ih =>
    change AddInductive.declareConstructors.arity 1 (paramForall decls params body) = _
    rw [AddInductive.declareConstructors.arity_eq_add, ih]
    simp only [List.length_cons]
    omega

theorem ParamValidity.mkForall_eq {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    lctx.mkForall params body = paramForall lctx.toList.reverse params body := by
  have hlength : lctx.toList.reverse.length = params.size := by
    rw [List.length_reverse, hvalid.context.length, hvalid.context.size]
  let declaration (index : Fin params.size) :=
    lctx.toList.reverse[index.val]'(by rw [hlength]; exact index.isLt)
  have hdecls : (List.finRange params.size).map declaration = lctx.toList.reverse := by
    apply List.ext_getElem
    · simpa using hlength.symm
    · intro index hleft hright
      simp only [List.getElem_map, List.getElem_finRange]
      rfl
  unfold LocalContext.mkForall LocalContext.mkBinding paramForall
  rw [Nat.foldRev_eq_finRange_foldr, ← hdecls, List.foldr_map]
  congr 1
  funext index result
  rcases hvalid.declarationAt index.val index.isLt with
    ⟨decl, hposition, hdeclindex, hexpr, hnonlet, hkind⟩
  have hdecl : declaration index = decl := by
    have hget : lctx.toList.reverse[index.val]? = some (declaration index) :=
      List.getElem?_eq_getElem _
    exact Option.some.inj (hget.symm.trans hposition)
  have hlookup : lctx.findFVar? params[index.val] = some decl := by
    rw [← hexpr]
    exact hvalid.find?_eq (List.mem_reverse.mp (List.mem_of_getElem? hposition))
  simp only [hdecl, hlookup]
  cases decl with
  | cdecl declIndex fvar name domain bi kind =>
    simp only [LocalDecl.index] at hdeclindex
    subst declIndex
    rfl
  | ldecl declIndex fvar name domain value nondep kind =>
    cases nondep <;> simp [LocalDecl.value?] at hnonlet

theorem ParamValidity.mkForall_arity {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    AddInductive.declareConstructors.arity 0 (lctx.mkForall params body) =
      numParams + AddInductive.declareConstructors.arity 0 body := by
  rw [hvalid.mkForall_eq, paramForall.arity, List.length_reverse, hvalid.context.length]
  have hvars : lctx.toList.reverse.map LocalDecl.toExpr = params.toList := by
    rw [List.map_reverse, hvalid.context.decls, List.reverse_reverse]
  have hparams : params =
      ((lctx.toList.reverse.map LocalDecl.fvarId).map Expr.fvar).toArray := by
    rw [List.map_map]
    change params = (lctx.toList.reverse.map LocalDecl.toExpr).toArray
    rw [hvars, Array.toArray_toList]
  rw [hparams, arity_abstract]

theorem ParamValidity.mkForall_arity_ge {numParams : Nat} {lctx : LocalContext}
    {params : Array Expr} (hvalid : ParamValidity numParams lctx params) (body : Expr) :
    numParams ≤ AddInductive.declareConstructors.arity 0 (lctx.mkForall params body) := by
  rw [hvalid.mkForall_arity]
  exact Nat.le_add_right _ _

def ParamBinding (numParams : Nat) (lctx : LocalContext) (params : Array Expr) : Prop :=
  ∀ body, lctx.mkForall params body = paramForall lctx.toList.reverse params body ∧
    AddInductive.declareConstructors.arity 0 (lctx.mkForall params body) =
      numParams + AddInductive.declareConstructors.arity 0 body

theorem ParamValidity.binding {numParams : Nat} {lctx : LocalContext} {params : Array Expr}
    (hvalid : ParamValidity numParams lctx params) : ParamBinding numParams lctx params :=
  fun body => ⟨hvalid.mkForall_eq body, hvalid.mkForall_arity body⟩

theorem withParams.getBinding (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result => ParamBinding numParams result.1.1 result.1.2.2 :=
  (withParams.getValidContext type numParams env state).mono fun _ hvalid => hvalid.1.binding

theorem withParams.getReabstractArity (type : Expr) (numParams : Nat)
    (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => pure (lctx, remainder, params))
      env state).WF fun result =>
        AddInductive.declareConstructors.arity 0
          (result.1.1.mkForall result.1.2.2 result.1.2.1) =
            AddInductive.declareConstructors.arity 0 type := by
  intro result hresult
  have hvalid := withParams.getValidContext type numParams env state result hresult
  have hprefix := withParams.getPrefix type numParams env state result hresult
  rw [hvalid.1.mkForall_arity]
  exact hprefix.2.1.symm

theorem withParams.mkForall_arity (type : Expr) (numParams : Nat)
    (next : LocalContext → Expr → Array Expr → M Expr) (env : Environment) (state : State) :
    (withParams type numParams (fun lctx remainder params => do
      return lctx.mkForall params (← next lctx remainder params)) env state).WF fun result =>
        numParams ≤ AddInductive.declareConstructors.arity 0 result.1 := by
  apply withParams.validContext
  intro lctx remainder params state' hvalid _
  have hnext : (next lctx remainder params env state').WF fun _ => True := fun _ _ => trivial
  exact hnext.bind fun result _ => .pure (hvalid.mkForall_arity_ge result.1)

def Result.ParamBinding (numParams : Nat) (result : Result) : Prop :=
  result.nparams = numParams ∧ ∃ params, ElimNestedInductive.ParamBinding numParams result.lctx params

theorem run.paramBinding (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (run fuel numParams types env state).WF fun result => result.1.ParamBinding numParams :=
  (run.paramValidity fuel numParams types env state).mono fun _ hvalid => by
    rcases hvalid.2 with ⟨params, hparams⟩
    exact ⟨hvalid.1, params, hparams.binding⟩

theorem run.paramBinding_run' (fuel numParams : Nat) (types : List InductiveType)
    (env : Environment) (state : State) :
    (StateT.run' (run fuel numParams types env) state).WF fun result => result.ParamBinding numParams :=
  (run.paramBinding fuel numParams types env state).map fun _ hbinding => hbinding

end Lean4Lean.ElimNestedInductive
