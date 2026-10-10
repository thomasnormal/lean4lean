import Lean4Lean.Verify.RecursorMetadata
import Lean4Lean.Verify.LocalContext

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def recursorTypeBody (infos : Array RecInfo) (parent : Nat) : Expr :=
  .app (mkAppN infos[parent]!.motive infos[parent]!.indices) infos[parent]!.major

def recursorTypeBinders (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat) : Array Expr :=
  stats.params ++ infos.map (·.motive) ++ infos.flatMap (·.minors) ++
    infos[parent]!.indices ++ #[infos[parent]!.major]

def recursorRawType (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (lctx : LocalContext) : Expr :=
  lctx.mkForall stats.params <| lctx.mkForall (infos.map (·.motive)) <|
    lctx.mkForall (infos.flatMap (·.minors)) <| lctx.mkForall infos[parent]!.indices <|
    lctx.mkForall #[infos[parent]!.major] (recursorTypeBody infos parent)

theorem declareRecursors.metadataVal_type (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (parent : Nat) (rules : List RecursorRule) :
    (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe parent rules).type =
      (recursorRawType stats infos parent lctx).inferImplicit 1000 false := rfl

def SelectedCDeclBindings (lctx : LocalContext) (ids : List FVarId) : Prop :=
  ∀ id ∈ ids, ∃ index name domain bi kind,
    lctx.find? id = some (.cdecl index id name domain bi kind)

def SelectedCDeclBindingAgreement (left right : LocalContext) (ids : List FVarId) : Prop :=
  ∀ id ∈ ids, ∃ leftIndex rightIndex name domain bi leftKind rightKind,
    left.find? id = some (.cdecl leftIndex id name domain bi leftKind) ∧
    right.find? id = some (.cdecl rightIndex id name domain bi rightKind)

theorem SelectedCDeclBindingAgreement.left {left right : LocalContext} {ids : List FVarId}
    (agreement : SelectedCDeclBindingAgreement left right ids) : SelectedCDeclBindings left ids := by
  intro id member
  obtain ⟨leftIndex, rightIndex, name, domain, bi, leftKind, rightKind, lookup, _⟩ := agreement id member
  exact ⟨leftIndex, name, domain, bi, leftKind, lookup⟩

theorem SelectedCDeclBindingAgreement.right {left right : LocalContext} {ids : List FVarId}
    (agreement : SelectedCDeclBindingAgreement left right ids) : SelectedCDeclBindings right ids := by
  intro id member
  obtain ⟨leftIndex, rightIndex, name, domain, bi, leftKind, rightKind, _, lookup⟩ := agreement id member
  exact ⟨rightIndex, name, domain, bi, rightKind, lookup⟩

theorem SelectedCDeclBindings.lookups {lctx : LocalContext} {ids : List FVarId}
    (bindings : SelectedCDeclBindings lctx ids) :
    ∀ id ∈ ids, ∃ declaration, lctx.find? id = some declaration := by
  intro id member
  obtain ⟨index, name, domain, bi, kind, lookup⟩ := bindings id member
  exact ⟨_, lookup⟩

theorem SelectedCDeclBindings.subset {lctx : LocalContext} {ids selected : List FVarId}
    (bindings : SelectedCDeclBindings lctx ids) (included : ∀ id ∈ selected, id ∈ ids) :
    SelectedCDeclBindings lctx selected := fun id member => bindings id (included id member)

theorem mkBindingList_congr_selected_cdecl {left right : LocalContext}
    (ids : List FVarId) (isLambda : Bool) (body : Expr) (distinct : ids.Nodup)
    (agreement : SelectedCDeclBindingAgreement left right ids) :
    left.mkBindingList isLambda ids body = right.mkBindingList isLambda ids body := by
  rw [LocalContext.mkBindingList_eq_fold agreement.left.lookups distinct,
    LocalContext.mkBindingList_eq_fold agreement.right.lookups distinct]
  clear distinct
  induction ids with
  | nil => rfl
  | cons id ids tailInduction =>
    obtain ⟨leftIndex, rightIndex, name, domain, bi, leftKind, rightKind, leftLookup, rightLookup⟩ :=
      agreement id (by simp only [List.mem_cons_self])
    have tailAgreement : SelectedCDeclBindingAgreement left right ids := by
      intro selected member
      exact agreement selected (List.mem_cons_of_mem id member)
    rw [List.foldr_cons, List.foldr_cons, tailInduction tailAgreement]
    simp only [LocalContext.mkBindingList1, leftLookup, rightLookup]

theorem mkForall_congr_selected_cdecl {left right : LocalContext} {body : Expr}
    (ids : List FVarId) (leftScope : left.BindingScope) (rightScope : right.BindingScope)
    (bodyClosed : body.looseBVarRange' = 0) (distinct : ids.Nodup)
    (agreement : SelectedCDeclBindingAgreement left right ids) :
    left.mkForall (ids.map Expr.fvar).toArray body = right.mkForall (ids.map Expr.fvar).toArray body := by
  rw [LocalContext.mkForall, LocalContext.mkForall,
    LocalContext.mkBinding_eq bodyClosed leftScope distinct,
    LocalContext.mkBinding_eq bodyClosed rightScope distinct]
  exact mkBindingList_congr_selected_cdecl ids false body distinct agreement

theorem mkForall_selected_fold {lctx : LocalContext} {body : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    lctx.mkForall (ids.map Expr.fvar).toArray body =
      ids.foldr (fun id expression => lctx.mkBindingList1 false [] id (expression.abstract1 id)) body := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq bodyClosed scope distinct]
  exact LocalContext.mkBindingList_eq_fold bindings.lookups distinct

theorem mkForall_selected_closed {lctx : LocalContext} {body : Expr}
    (ids : List FVarId) (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    (lctx.mkForall (ids.map Expr.fvar).toArray body).looseBVarRange' = 0 := by
  rw [mkForall_selected_fold ids scope bodyClosed distinct bindings]
  clear distinct
  induction ids with
  | nil => exact bodyClosed
  | cons id ids tailInduction =>
    obtain ⟨index, name, domain, bi, kind, lookup⟩ := bindings id (by simp only [List.mem_cons_self])
    have tailBindings := bindings.subset (fun selected member => List.mem_cons_of_mem id member)
    have tailClosed := tailInduction tailBindings
    have domainClosed : domain.looseBVarRange' = 0 := (scope id _ lookup).1
    let inner := ids.foldr
      (fun selected expression => lctx.mkBindingList1 false [] selected (expression.abstract1 selected)) body
    have innerClosed : inner.looseBVarRange' = 0 := tailClosed
    have abstracted := Expr.abstractFVars_looseBVarRange inner [id] 0
    rw [Expr.abstractFVars_cons (Nat.le_of_eq innerClosed),
      Expr.abstractFVars_nil] at abstracted
    simp only [List.length_singleton, List.length_nil, Nat.add_zero, innerClosed] at abstracted
    simp only [List.foldr_cons]
    change (lctx.mkBindingList1 false [] id (inner.abstract1 id)).looseBVarRange' = 0
    simp only [LocalContext.mkBindingList1, lookup, Expr.abstractList,
      Bool.false_eq_true, if_false, Expr.looseBVarRange', domainClosed]
    change max 0 ((inner.abstract1 id).looseBVarRange' - 1) = 0
    omega

theorem mkForall_append_selected_cdecl {lctx : LocalContext} {body : Expr}
    (left right : List FVarId) (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (distinct : (left ++ right).Nodup) (bindings : SelectedCDeclBindings lctx (left ++ right)) :
    lctx.mkForall (left.map Expr.fvar).toArray
      (lctx.mkForall (right.map Expr.fvar).toArray body) =
      lctx.mkForall ((left ++ right).map Expr.fvar).toArray body := by
  have leftBindings := bindings.subset (fun id member => List.mem_append_left right member)
  have rightBindings := bindings.subset (fun id member => List.mem_append_right left member)
  have parts := List.nodup_append.mp distinct
  have innerClosed := mkForall_selected_closed right scope bodyClosed parts.2.1 rightBindings
  rw [mkForall_selected_fold left scope innerClosed parts.1 leftBindings,
    mkForall_selected_fold right scope bodyClosed parts.2.1 rightBindings,
    mkForall_selected_fold (left ++ right) scope bodyClosed distinct bindings, List.foldr_append]

def binderArrayIds (arguments : Array Expr) : List FVarId := arguments.toList.map Expr.fvarId!

def BinderArrayFVars (arguments : Array Expr) : Prop :=
  ∀ expression ∈ arguments.toList, ∃ identifier, expression = .fvar identifier

theorem BinderArrayFVars.array_eq {arguments : Array Expr} (shape : BinderArrayFVars arguments) :
    arguments = ((binderArrayIds arguments).map Expr.fvar).toArray := by
  apply Array.toList_inj.mp
  rw [List.toList_toArray, binderArrayIds, List.map_map]
  have mapped := List.map_congr_left (fun expression member => by
    obtain ⟨identifier, rfl⟩ := shape expression member
    rfl : ∀ expression ∈ arguments.toList, Expr.fvar expression.fvarId! = expression)
  exact (mapped.trans (List.map_id' arguments.toList)).symm

theorem BinderArrayFVars.of_toList_eq {arguments : Array Expr} {ids : List FVarId}
    (array : arguments.toList = ids.map Expr.fvar) : BinderArrayFVars arguments := by
  intro expression member
  rw [array] at member
  obtain ⟨identifier, _, rfl⟩ := List.mem_map.mp member
  exact ⟨identifier, rfl⟩

theorem binderArrayIds_of_toList_eq {arguments : Array Expr} {ids : List FVarId}
    (array : arguments.toList = ids.map Expr.fvar) : binderArrayIds arguments = ids := by
  rw [binderArrayIds, array, List.map_map]
  change ids.map (fun identifier => identifier) = ids
  exact List.map_id' ids

theorem BinderArrayFVars.append_left {left right : Array Expr}
    (shape : BinderArrayFVars (left ++ right)) : BinderArrayFVars left := by
  intro expression member
  exact shape expression (by rw [Array.toList_append]; exact List.mem_append_left _ member)

theorem BinderArrayFVars.append_right {left right : Array Expr}
    (shape : BinderArrayFVars (left ++ right)) : BinderArrayFVars right := by
  intro expression member
  exact shape expression (by rw [Array.toList_append]; exact List.mem_append_right _ member)

theorem binderArrayIds_append (left right : Array Expr) :
    binderArrayIds (left ++ right) = binderArrayIds left ++ binderArrayIds right := by
  simp only [binderArrayIds, Array.toList_append, List.map_append]

theorem mkForall_append_array_cdecl {lctx : LocalContext} {body : Expr}
    (left right : Array Expr) (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (shape : BinderArrayFVars (left ++ right)) (distinct : (binderArrayIds (left ++ right)).Nodup)
    (bindings : SelectedCDeclBindings lctx (binderArrayIds (left ++ right))) :
    lctx.mkForall left (lctx.mkForall right body) = lctx.mkForall (left ++ right) body := by
  have combined := shape.array_eq
  have leftArray := shape.append_left.array_eq
  have rightArray := shape.append_right.array_eq
  conv => lhs; rw [leftArray, rightArray]
  conv => rhs; rw [combined, binderArrayIds_append]
  exact mkForall_append_selected_cdecl (binderArrayIds left) (binderArrayIds right) scope bodyClosed
    (by simpa only [binderArrayIds_append] using distinct)
    (by simpa only [binderArrayIds_append] using bindings)

def binderGroupArray (groups : List (Array Expr)) : Array Expr := groups.foldr (· ++ ·) #[]

theorem mkForall_groups_eq_flat {lctx : LocalContext} {body : Expr}
    (groups : List (Array Expr)) (scope : lctx.BindingScope) (bodyClosed : body.looseBVarRange' = 0)
    (shape : BinderArrayFVars (binderGroupArray groups))
    (distinct : (binderArrayIds (binderGroupArray groups)).Nodup)
    (bindings : SelectedCDeclBindings lctx (binderArrayIds (binderGroupArray groups))) :
    groups.foldr (fun arguments expression => lctx.mkForall arguments expression) body =
      lctx.mkForall (binderGroupArray groups) body := by
  induction groups with
  | nil =>
    change body = lctx.mkForall #[] body
    exact (mkForall_selected_fold [] scope bodyClosed (by simp only [List.nodup_nil])
      (fun id member => by cases member)).symm
  | cons arguments groups tailInduction =>
    change BinderArrayFVars (arguments ++ binderGroupArray groups) at shape
    change (binderArrayIds (arguments ++ binderGroupArray groups)).Nodup at distinct
    change SelectedCDeclBindings lctx (binderArrayIds (arguments ++ binderGroupArray groups)) at bindings
    rw [binderArrayIds_append] at distinct bindings
    have parts := List.nodup_append.mp distinct
    have tailBindings := bindings.subset (fun id member => List.mem_append_right _ member)
    rw [List.foldr_cons, tailInduction shape.append_right parts.2.1 tailBindings]
    exact mkForall_append_array_cdecl arguments (binderGroupArray groups) scope bodyClosed shape
      (by simpa only [binderArrayIds_append] using distinct)
      (by simpa only [binderArrayIds_append] using bindings)

theorem recursorRawType_eq_flat (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (lctx : LocalContext) (scope : lctx.BindingScope)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (shape : BinderArrayFVars (recursorTypeBinders stats infos parent))
    (distinct : (binderArrayIds (recursorTypeBinders stats infos parent)).Nodup)
    (bindings : SelectedCDeclBindings lctx (binderArrayIds (recursorTypeBinders stats infos parent))) :
    recursorRawType stats infos parent lctx =
      lctx.mkForall (recursorTypeBinders stats infos parent) (recursorTypeBody infos parent) := by
  let groups := [stats.params, infos.map (·.motive), infos.flatMap (·.minors),
    infos[parent]!.indices, #[infos[parent]!.major]]
  have combined : binderGroupArray groups = recursorTypeBinders stats infos parent := by
    simp only [groups, binderGroupArray, List.foldr_cons, List.foldr_nil, Array.append_empty,
      recursorTypeBinders, Array.append_assoc]
  have flattened := mkForall_groups_eq_flat (lctx := lctx) (body := recursorTypeBody infos parent)
    groups scope bodyClosed (by simpa only [combined] using shape)
    (by simpa only [combined] using distinct) (by simpa only [combined] using bindings)
  simpa only [groups, List.foldr_cons, List.foldr_nil, combined, recursorRawType] using flattened

theorem recursorRawType_eq_flat_selected (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (lctx : LocalContext) (ids : List FVarId) (scope : lctx.BindingScope)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (array : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    (distinct : ids.Nodup) (bindings : SelectedCDeclBindings lctx ids) :
    recursorRawType stats infos parent lctx =
      lctx.mkForall (ids.map Expr.fvar).toArray (recursorTypeBody infos parent) := by
  have nativeIds := binderArrayIds_of_toList_eq array
  have nativeArray : recursorTypeBinders stats infos parent = (ids.map Expr.fvar).toArray := by
    apply Array.toList_inj.mp
    simpa only [List.toList_toArray] using array
  have flattened := recursorRawType_eq_flat stats infos parent lctx scope bodyClosed
    (BinderArrayFVars.of_toList_eq array) (by simpa only [nativeIds] using distinct)
    (by simpa only [nativeIds] using bindings)
  simpa only [nativeArray] using flattened

theorem recursorRawType_congr_selected (stats : InductiveStats) (infos : Array RecInfo) (parent : Nat)
    (left right : LocalContext) (ids : List FVarId)
    (leftScope : left.BindingScope) (rightScope : right.BindingScope)
    (bodyClosed : (recursorTypeBody infos parent).looseBVarRange' = 0)
    (array : (recursorTypeBinders stats infos parent).toList = ids.map Expr.fvar)
    (distinct : ids.Nodup) (agreement : SelectedCDeclBindingAgreement left right ids) :
    recursorRawType stats infos parent left = recursorRawType stats infos parent right := by
  rw [recursorRawType_eq_flat_selected stats infos parent left ids leftScope bodyClosed array distinct agreement.left,
    recursorRawType_eq_flat_selected stats infos parent right ids rightScope bodyClosed array distinct agreement.right]
  exact mkForall_congr_selected_cdecl ids leftScope rightScope bodyClosed distinct agreement

end Lean4Lean.AddInductive
