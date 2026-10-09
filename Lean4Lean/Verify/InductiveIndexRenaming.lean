import Lean4Lean.Verify.InductiveBinderDomains

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

inductive IndexRenaming (pairs : List (FVarId × FVarId)) : Expr → Expr → Prop where
  | bvar (index : Nat) : IndexRenaming pairs (.bvar index) (.bvar index)
  | sort (level : Level) : IndexRenaming pairs (.sort level) (.sort level)
  | const (name : Name) (levels : List Level) : IndexRenaming pairs (.const name levels) (.const name levels)
  | lit (literal : Literal) : IndexRenaming pairs (.lit literal) (.lit literal)
  | mvar (id : MVarId) : IndexRenaming pairs (.mvar id) (.mvar id)
  | fvar {left right : FVarId} (hpair : left = right ∨ (left, right) ∈ pairs) :
      IndexRenaming pairs (.fvar left) (.fvar right)
  | app {leftFn rightFn leftArg rightArg : Expr}
      (function : IndexRenaming pairs leftFn rightFn) (argument : IndexRenaming pairs leftArg rightArg) :
      IndexRenaming pairs (.app leftFn leftArg) (.app rightFn rightArg)
  | lam (name : Name) (bi : BinderInfo) {leftDomain rightDomain leftBody rightBody : Expr}
      (domain : IndexRenaming pairs leftDomain rightDomain) (body : IndexRenaming pairs leftBody rightBody) :
      IndexRenaming pairs (.lam name leftDomain leftBody bi) (.lam name rightDomain rightBody bi)
  | forallE (name : Name) (bi : BinderInfo) {leftDomain rightDomain leftBody rightBody : Expr}
      (domain : IndexRenaming pairs leftDomain rightDomain) (body : IndexRenaming pairs leftBody rightBody) :
      IndexRenaming pairs (.forallE name leftDomain leftBody bi) (.forallE name rightDomain rightBody bi)
  | letE (name : Name) (nondep : Bool) {leftDomain rightDomain leftValue rightValue leftBody rightBody : Expr}
      (domain : IndexRenaming pairs leftDomain rightDomain) (value : IndexRenaming pairs leftValue rightValue)
      (body : IndexRenaming pairs leftBody rightBody) :
      IndexRenaming pairs (.letE name leftDomain leftValue leftBody nondep)
        (.letE name rightDomain rightValue rightBody nondep)
  | mdata (data : MData) {left right : Expr} (body : IndexRenaming pairs left right) :
      IndexRenaming pairs (.mdata data left) (.mdata data right)
  | proj (name : Name) (index : Nat) {left right : Expr} (body : IndexRenaming pairs left right) :
      IndexRenaming pairs (.proj name index left) (.proj name index right)

theorem IndexRenaming.refl (pairs : List (FVarId × FVarId)) (type : Expr) :
    IndexRenaming pairs type type := by
  induction type with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | mvar id => exact .mvar id
  | fvar id => exact .fvar (.inl rfl)
  | app function argument ihFn ihArg => exact .app ihFn ihArg
  | lam name domain body bi ihDomain ihBody => exact .lam name bi ihDomain ihBody
  | forallE name domain body bi ihDomain ihBody => exact .forallE name bi ihDomain ihBody
  | letE name domain value body nondep ihDomain ihValue ihBody => exact .letE name nondep ihDomain ihValue ihBody
  | mdata data body ih => exact .mdata data ih
  | proj name index body ih => exact .proj name index ih

theorem IndexRenaming.mono {pairs extended : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexRenaming pairs left right) (hpairs : pairs ⊆ extended) :
    IndexRenaming extended left right := by
  induction related with
  | bvar index => exact .bvar index
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | mvar id => exact .mvar id
  | fvar hpair => exact .fvar (hpair.imp_right (fun hmember => hpairs hmember))
  | app function argument ihFn ihArg => exact .app ihFn ihArg
  | lam name bi domain body ihDomain ihBody => exact .lam name bi ihDomain ihBody
  | forallE name bi domain body ihDomain ihBody => exact .forallE name bi ihDomain ihBody
  | letE name nondep domain value body ihDomain ihValue ihBody => exact .letE name nondep ihDomain ihValue ihBody
  | mdata data body ih => exact .mdata data ih
  | proj name index body ih => exact .proj name index ih

theorem IndexRenaming.liftLooseBVars' {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexRenaming pairs left right) (start amount : Nat) :
    IndexRenaming pairs (left.liftLooseBVars' start amount) (right.liftLooseBVars' start amount) := by
  induction related generalizing start with
  | bvar index => exact .bvar _
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | mvar id => exact .mvar id
  | fvar hpair => exact .fvar hpair
  | app function argument ihFn ihArg => exact .app (ihFn start) (ihArg start)
  | lam name bi domain body ihDomain ihBody => exact .lam name bi (ihDomain start) (ihBody (start + 1))
  | forallE name bi domain body ihDomain ihBody => exact .forallE name bi (ihDomain start) (ihBody (start + 1))
  | letE name nondep domain value body ihDomain ihValue ihBody =>
    exact .letE name nondep (ihDomain start) (ihValue start) (ihBody (start + 1))
  | mdata data body ih => exact .mdata data (ih start)
  | proj name index body ih => exact .proj name index (ih start)

theorem IndexRenaming.instantiate1' {pairs : List (FVarId × FVarId)} {left right leftValue rightValue : Expr}
    (related : IndexRenaming pairs left right) (values : IndexRenaming pairs leftValue rightValue) (depth : Nat) :
    IndexRenaming pairs (left.instantiate1' leftValue depth) (right.instantiate1' rightValue depth) := by
  induction related generalizing depth with
  | bvar index =>
    simp only [Expr.instantiate1']
    split
    · exact .bvar index
    · split
      · exact values.liftLooseBVars' 0 depth
      · exact .bvar _
  | sort level => exact .sort level
  | const name levels => exact .const name levels
  | lit literal => exact .lit literal
  | mvar id => exact .mvar id
  | fvar hpair => exact .fvar hpair
  | app function argument ihFn ihArg => exact .app (ihFn depth) (ihArg depth)
  | lam name bi domain body ihDomain ihBody => exact .lam name bi (ihDomain depth) (ihBody (depth + 1))
  | forallE name bi domain body ihDomain ihBody => exact .forallE name bi (ihDomain depth) (ihBody (depth + 1))
  | letE name nondep domain value body ihDomain ihValue ihBody =>
    exact .letE name nondep (ihDomain depth) (ihValue depth) (ihBody (depth + 1))
  | mdata data body ih => exact .mdata data (ih depth)
  | proj name index body ih => exact .proj name index (ih depth)

theorem IndexRenaming.instantiate1 {pairs : List (FVarId × FVarId)} {left right leftValue rightValue : Expr}
    (related : IndexRenaming pairs left right) (values : IndexRenaming pairs leftValue rightValue) :
    IndexRenaming pairs (left.instantiate1 leftValue) (right.instantiate1 rightValue) := by
  rw [Expr.instantiate1_eq, Expr.instantiate1_eq]
  exact related.instantiate1' values 0

theorem IndexRenaming.binderSignature {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexRenaming pairs left right) : Expr.binderSignature left = Expr.binderSignature right := by
  induction related with
  | forallE name bi domain body ihDomain ihBody => exact congrArg ((name, bi) :: ·) ihBody
  | _ => rfl

theorem IndexRenaming.fvar_iff {pairs : List (FVarId × FVarId)} {left right : FVarId} :
    IndexRenaming pairs (.fvar left) (.fvar right) ↔ left = right ∨ (left, right) ∈ pairs := by
  constructor
  · intro related; cases related with | fvar hpair => exact hpair
  · exact .fvar

theorem IndexRenaming.const_iff {pairs : List (FVarId × FVarId)}
    {leftName rightName : Name} {leftLevels rightLevels : List Level} :
    IndexRenaming pairs (.const leftName leftLevels) (.const rightName rightLevels) ↔
      leftName = rightName ∧ leftLevels = rightLevels := by
  constructor
  · intro related; cases related; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact .const _ _

theorem IndexRenaming.sort_iff {pairs : List (FVarId × FVarId)} {left right : Level} :
    IndexRenaming pairs (.sort left) (.sort right) ↔ left = right := by
  constructor
  · intro related; cases related; rfl
  · rintro rfl; exact .sort _

def ConsumedIndexRenaming (pairs : List (FVarId × FVarId)) (left right : Expr) : Prop :=
  ∃ rawLeft rawRight, IndexRenaming pairs rawLeft rawRight ∧
    peelTypeAnnotations rawLeft = left ∧ peelTypeAnnotations rawRight = right

theorem ConsumedIndexRenaming.ofRaw {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexRenaming pairs left right) :
    ConsumedIndexRenaming pairs (peelTypeAnnotations left) (peelTypeAnnotations right) :=
  ⟨left, right, related, rfl, rfl⟩

theorem ConsumedIndexRenaming.mono {pairs extended : List (FVarId × FVarId)} {left right : Expr}
    (related : ConsumedIndexRenaming pairs left right) (hpairs : pairs ⊆ extended) :
    ConsumedIndexRenaming extended left right := by
  obtain ⟨rawLeft, rawRight, hraw, hleft, hright⟩ := related
  exact ⟨rawLeft, rawRight, hraw.mono hpairs, hleft, hright⟩

end Lean4Lean.AddInductive
