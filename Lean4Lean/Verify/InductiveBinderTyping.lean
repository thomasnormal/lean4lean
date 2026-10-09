import Lean4Lean.Verify.InductiveAnnotationTyping
import Lean4Lean.Verify.InductiveBinderDomains

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def BinderRawDomainTypedSpines (translation : Nat → Expr → VExpr → Prop) (env : VEnv)
    (uvars : Nat) (contexts : Nat → List VExpr) (levels : Nat → VLevel)
    (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step → ∃ semantic,
    TypedAnnotationSpine (translation position) env uvars (contexts position) step.domain semantic (levels position)

def BinderRawDomainHasType (translation : Nat → Expr → VExpr → Prop) (env : VEnv)
    (uvars : Nat) (contexts : Nat → List VExpr) (levels : Nat → VLevel)
    (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step →
    SourceHasType (translation position) env uvars (contexts position) step.domain (.sort (levels position))

def BinderStoredIndexDomainHasType (translation : Nat → Expr → VExpr → Prop) (env : VEnv)
    (uvars : Nat) (contexts : Nat → List VExpr) (levels : Nat → VLevel)
    (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step → step.role = .index →
    SourceHasType (translation position) env uvars (contexts position) step.localDomain (.sort (levels position))

def BinderStoredIndexTypeHasType (translation : Nat → Expr → VExpr → Prop) (env : VEnv)
    (uvars : Nat) (contexts : Nat → List VExpr) (levels : Nat → VLevel)
    (ctx : Context) (steps : List BinderStep) : Prop :=
  ∀ position step decl, steps[position]? = some step → step.role = .index →
    ctx.lctx.find? step.value.fvarId! = some decl →
    SourceHasType (translation position) env uvars (contexts position) decl.type (.sort (levels position))

theorem BinderRawDomainTypedSpines.rawDomainHasType
    {translation : Nat → Expr → VExpr → Prop} {env : VEnv} {uvars : Nat}
    {contexts : Nat → List VExpr} {levels : Nat → VLevel} {steps : List BinderStep}
    (spines : BinderRawDomainTypedSpines translation env uvars contexts levels steps)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered) :
    BinderRawDomainHasType translation env uvars contexts levels steps := by
  intro position step selected
  obtain ⟨semantic, spine⟩ := spines position step selected
  exact spine.sourceHasType definitions ordered

theorem BinderRawDomainTypedSpines.storedIndexDomainHasType
    {translation : Nat → Expr → VExpr → Prop} {env : VEnv} {uvars : Nat}
    {contexts : Nat → List VExpr} {levels : Nat → VLevel} {steps : List BinderStep}
    (spines : BinderRawDomainTypedSpines translation env uvars contexts levels steps)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered) :
    BinderStoredIndexDomainHasType translation env uvars contexts levels steps := by
  intro position step selected _
  obtain ⟨semantic, spine⟩ := spines position step selected
  exact spine.peeledHasType definitions ordered

theorem BinderDeclaredAt.typeHasType {translation : Expr → VExpr → Prop} {env : VEnv}
    {uvars : Nat} {context : List VExpr} {type : VExpr} {ctx : Context}
    {value domain : Expr} {name : Name} {bi : BinderInfo}
    (declared : BinderDeclaredAt ctx value name domain bi)
    (typed : SourceHasType translation env uvars context domain type) :
    ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
      decl.type = domain ∧ SourceHasType translation env uvars context decl.type type := by
  obtain ⟨decl, lookup, valueEq, typeEq, _, _⟩ := declared
  exact ⟨decl, lookup, valueEq, typeEq, typeEq.symm ▸ typed⟩

theorem BinderStoredIndexDomainHasType.storedIndexTypeHasType
    {translation : Nat → Expr → VExpr → Prop} {env : VEnv} {uvars : Nat}
    {contexts : Nat → List VExpr} {levels : Nat → VLevel} {ctx : Context} {steps : List BinderStep}
    (typed : BinderStoredIndexDomainHasType translation env uvars contexts levels steps)
    (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeHasType translation env uvars contexts levels ctx steps := by
  intro position step decl selected index lookup
  have member : step ∈ steps := List.mem_iff_getElem?.mpr ⟨position, selected⟩
  obtain ⟨stored, storedLookup, _, typeEq, _, _⟩ := declared step member index
  have sameDecl : stored = decl := Option.some.inj (storedLookup.symm.trans lookup)
  subst stored
  rw [typeEq]
  exact typed position step selected index

theorem BinderRawDomainTypedSpines.storedIndexTypeHasType
    {translation : Nat → Expr → VExpr → Prop} {env : VEnv} {uvars : Nat}
    {contexts : Nat → List VExpr} {levels : Nat → VLevel} {ctx : Context} {steps : List BinderStep}
    (spines : BinderRawDomainTypedSpines translation env uvars contexts levels steps)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered)
    (declared : BinderStepsIndexDeclared ctx steps) :
    BinderStoredIndexTypeHasType translation env uvars contexts levels ctx steps :=
  (spines.storedIndexDomainHasType definitions ordered).storedIndexTypeHasType declared

theorem BinderRawDomainTypedSpines.typingReceipt
    {translation : Nat → Expr → VExpr → Prop} {env : VEnv} {uvars : Nat}
    {contexts : Nat → List VExpr} {levels : Nat → VLevel} {ctx : Context} {steps : List BinderStep}
    (spines : BinderRawDomainTypedSpines translation env uvars contexts levels steps)
    (definitions : CanonicalAnnotationDefinitions env) (ordered : env.Ordered)
    (declared : BinderStepsIndexDeclared ctx steps) :
    BinderRawDomainHasType translation env uvars contexts levels steps ∧
      BinderStoredIndexDomainHasType translation env uvars contexts levels steps ∧
      BinderStoredIndexTypeHasType translation env uvars contexts levels ctx steps :=
  ⟨spines.rawDomainHasType definitions ordered, spines.storedIndexDomainHasType definitions ordered,
    spines.storedIndexTypeHasType definitions ordered declared⟩

end Lean4Lean.AddInductive
