import Lean4Lean.Verify.InductiveAnnotationTranslation
import Lean4Lean.Verify.InductiveTelescopeTranslation
import Lean4Lean.Verify.InductiveBinderTyping

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

def BinderRawDomainTranslations (env : VEnv) (universeNames : List Name)
    (contexts : Nat → VLCtx) (levels : Nat → VLevel) (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step →
    SourceHasType (TrExprS env universeNames (contexts position)) env universeNames.length
      (contexts position).toCtx step.domain (.sort (levels position))

def BinderRawDomainUniverseUniform (universeNames : List Name)
    (levels : Nat → VLevel) (steps : List BinderStep) : Prop :=
  ∀ position step, steps[position]? = some step →
    UniformAnnotationUniverse universeNames step.domain (levels position)

theorem BinderRawDomainTranslations.typedSpines {env : VEnv} {universeNames : List Name}
    {contexts : Nat → VLCtx} {levels : Nat → VLevel} {steps : List BinderStep}
    (translated : BinderRawDomainTranslations env universeNames contexts levels steps)
    (envWF : env.WF)
    (contextTypes : ∀ position, OnCtx (contexts position).toCtx (env.IsType universeNames.length))
    (constants : CanonicalAnnotationConstants env)
    (uniform : BinderRawDomainUniverseUniform universeNames levels steps) :
    BinderRawDomainTypedSpines (fun position => TrExprS env universeNames (contexts position))
      env universeNames.length (fun position => (contexts position).toCtx) levels steps := by
  intro position step selected
  obtain ⟨semantic, domainTranslated, domainTyped⟩ := translated position step selected
  exact ⟨semantic, TypedAnnotationSpine.ofTrExprS envWF (contextTypes position) constants
    (uniform position step selected) domainTranslated domainTyped⟩

theorem BinderRawDomainTranslations.typingReceipt {env : VEnv} {universeNames : List Name}
    {contexts : Nat → VLCtx} {levels : Nat → VLevel} {ctx : Context} {steps : List BinderStep}
    (translated : BinderRawDomainTranslations env universeNames contexts levels steps)
    (envWF : env.WF)
    (contextTypes : ∀ position, OnCtx (contexts position).toCtx (env.IsType universeNames.length))
    (constants : CanonicalAnnotationConstants env) (definitions : CanonicalAnnotationDefinitions env)
    (uniform : BinderRawDomainUniverseUniform universeNames levels steps)
    (declared : BinderStepsIndexDeclared ctx steps) :
    BinderRawDomainHasType (fun position => TrExprS env universeNames (contexts position))
        env universeNames.length (fun position => (contexts position).toCtx) levels steps ∧
      BinderStoredIndexDomainHasType (fun position => TrExprS env universeNames (contexts position))
        env universeNames.length (fun position => (contexts position).toCtx) levels steps ∧
      BinderStoredIndexTypeHasType (fun position => TrExprS env universeNames (contexts position))
        env universeNames.length (fun position => (contexts position).toCtx) levels ctx steps :=
  (translated.typedSpines envWF contextTypes constants uniform).typingReceipt definitions envWF.ordered declared

theorem OpenedTelescope.domainTranslations {env : VEnv} {universeNames : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr}
    (opened : OpenedTelescope type steps terminal)
    (translated : TrExprS env universeNames context type semantic)
    (ordered : env.Ordered) (contextWF : context.WF env universeNames.length)
    (freshValues : FreshBinderValues context.fvars steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧ (∀ position, (contexts position).WF env universeNames.length) ∧
      BinderRawDomainTranslations env universeNames contexts levels steps :=
  opened.translatedDomains translated ordered contextWF freshValues

theorem OpenedTelescope.translatedTypingReceipt {env : VEnv} {universeNames : List Name}
    {context : VLCtx} {type terminal : Expr} {steps : List BinderStep} {semantic : VExpr} {ctx : Context}
    (opened : OpenedTelescope type steps terminal)
    (translated : TrExprS env universeNames context type semantic)
    (envWF : env.WF) (contextWF : context.WF env universeNames.length)
    (freshValues : FreshBinderValues context.fvars steps)
    (constants : CanonicalAnnotationConstants env) (definitions : CanonicalAnnotationDefinitions env)
    (declared : BinderStepsIndexDeclared ctx steps) :
    ∃ contexts : Nat → VLCtx, ∃ levels : Nat → VLevel,
      contexts 0 = context ∧ (∀ position, (contexts position).WF env universeNames.length) ∧
      BinderRawDomainTranslations env universeNames contexts levels steps ∧
      (BinderRawDomainUniverseUniform universeNames levels steps →
        BinderRawDomainHasType (fun position => TrExprS env universeNames (contexts position))
            env universeNames.length (fun position => (contexts position).toCtx) levels steps ∧
          BinderStoredIndexDomainHasType (fun position => TrExprS env universeNames (contexts position))
            env universeNames.length (fun position => (contexts position).toCtx) levels steps ∧
          BinderStoredIndexTypeHasType (fun position => TrExprS env universeNames (contexts position))
            env universeNames.length (fun position => (contexts position).toCtx) levels ctx steps) := by
  obtain ⟨contexts, levels, initial, contextsWF, domains⟩ :=
    opened.domainTranslations translated envWF.ordered contextWF freshValues
  exact ⟨contexts, levels, initial, contextsWF, domains, fun uniform =>
    domains.typingReceipt envWF (fun position => (contextsWF position).toCtx) constants definitions uniform declared⟩

end Lean4Lean.AddInductive
