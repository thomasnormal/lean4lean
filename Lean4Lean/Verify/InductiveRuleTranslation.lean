import Lean4Lean.Verify.InductiveNativeBridge
import Lean4Lean.Theory.ConstructorHeaders

namespace Lean4Lean.NativeInductive
open Lean hiding Environment Exception

/-- Explicit constant occurrences, including occurrences below native binders. -/
def hasExplicitConst (name : Name) : Expr → Bool
  | .const constant _ => constant == name
  | .app fn arg => hasExplicitConst name fn || hasExplicitConst name arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
    hasExplicitConst name domain || hasExplicitConst name body
  | .letE _ domain value body _ =>
    hasExplicitConst name domain || hasExplicitConst name value || hasExplicitConst name body
  | .mdata _ value | .proj _ _ value => hasExplicitConst name value
  | _ => false

theorem explicitConstPresent {env : VEnv} {universes : List Name} {context : VLCtx}
    {native : Expr} {semantic : VExpr} (translated : TrExprS env universes context native semantic) :
    ∀ name, hasExplicitConst name native = true → env.contains name := by
  induction translated with
  | bvar | fvar | sort | lit => intro name occurrence; simp [hasExplicitConst] at occurrence
  | const lookup _ _ =>
    intro name occurrence
    simp only [hasExplicitConst, beq_iff_eq] at occurrence
    subst name
    exact ⟨_, lookup⟩
  | app _ _ _ _ fnIH argIH =>
    intro name occurrence
    simp only [hasExplicitConst, Bool.or_eq_true] at occurrence
    exact occurrence.elim (fnIH name) (argIH name)
  | lam _ _ _ domainIH bodyIH | forallE _ _ _ _ domainIH bodyIH =>
    intro name occurrence
    simp only [hasExplicitConst, Bool.or_eq_true] at occurrence
    exact occurrence.elim (domainIH name) (bodyIH name)
  | letE _ _ _ _ domainIH valueIH bodyIH =>
    intro name occurrence
    simp only [hasExplicitConst, Bool.or_eq_true] at occurrence
    exact occurrence.elim (fun first => first.elim (domainIH name) (valueIH name)) (bodyIH name)
  | mdata _ ih | proj _ _ ih => exact ih

theorem noTranslation_of_absentExplicitConst
    {env : VEnv} {universes : List Name} {context : VLCtx} {native : Expr} {name : Name}
    (absent : env.constants name = none) (occurrence : hasExplicitConst name native = true) :
    ¬ ∃ semantic, TrExprS env universes context native semantic := by
  rintro ⟨semantic, translated⟩
  obtain ⟨constant, lookup⟩ := explicitConstPresent translated name occurrence
  rw [absent] at lookup
  cases lookup

theorem RegistrationEntry.RuleSemantics.afterInsertion
    {before after : VEnv} {models : List VConstVal} {entry : RegistrationEntry}
    (rules : entry.RuleSemantics before)
    (inserted : before.addConstructorHeaders models = some after) :
    entry.RuleSemantics after :=
  rules.mono (VEnv.addConstructorHeaders.le inserted)

/-- Head translation uses only the signature receipt and its actual insertion.
It does not assume any rule-body translation, so producers can use it before
assembling complete registration evidence. The caller's universes may differ
from the called signature's level-parameter names. -/
theorem recursorHeadAfterInsertion
    {safety : DefinitionSafety} {before after : VEnv} {models : List VConstVal}
    {info : RecursorVal} {model : VConstVal}
    (translated : TrConstVal safety before (.recInfo info) model)
    (member : model ∈ models) (inserted : before.addConstructorHeaders models = some after)
    (universes : List Name) (levels : List Level) (semanticLevels : List VLevel)
    (mapped : levels.mapM (VLevel.ofLevel universes) = some semanticLevels)
    (arity : levels.length = info.levelParams.length) (context : VLCtx) :
    TrExprS after universes context (.const info.name levels) (.const info.name semanticLevels) := by
  have installed := VEnv.addConstructorHeaders.constants inserted member
  have name : model.name = info.name := translated.2.symm
  rw [name] at installed
  exact .const installed mapped (arity.trans translated.1.2.1)

/-- A fresh recursor signature is absent at the constructor stage. -/
theorem RegistrationEvidence.recursorAbsentBefore
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : RecursorEntry} (member : entry ∈ evidence.recursors) :
    evidence.constructorEnv.constants entry.info.name = none := by
  have modelMember : entry.model ∈ evidence.recursors.map (·.model) :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  have absent := VEnv.addConstructorHeaders.fresh evidence.recursorAdd modelMember
  have name : entry.model.name = entry.info.name :=
    (evidence.recursorTranslation entry member).2.symm
  simpa only [name] using absent

/-- All mutual recursor heads are available after the whole signature batch. -/
theorem RegistrationEvidence.recursorHeadTranslation
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry : RecursorEntry} (member : entry ∈ evidence.recursors)
    (levels : List Level) (semanticLevels : List VLevel)
    (mapped : levels.mapM (VLevel.ofLevel entry.info.levelParams) = some semanticLevels)
    (arity : levels.length = entry.info.levelParams.length) (context : VLCtx) :
    TrExprS result entry.info.levelParams context (.const entry.info.name levels)
      (.const entry.info.name semanticLevels) := by
  have modelMember : entry.model ∈ evidence.recursors.map (·.model) :=
    List.mem_map.mpr ⟨entry, member, rfl⟩
  exact recursorHeadAfterInsertion (evidence.recursorTranslation entry member) modelMember
    evidence.recursorAdd entry.info.levelParams levels semanticLevels mapped arity context

/-- Any rule containing a fresh mutual recursor call cannot translate before insertion. -/
theorem RegistrationEvidence.recursiveRuleTranslationStages
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    {entry called : RecursorEntry} (member : entry ∈ evidence.recursors)
    (calledMember : called ∈ evidence.recursors) {rule : RecursorRule}
    (ruleMember : rule ∈ entry.info.rules)
    (recursiveCall : hasExplicitConst called.info.name rule.rhs = true) :
    (∃ semantic, TrExprS result entry.info.levelParams [] rule.rhs semantic) ∧
      ¬ ∃ semantic,
        TrExprS evidence.constructorEnv entry.info.levelParams [] rule.rhs semantic := by
  exact ⟨evidence.recursorRuleTranslation entry member rule ruleMember,
    noTranslation_of_absentExplicitConst (evidence.recursorAbsentBefore calledMember) recursiveCall⟩

end Lean4Lean.NativeInductive
