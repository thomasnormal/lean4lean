import Lean4Lean.Theory.Typing.QuotInjectivity
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean.VEnv.QuotConfluenceObstruction
open VExpr
open private notProofOfSortTelescope from Lean4Lean.Theory.Typing.QuotInjectivity
open private quotientExtension from Lean4Lean.Theory.Typing.RewriteRules

variable {environment : VEnv}

theorem equalityRegistered (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) : environment.QuotReady := by
  obtain ⟨declarations, wellFormed⟩ := environmentWF
  induction wellFormed with
  | empty => cases registered
  | decl declaration _ induction =>
    cases declaration with
    | «axiom» _ added | «opaque» _ added =>
      rw [VEnv.addConst.defeqs_eq added] at registered
      exact (VEnv.addConst_le added).constants (induction registered)
    | «def» _ added =>
      rcases registered with newEquation | oldEquation
      · cases congrArg VDefEq.lhs newEquation
      · rw [VEnv.addConst.defeqs_eq added] at oldEquation
        exact ((VEnv.addConst_le added).trans VEnv.addDefEq_le).constants (induction oldEquation)
    | mutualDef _ added _ =>
      rcases (VEnv.addDefEqs_defeqs ..).mp registered with ⟨definition, _, impossible⟩ | old
      · cases congrArg VDefEq.lhs impossible
      · rw [VEnv.addConsts_defeqs added] at old
        exact ((VEnv.addConsts_le added).trans (VEnv.addDefEqs_extension ..)).constants
          (induction old)
    | «example» _ => exact induction registered
    | quot ready added => exact (quotientExtension added).1.constants ready
    | induct _ added =>
      rw [VEnv.addInduct.defeqs_eq added] at registered
      exact (VEnv.addInduct.le added).constants (induction registered)

def relationType : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))

def functionType : VExpr := .forallE (.bvar 1) (.sort .zero)

def respectType : VExpr :=
  .forallE (.bvar 2) (.forallE (.bvar 3)
    (.forallE (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0))
      (.app (.app (.app (.const ``Eq [.succ .zero]) (.sort .zero))
        (.app (.bvar 3) (.bvar 2))) (.app (.bvar 3) (.bvar 1)))))

def quotient (domain relation : VExpr) : VExpr :=
  .app (.app (.const ``Quot [.zero]) domain) relation

def locals : List VExpr :=
  quotient (.bvar 4) (.bvar 3) :: .bvar 3 :: respectType :: functionType :: relationType :: [.sort .zero]

def majorType : VExpr := quotient (.bvar 5) (.bvar 4)

def constructor : VExpr :=
  .app (.app (.app (.const ``Quot.mk [.zero]) (.bvar 5)) (.bvar 4)) (.bvar 1)

def eliminator : VExpr :=
  .app (.app (.app (.app (.app (.const ``Quot.lift [.zero, .succ .zero])
    (.bvar 5)) (.bvar 4)) (.sort .zero)) (.bvar 3)) (.bvar 2)

def neutral : VExpr := .app eliminator (.bvar 0)

def redex : VExpr := .app eliminator constructor

def reduced : VExpr := .app (.bvar 3) (.bvar 1)

theorem localsWF (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    OnCtx locals (environment.IsType 0) := by
  have equal := equalityRegistered environmentWF registered
  obtain ⟨_, _, _, _, quotientRegistered, _⟩ := environmentWF.quotientObjects registered
  unfold locals quotient respectType functionType relationType
  exact ⟨⟨⟨⟨⟨⟨trivial, _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩,
    _, by type_tac⟩, _, by type_tac⟩, _, by type_tac⟩

theorem prefixTyped (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.HasType 0 locals eliminator (.forallE majorType (.sort .zero)) := by
  obtain ⟨_, _, liftRegistered, _, _⟩ := environmentWF.quotientObjects registered
  unfold eliminator majorType quotient locals respectType functionType relationType
  type_tac

theorem constructorTyped (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.HasType 0 locals constructor majorType := by
  obtain ⟨_, _, _, constructorRegistered, _⟩ := environmentWF.quotientObjects registered
  unfold constructor majorType quotient locals respectType functionType relationType
  type_tac

theorem majorTyped : environment.HasType 0 locals (.bvar 0) majorType := by
  unfold locals majorType quotient
  type_tac

theorem majorTypeTyped (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.HasType 0 locals majorType (.sort .zero) := by
  obtain ⟨_, _, _, _, quotientRegistered, _⟩ := environmentWF.quotientObjects registered
  unfold majorType quotient locals respectType functionType relationType
  type_tac

theorem neutralTyped (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.HasType 0 locals neutral (.sort .zero) :=
  (prefixTyped environmentWF registered).app majorTyped

theorem normalEq (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    @NormalEq (environmentWF.reductionParams 0) locals neutral redex := by
  letI := environmentWF.reductionParams 0
  exact .appDF (prefixTyped environmentWF registered) (prefixTyped environmentWF registered)
    majorTyped (constructorTyped environmentWF registered) (.refl (prefixTyped environmentWF registered))
    (.proofIrrel (majorTypeTyped environmentWF registered) majorTyped (constructorTyped environmentWF registered))

theorem reduction (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    @ParRed (environmentWF.reductionParams 0) locals redex reduced := by
  letI := environmentWF.reductionParams 0
  have functionMatched := Pattern.Matches.const (c := ``Quot.lift) (ls := [.zero, .succ .zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .sort .zero)
    |>.var (a' := .bvar 3) |>.var (a' := .bvar 2)
  have constructorMatched := Pattern.Matches.const (c := ``Quot.mk) (ls := [.zero])
    |>.var (a' := .bvar 5) |>.var (a' := .bvar 4) |>.var (a' := .bvar 1)
  exact .extra (Γ := locals) (.quot registered) (functionMatched.app constructorMatched)
    ⟨⟨.sort .zero, by
        change environment.HasType 0 locals (.bvar 5) (.sort .zero)
        unfold locals respectType functionType relationType quotient
        type_tac⟩,
      ⟨.forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero)), by
        change environment.HasType 0 locals (.bvar 4) _
        unfold locals respectType functionType relationType quotient
        type_tac⟩, trivial⟩ (fun _ => .rfl)

theorem semanticEquality (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    environment.IsDefEq 0 locals neutral reduced (.sort .zero) := by
  letI := environmentWF.reductionParams 0
  have contextWF := localsWF environmentWF registered
  have first := (normalEq environmentWF registered).defeq contextWF
    |>.of_l environmentWF contextWF (neutralTyped environmentWF registered)
  exact first.trans ((reduction environmentWF registered).defeq contextWF first.hasType.2)

private def inert : VExpr → Prop
  | .bvar _ | .sort _ => True
  | .const name _ => name = ``Quot.lift
  | .app function argument => inert function ∧ inert argument
  | _ => False

private theorem inert.not_constructor {expression : VExpr} (shape : inert expression)
    (matched : (Pattern.varN (.const ``Quot.mk) count).Matches expression levels values) : False := by
  induction count generalizing expression with
  | zero =>
    cases matched
    exact (by decide : (``Quot.mk : Name) ≠ ``Quot.lift) shape
  | succ count induction =>
    cases matched with
    | var earlier => exact induction shape.1 earlier

private theorem inert.parRed (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (reduction : @ParRed (environmentWF.reductionParams 0) context source target)
    (shape : inert source) : target = source := by
  induction reduction with
  | bvar | sort | const => rfl
  | app _ _ functionIH argumentIH => rw [functionIH shape.1, argumentIH shape.2]
  | lam | forallE => cases shape
  | beta => cases shape.1
  | extra rule matched _ _ =>
    exfalso
    cases rule with
    | delta closed definitionRegistered =>
      cases matched
      exact environmentWF.rewriteMetadata.quotientNames definitionRegistered registered
        ``Quot.lift (by simp) shape
    | quot =>
      cases matched with
      | app _ majorMatched => exact shape.2.not_constructor majorMatched

theorem neutralReduction (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq)
    (reduction : @ParRedS (environmentWF.reductionParams 0) locals neutral target) : target = neutral := by
  induction reduction with
  | rfl => rfl
  | tail _ step induction =>
    subst induction
    exact inert.parRed environmentWF registered step (by trivial)

theorem not_normalEq_reduced (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    ¬@NormalEq (environmentWF.reductionParams 0) locals neutral reduced := by
  letI := environmentWF.reductionParams 0
  intro equal
  cases equal with
  | appDF _ _ _ _ functionEqual _ =>
    cases functionEqual with
    | proofIrrel propositionTyped proofTyped _ =>
      exact notProofOfSortTelescope environmentWF (localsWF environmentWF registered)
        (by trivial) (prefixTyped environmentWF registered) propositionTyped proofTyped
  | proofIrrel propositionTyped proofTyped _ =>
    exact notProofOfSortTelescope environmentWF (localsWF environmentWF registered)
      (by trivial) (neutralTyped environmentWF registered) propositionTyped proofTyped

theorem not_simulated (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    ¬∃ target, @ParRedS (environmentWF.reductionParams 0) locals neutral target ∧
      @NormalEq (environmentWF.reductionParams 0) locals target reduced := by
  rintro ⟨target, steps, equal⟩
  have same := neutralReduction environmentWF registered steps
  subst target
  exact not_normalEq_reduced environmentWF registered equal

theorem counterexample (environmentWF : environment.WF)
    (registered : environment.defeqs quotDefEq) :
    OnCtx locals (environment.IsType 0) ∧
      @NormalEq (environmentWF.reductionParams 0) locals neutral redex ∧
      @ParRed (environmentWF.reductionParams 0) locals redex reduced ∧
      ¬∃ target, @ParRedS (environmentWF.reductionParams 0) locals neutral target ∧
        @NormalEq (environmentWF.reductionParams 0) locals target reduced :=
  ⟨localsWF environmentWF registered, normalEq environmentWF registered,
    reduction environmentWF registered, not_simulated environmentWF registered⟩

end Lean4Lean.VEnv.QuotConfluenceObstruction
