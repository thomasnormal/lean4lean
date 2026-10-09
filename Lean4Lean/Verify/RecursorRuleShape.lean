import Lean4Lean.Verify.InductiveRunMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.loopCtorArgs_frame from Lean4Lean.Verify.RecursorInfoFrame

structure RecursorRuleShape (ctors : List Constructor) (rules : List RecursorRule)
    (initial final : Nat) : Prop where
  names : rules.map (·.ctor) = ctors.map (·.name)
  stateAdvance : final = initial + ctors.length

theorem RecursorRuleShape.count {ctors : List Constructor} {rules : List RecursorRule}
    {initial final : Nat} (hshape : RecursorRuleShape ctors rules initial final) :
    rules.length = ctors.length := by
  simpa using congrArg List.length hshape.names

private theorem loopU_WF (types : Array InductiveType) (stats : InductiveStats)
    (motives minors : Array Expr) (levels : List Level) (fields : Array Expr)
    (index : Nat) (values : Array Expr) (next : Array Expr → M (RecursorRule × Nat))
    (ctx : Context) (post : RecursorRule × Nat → Prop)
    (hnext : ∀ values current, (next values current).WF post) :
    (mkRecRules.loopU types stats motives minors levels fields index values next ctx).WF post := by
  rw [mkRecRules.loopU.eq_def]
  split
  · apply Lean4Lean.AddInductive.bindWF
    intro value
    apply loopU_WF
    exact hnext
  · exact hnext values ctx
termination_by fields.size - index
decreasing_by all_goals simp_wf; omega

private theorem forIn_shape (ctors : List Constructor) (initial : Array RecursorRule)
    (state : Nat) (ctx : Context)
    (step : Constructor → Array RecursorRule → StateT Nat M (ForInStep (Array RecursorRule)))
    (hstep : ∀ ctor rules state, (step ctor rules state ctx).WF fun result =>
      ∃ rule, result.1 = .yield (rules.push rule) ∧ rule.ctor = ctor.name ∧ result.2 = state + 1) :
    (forIn ctors initial step state ctx).WF fun result =>
      result.1.toList.map (·.ctor) = initial.toList.map (·.ctor) ++ ctors.map (·.name) ∧
      result.2 = state + ctors.length := by
  induction ctors generalizing initial state with
  | nil => exact .pure ⟨by simp, by simp⟩
  | cons ctor ctors ih =>
    rw [List.forIn_cons]
    refine (hstep ctor initial state).bind ?_
    rintro ⟨result, nextState⟩ ⟨rule, hyield, hname, hstate⟩
    dsimp only at hyield hstate
    subst result
    subst nextState
    refine (ih (initial.push rule) (state + 1)).mono ?_
    rintro result ⟨hnames, hfinal⟩
    constructor
    · simpa [Array.toList_push, hname, List.append_assoc] using hnames
    · simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfinal

theorem mkRecRules.shape (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (index : Nat) (motives minors : Array Expr)
    (state : Nat) (ctx : Context) :
    (mkRecRules types elimLevel stats index motives minors state ctx).WF fun result =>
      RecursorRuleShape types[index]!.ctors result.1 state result.2 := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply forIn_shape
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      result.1.ctor = ctor.name ∧ result.2 = minorIndex + 1) ?_ ?_
    · apply Lean4Lean.AddInductive.loopCtorArgs_frame
      intro type fields recursiveFields current _
      apply loopU_WF
      intro values final
      apply Lean4Lean.AddInductive.bindWF
      intro lctx
      exact .pure ⟨rfl, rfl⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hname, hstate⟩
      exact .pure ⟨rule, rfl, hname, hstate⟩
  · rintro result ⟨hnames, hstate⟩
    exact ⟨by simpa using hnames, hstate⟩

theorem InductiveStats.RecursorMetadata.ruleShape {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ (info : RecursorVal) (initial final : Nat),
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      RecursorRuleShape types[index]!.ctors info.rules initial final := by
  intro index hindex
  obtain ⟨rules, initial, final, hsource, hfind⟩ := hmetadata index hindex
  exact ⟨_, initial, final, hfind, mkRecRules.shape types elimLevel stats index
    (infos.map (·.motive)) (infos.flatMap (·.minors)) initial ctx _ hsource⟩

def OrderedRecursorRules (types : Array InductiveType) (env : Kernel.Environment) : Prop :=
  ∀ index, index < types.size → ∃ info : RecursorVal,
    env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
    info.rules.map (·.ctor) = types[index]!.ctors.map (·.name) ∧
    info.rules.length = types[index]!.ctors.length

theorem InductiveStats.RecursorMetadata.orderedRules {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    OrderedRecursorRules types env := by
  intro index hindex
  obtain ⟨info, _, _, hfind, hshape⟩ := hmetadata.ruleShape index hindex
  exact ⟨info, hfind, hshape.names, hshape.count⟩

theorem InductiveStats.SafeRunMetadata.orderedRules {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    OrderedRecursorRules types env := by
  obtain ⟨_, _, _, _, _, _, hrecursors⟩ := hmetadata.recursors
  exact hrecursors.orderedRules

theorem run.safeOrderedRules (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      OrderedRecursorRules types.toArray env := by
  refine (run.safeMetadata nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hmetadata⟩
  exact ⟨hmetadata.resultWF, hmetadata.toSafeRunRegistration.preservesOriginal,
    hmetadata.orderedRules⟩

end Lean4Lean.AddInductive
