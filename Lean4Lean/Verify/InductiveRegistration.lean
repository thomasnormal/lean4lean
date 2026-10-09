import Lean4Lean.Verify.InductivePositivity
import Lean4Lean.Verify.InductiveMetadata

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

structure InductiveStats.SafeConstructorRegistration (stats : InductiveStats)
    (nparams : Nat) (indTypes : Array InductiveType) (numNested : Nat)
    (original root : Context) (env : Kernel.Environment) : Prop where
  traces : stats.RegisteredSafeConstructorTraces nparams indTypes original root
  headerWF : root.env.constants.WF
  resultWF : env.constants.WF
  toHeaders : ∀ name info, original.env.find? name = some info → root.env.find? name = some info
  fromHeaders : ∀ name info, root.env.find? name = some info → env.find? name = some info
  headerMetadata : stats.HeaderMetadata nparams indTypes numNested false original.lparams root.env
  resultHeaderMetadata : stats.HeaderMetadata nparams indTypes numNested false original.lparams env
  constructorMetadata : stats.ConstructorMetadata original.lparams indTypes false env

theorem InductiveStats.SafeConstructorRegistration.preservesOriginal {stats : InductiveStats}
    {nparams numNested : Nat} {indTypes : Array InductiveType} {original root : Context}
    {env : Kernel.Environment}
    (hregistration : stats.SafeConstructorRegistration nparams indTypes numNested original root env) :
    ∀ name info, original.env.find? name = some info → env.find? name = some info :=
  fun name info hold => hregistration.fromHeaders name info (hregistration.toHeaders name info hold)

theorem InductiveStats.SafeConstructorRegistration.declaredParameters {stats : InductiveStats}
    {nparams numNested : Nat} {indTypes : Array InductiveType} {original root : Context}
    {env : Kernel.Environment}
    (hregistration : stats.SafeConstructorRegistration nparams indTypes numNested original root env) :
    DeclaredParameterMetadata nparams indTypes env :=
  stats.declaredParameterMetadata nparams indTypes numNested false original.lparams env
    hregistration.traces.2.1 hregistration.resultHeaderMetadata hregistration.constructorMetadata

theorem checkInductiveTypes.safeConstructorRegistration (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat)
    (next : InductiveStats → Context → M α) (ctx : Context)
    (hwf : ctx.env.constants.WF) (post : α → Prop)
    (hnext : ∀ stats root env,
      stats.SafeConstructorRegistration nparams indTypes numNested ctx root env →
      (next stats root { root with env }).WF post) :
    (checkInductiveTypes nparams indTypes (fun stats => do
      withEnv (← declareInductiveTypes stats nparams indTypes numNested false) do
        checkConstructors indTypes stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats indTypes false) do
          next stats root) ctx).WF post := by
  apply checkInductiveTypes.frameHeaderSizesParamsCountDistinct
  intro stats current hsizes hcount hfvars hnodup hframe
  have hcurrent : current.env.constants.WF := by simpa only [hframe.env] using hwf
  refine (declareInductiveTypes.metadata stats nparams indTypes numNested false current
    hcurrent hsizes.1).bind ?_
  rintro headers ⟨hheadersWF, hpreserve, hheaders⟩
  let root := { current with env := headers }
  have hchecked : (checkConstructors indTypes stats false root).WF fun _ =>
      stats.SafeConstructorTraces indTypes PositivityWHNF root ∧
        ∀ indType ∈ indTypes, ∀ ctor ∈ indType.ctors,
          stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
    fun result hresult => ⟨checkConstructors.safeTraces indTypes stats root result hresult,
      checkConstructors.arity indTypes stats false root hfvars hnodup result hresult⟩
  refine hchecked.bind ?_
  rintro _ ⟨htraces, hbound⟩
  refine (declareConstructors.metadata stats indTypes false root hheadersWF hbound).bind ?_
  rintro env ⟨hfinal, hkeep, hctors⟩
  apply hnext stats root env
  refine ⟨⟨hsizes, hcount, hfvars, hnodup,
    ⟨rfl, hframe.lparams, hframe.safety, hframe.allowPrimitive, hframe.fuel⟩, htraces⟩,
    hheadersWF, hfinal, ?_, hkeep, ?_, ?_, ?_⟩
  · simpa only [hframe.env] using hpreserve
  · simpa only [hframe.lparams] using hheaders
  · intro parent hparent
    apply hkeep
    simpa only [hframe.lparams] using hheaders parent hparent
  · simpa only [root, hframe.lparams] using hctors

theorem checkInductiveTypes.getSafeConstructorRegistration (nparams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (ctx : Context)
    (hwf : ctx.env.constants.WF) :
    (checkInductiveTypes nparams indTypes (fun stats => do
      withEnv (← declareInductiveTypes stats nparams indTypes numNested false) do
        checkConstructors indTypes stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats indTypes false) do
          return (stats, root, (← readThe Context).env)) ctx).WF fun result =>
      result.1.SafeConstructorRegistration nparams indTypes numNested ctx result.2.1 result.2.2 := by
  apply checkInductiveTypes.safeConstructorRegistration nparams indTypes numNested _ ctx hwf
  intro stats root env hregistration
  exact .pure hregistration

theorem run.safeConstructorRegistration (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun _ =>
      ∃ (stats : InductiveStats) (root : Context) (env : Kernel.Environment),
        stats.SafeConstructorRegistration nparams types.toArray numNested ctx root env := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  rw [hsafety]
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply checkInductiveTypes.safeConstructorRegistration nparams types.toArray numNested _ ctx hwf
  intro stats root env hregistration
  exact fun _ _ => ⟨stats, root, env, hregistration⟩

theorem run.safeConstructorTraces (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun _ =>
      ∃ (stats : InductiveStats) (root : Context), root.safety = .safe ∧
        stats.SafeConstructorTraces types.toArray PositivityWHNF root := by
  refine (run.safeConstructorRegistration nparams types numNested ctx hsafety hwf).mono ?_
  rintro _ ⟨stats, root, env, hregistration⟩
  obtain ⟨_, _, _, _, hframe, htraces⟩ := hregistration.traces
  exact ⟨stats, root, hframe.safety.trans hsafety, htraces⟩

end Lean4Lean.AddInductive
