import Lean4Lean.Verify.InductiveCPS
import Lean4Lean.Verify.RecursorFieldDistinct

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

theorem checkInductiveTypes.safeScopedConstructorRegistration (nparams : Nat)
    (types : Array InductiveType) (numNested : Nat) (next : InductiveStats → Context → M ResultType)
    (ctx : Context) (hmap : ctx.env.constants.WF) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) (post : ResultType → Prop)
    (hnext : ∀ stats root env,
      stats.SafeConstructorRegistration nparams types numNested ctx root env →
      ({ ctx with env := root.env } : Context).RecursorScopeFrame root →
      (next stats root { root with env }).WF post) :
    (checkInductiveTypes nparams types (fun stats => do
      withEnv (← declareInductiveTypes stats nparams types numNested false) do
        checkConstructors types stats false
        let root ← readThe Context
        withEnv (← declareConstructors stats types false) do
          next stats root) ctx).WF post := by
  apply checkInductiveTypes.scopedStats
  · exact hwf
  · exact hreserved
  intro stats current hframe hsizes hcount hfvars hnodup
  have hcurrent : current.env.constants.WF := by simpa only [hframe.env] using hmap
  refine (declareInductiveTypes.metadata stats nparams types numNested false current hcurrent hsizes.1).bind ?_
  rintro headers ⟨hheadersWF, hpreserve, hheaders⟩
  let root := { current with env := headers }
  have hchecked : (checkConstructors types stats false root).WF fun _ =>
      stats.SafeConstructorTraces types PositivityWHNF root ∧
        ∀ type ∈ types, ∀ ctor ∈ type.ctors, stats.params.size ≤ declareConstructors.arity 0 ctor.type :=
    fun result hresult => ⟨checkConstructors.safeTraces types stats root result hresult,
      checkConstructors.arity types stats false root hfvars hnodup result hresult⟩
  refine hchecked.bind ?_
  rintro _ ⟨htraces, hbound⟩
  refine (declareConstructors.metadata stats types false root hheadersWF hbound).bind ?_
  rintro env ⟨hfinal, hkeep, hctors⟩
  apply hnext stats root env
  · refine ⟨⟨hsizes, hcount, hfvars, hnodup,
      ⟨rfl, hframe.lparams, hframe.safety, hframe.allowPrimitive, hframe.fuel⟩, htraces⟩,
      hheadersWF, hfinal, ?_, hkeep, ?_, ?_, ?_⟩
    · simpa only [hframe.env] using hpreserve
    · simpa only [hframe.lparams] using hheaders
    · intro parent hparent
      apply hkeep
      simpa only [hframe.lparams] using hheaders parent hparent
    · simpa only [root, hframe.lparams] using hctors
  · exact hframe.withEnv headers

structure InductiveStats.SafeRunScope (stats : InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment) : Prop
    extends stats.SafeRunRegistration nparams types numNested original root constructors env where
  rootScope : ({ original with env := root.env } : Context).RecursorScopeFrame root
  recursors : ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context) (isK : Bool),
    ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
    RecursorInfoCounts types infos ∧
    stats.RecursorOffsetMetadata types elimLevel infos original.lparams source.lctx isK false source env ∧
    LocalRecursorRuleRhsDistinct stats types infos source env

theorem InductiveStats.SafeRunScope.minorOffsets {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    stats.SafeRunMinorOffsets nparams types numNested original root constructors env := by
  refine ⟨hscope.toSafeRunRegistration, ?_⟩
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hmetadata, _⟩ := hscope.recursors
  exact ⟨elimLevel, infos, source, isK, hframe.toHeaderFrame, hcounts, hmetadata⟩

theorem InductiveStats.SafeRunScope.localRules {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhsDistinct stats types infos source env := by
  obtain ⟨_, infos, source, _, hframe, hcounts, _, hdistinct⟩ := hscope.recursors
  exact ⟨infos, source, hframe, hcounts, hdistinct⟩

theorem InductiveStats.SafeRunScope.originalSource {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hscope : stats.SafeRunScope nparams types numNested original root constructors env) :
    ∃ (infos : Array RecInfo) (source : Context),
      ({ original with env := constructors } : Context).RecursorScopeFrame source ∧
      RecursorInfoCounts types infos ∧ LocalRecursorRuleRhsDistinct stats types infos source env := by
  obtain ⟨infos, source, hframe, hcounts, hdistinct⟩ := hscope.localRules
  exact ⟨infos, source, (hscope.rootScope.withEnv constructors).trans hframe, hcounts, hdistinct⟩

theorem run.safeScope (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hmap : ctx.env.constants.WF)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunScope nparams types.toArray numNested ctx root constructors env := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  rw [hsafety]
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply checkInductiveTypes.safeScopedConstructorRegistration nparams types.toArray numNested _ ctx hmap hwf hreserved
  intro stats root constructors hregistration hroot
  apply Lean4Lean.AddInductive.bindWF
  intro elimLevel
  apply mkRecInfos.scopedCounts
  · exact hroot.wf
  · exact hroot.reserved
  intro infos current hframe hcounts
  apply Lean4Lean.AddInductive.getLCtxWF
  apply Lean4Lean.AddInductive.bindWF
  intro isK
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  have hsafe : current.safety = .safe := hframe.safety.trans (hroot.safety.trans hsafety)
  rw [hsafe]
  refine (declareRecursors.offsetMetadata stats types.toArray elimLevel infos ctx.lparams current.lctx
    isK false current (by simpa only [hframe.env] using hregistration.resultWF)).mono ?_
  rintro env ⟨hfinal, hkeep, hmetadata⟩
  refine ⟨stats, root, constructors, ⟨hregistration, hfinal, ?_⟩, hroot,
    elimLevel, infos, current, isK, hframe, hcounts, hmetadata,
    hmetadata.localRuleRhsDistinct hcounts hframe.wf hframe.reserved⟩
  intro name info hold
  apply hkeep name info
  simpa only [hframe.env] using hold

theorem run.safeRhsDistinct (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hsafety : ctx.safety = .safe) (hmap : ctx.env.constants.WF)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (run nparams types numNested ctx).WF fun env => env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment)
        (infos : Array RecInfo) (source : Context),
        stats.SafeRunScope nparams types.toArray numNested ctx root constructors env ∧
        ({ root with env := constructors } : Context).RecursorScopeFrame source ∧
        RecursorInfoCounts types.toArray infos ∧ LocalRecursorRuleRhsDistinct stats types.toArray infos source env := by
  refine (run.safeScope nparams types numNested ctx hsafety hmap hwf hreserved).mono ?_
  rintro env ⟨stats, root, constructors, hscope⟩
  obtain ⟨infos, source, hframe, hcounts, hdistinct⟩ := hscope.localRules
  exact ⟨hscope.resultWF, hscope.toSafeRunRegistration.preservesOriginal,
    stats, root, constructors, infos, source, hscope, hframe, hcounts, hdistinct⟩

end Lean4Lean.AddInductive
