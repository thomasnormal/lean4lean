import Lean4Lean.Verify.InductiveRunPreservation
import Lean4Lean.Verify.RecursorInfoCounts

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

structure InductiveStats.SafeRunMetadata (stats : InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment) : Prop
    extends stats.SafeRunRegistration nparams types numNested original root constructors env where
  recursors : ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context) (isK : Bool),
    ({ root with env := constructors } : Context).HeaderFrame source ∧
    RecursorInfoCounts types infos ∧
    stats.RecursorMetadata types elimLevel infos original.lparams source.lctx isK false source env

theorem InductiveStats.SafeRunMetadata.declaredRecursors {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    stats.DeclaredRecursorCounts nparams types env := by
  obtain ⟨_, _, _, _, _, hcounts, hrecursors⟩ := hmetadata.recursors
  exact hrecursors.declaredCounts hmetadata.registration.traces.2.1 hcounts.size hcounts.minorTotal

theorem InductiveStats.SafeRunMetadata.sourceRules {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧
      ∀ index, index < types.size → ∃ (info : RecursorVal) (minorIndex nextIndex : Nat),
        env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
        mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
          minorIndex source = .ok (info.rules, nextIndex) := by
  obtain ⟨elimLevel, infos, source, _, hframe, hcounts, hrecursors⟩ := hmetadata.recursors
  exact ⟨elimLevel, infos, source, hframe, hcounts, hrecursors.sourceRules⟩

private theorem getLCtxWF {ctx : Context} {next : LocalContext → M α} {post : α → Prop}
    (hnext : (next ctx.lctx ctx).WF post) : ((getLCtx >>= next) ctx).WF post :=
  hnext

theorem run.safeMetadata (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMetadata nparams types.toArray numNested ctx root constructors env := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  rw [hsafety]
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply checkInductiveTypes.safeConstructorRegistration nparams types.toArray numNested _ ctx hwf
  intro stats root constructors hregistration
  apply Lean4Lean.AddInductive.bindWF
  intro elimLevel
  apply mkRecInfos.frameCounts
  intro infos current hframe hcounts
  apply getLCtxWF
  apply Lean4Lean.AddInductive.bindWF
  intro isK
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  obtain ⟨_, _, _, _, hroot, _⟩ := hregistration.traces
  have hsafety : current.safety = .safe := hframe.safety.trans (hroot.safety.trans hsafety)
  rw [hsafety]
  refine (declareRecursors.metadata stats types.toArray elimLevel infos ctx.lparams current.lctx
    isK false current (by simpa only [hframe.env] using hregistration.resultWF)).mono ?_
  rintro env ⟨hfinal, hkeep, hrecursors⟩
  refine ⟨stats, root, constructors, ⟨hregistration, hfinal, ?_⟩,
    elimLevel, infos, current, isK, hframe, hcounts, hrecursors⟩
  intro name info hold
  apply hkeep name info
  simpa only [hframe.env] using hold

theorem run.safeDeclaredMetadata (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      ∃ stats : InductiveStats,
        stats.HeaderMetadata nparams types.toArray numNested false ctx.lparams env ∧
        stats.ConstructorMetadata ctx.lparams types.toArray false env ∧
        DeclaredParameterMetadata nparams types.toArray env ∧
        stats.DeclaredRecursorCounts nparams types.toArray env := by
  refine (run.safeMetadata nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hmetadata⟩
  exact ⟨hmetadata.resultWF, hmetadata.toSafeRunRegistration.preservesOriginal, stats,
    hmetadata.toSafeRunRegistration.headerMetadata, hmetadata.toSafeRunRegistration.constructorMetadata,
    hmetadata.toSafeRunRegistration.declaredParameters, hmetadata.declaredRecursors⟩

end Lean4Lean.AddInductive
