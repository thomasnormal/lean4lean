import Lean4Lean.Verify.RecursorRuleShape

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata
open private Lean4Lean.AddInductive.stateExceptBindWF from Lean4Lean.Verify.RecursorRegistration
open private Lean4Lean.AddInductive.stateBindResultWF from Lean4Lean.Verify.RecursorMetadata
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.getLCtxWF from Lean4Lean.Verify.InductiveRunMetadata

def recursorMinorOffset (types : Array InductiveType) (index : Nat) : Nat :=
  ((types.toList.take index).flatMap (·.ctors)).length

theorem recursorMinorOffset.zero (types : Array InductiveType) :
    recursorMinorOffset types 0 = 0 := rfl

theorem recursorMinorOffset.succ (types : Array InductiveType) (index : Nat)
    (hindex : index < types.size) :
    recursorMinorOffset types (index + 1) = recursorMinorOffset types index + types[index]!.ctors.length := by
  unfold recursorMinorOffset
  rw [List.take_succ_eq_append_getElem (by simpa using hindex)]
  simp [Array.getElem_toList, getElem!_pos, hindex]

theorem recursorMinorOffset.total (types : Array InductiveType) :
    recursorMinorOffset types types.size = (types.toList.flatMap (·.ctors)).length := by
  simp [recursorMinorOffset, ← Array.length_toList]

def InductiveStats.RecursorOffsetMetadata (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ index, index < types.size → ∃ rules,
    mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
      (recursorMinorOffset types index) ctx = .ok (rules, recursorMinorOffset types (index + 1)) ∧
    env.find? (mkRecName types[index]!.name) = some (.recInfo
      (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules))

theorem InductiveStats.RecursorOffsetMetadata.metadata {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env := by
  intro index hindex
  obtain ⟨rules, hsource, hfind⟩ := hmetadata index hindex
  exact ⟨rules, _, _, hsource, hfind⟩

theorem InductiveStats.RecursorOffsetMetadata.sourceRules {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ info : RecursorVal,
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        (recursorMinorOffset types index) ctx = .ok (info.rules, recursorMinorOffset types (index + 1)) := by
  intro index hindex
  obtain ⟨rules, hsource, hfind⟩ := hmetadata index hindex
  exact ⟨_, hfind, hsource⟩

private theorem forIn'_offsets (start count : Nat) (initial : Kernel.Environment)
    (ctx : Context) (offset : Nat → Nat)
    (step : (index : Nat) → index ∈ List.range' start count → Kernel.Environment →
      StateT Nat M (ForInStep Kernel.Environment)) (property : Nat → Kernel.Environment → Prop)
    (hwf : initial.constants.WF)
    (hmono : ∀ index before after,
      (∀ name info, before.find? name = some info → after.find? name = some info) →
      property index before → property index after)
    (hstep : ∀ index hmem env, env.constants.WF →
      (step index hmem env (offset index) ctx).WF fun result =>
        ∃ next, result.1 = .yield next ∧ next.constants.WF ∧
          (∀ name info, env.find? name = some info → next.find? name = some info) ∧
          property index next ∧ result.2 = offset (index + 1)) :
    (forIn' (List.range' start count) initial step (offset start) ctx).WF fun result =>
      result.1.constants.WF ∧
      (∀ name info, initial.find? name = some info → result.1.find? name = some info) ∧
      (∀ index ∈ List.range' start count, property index result.1) ∧
      result.2 = offset (start + count) := by
  induction count generalizing start initial with
  | zero => exact .pure ⟨hwf, fun _ _ hold => hold, by simp, by simp⟩
  | succ count ih =>
    simp only [List.range'_succ, Nat.add_one] at step hstep ⊢
    rw [List.forIn'_cons]
    refine (hstep start (by simp) initial hwf).bind ?_
    rintro ⟨result, nextState⟩ ⟨next, hyield, hnext, hkeep, hself, hstate⟩
    dsimp only at hyield hstate
    subst result
    subst nextState
    refine (ih (start + 1) next (fun index hmem env => step index (by simp [hmem]) env)
      hnext (fun index hmem env hwf => hstep index (by simp [hmem]) env hwf)).mono ?_
    rintro result ⟨hfinal, hrest, hitems, hstate⟩
    refine ⟨hfinal, fun name info hold => hrest name info (hkeep name info hold), ?_, ?_⟩
    · intro index hindex
      rcases List.mem_cons.mp hindex with rfl | hindex
      · exact hmono _ next result.1 hrest hself
      · exact hitems index hindex
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstate

theorem declareRecursors.offsetMetadata (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.RecursorOffsetMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env := by
  unfold declareRecursors
  dsimp only
  simp only [pure_bind, bind_pure]
  apply Except.WF.map
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_offsets (offset := recursorMinorOffset types)
      (property := fun index env => ∃ rules,
        mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
          (recursorMinorOffset types index) ctx = .ok (rules, recursorMinorOffset types (index + 1)) ∧
        env.find? (mkRecName types[index]!.name) = some (.recInfo
          (metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules)))
    · exact hwf
    · rintro index before after hkeep ⟨rules, hsource, hfind⟩
      exact ⟨rules, hsource, hkeep _ _ hfind⟩
    · intro index hindex env henv
      have hbound : index < types.size := by simpa using hindex
      apply Lean4Lean.AddInductive.stateBindResultWF
      intro rules nextState hsource
      have hadvance : nextState = recursorMinorOffset types (index + 1) := by
        rw [recursorMinorOffset.succ types index hbound]
        exact (mkRecRules.shape types elimLevel stats index (infos.map (·.motive))
          (infos.flatMap (·.minors)) (recursorMinorOffset types index) ctx _ hsource).stateAdvance
      refine Lean4Lean.AddInductive.stateExceptBindWF (Lean4Lean.checkName.WF env
        (mkRecName types[index].name) ctx.allowPrimitive) ?_
      rintro _ ⟨hfresh, _⟩
      let record := metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules
      have hfreshRecord : env.constants.find? (ConstantInfo.recInfo record).name = none := by
        simpa only [record, metadataVal, ConstantInfo.name, ConstantInfo.toConstantVal,
          getElem!_pos, hbound] using hfresh
      obtain ⟨hnext, hself, hkeep⟩ := Lean4Lean.AddInductive.addFresh env (.recInfo record) henv hfreshRecord
      refine .pure ⟨_, rfl, ?_, ?_, ⟨rules, ?_, ?_⟩, hadvance⟩
      · simpa only [record, metadataVal, getElem!_pos, hbound] using hnext
      · simpa only [record, metadataVal, getElem!_pos, hbound] using hkeep
      · simpa only [← hadvance] using hsource
      · simpa only [record, metadataVal, ConstantInfo.name, ConstantInfo.toConstantVal,
          getElem!_pos, hbound] using hself
  · rintro result ⟨hfinal, hkeep, hitems, _⟩
    exact ⟨hfinal, hkeep, fun index hindex => hitems index (by simpa using hindex)⟩

structure InductiveStats.SafeRunMinorOffsets (stats : InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment) : Prop
    extends stats.SafeRunRegistration nparams types numNested original root constructors env where
  recursors : ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context) (isK : Bool),
    ({ root with env := constructors } : Context).HeaderFrame source ∧
    RecursorInfoCounts types infos ∧
    stats.RecursorOffsetMetadata types elimLevel infos original.lparams source.lctx isK false source env

theorem InductiveStats.SafeRunMinorOffsets.metadata {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    stats.SafeRunMetadata nparams types numNested original root constructors env := by
  refine ⟨hoffsets.toSafeRunRegistration, ?_⟩
  obtain ⟨elimLevel, infos, source, isK, hframe, hcounts, hrecursors⟩ := hoffsets.recursors
  exact ⟨elimLevel, infos, source, isK, hframe, hcounts, hrecursors.metadata⟩

theorem InductiveStats.SafeRunMinorOffsets.sourceRules {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧
      ∀ index, index < types.size → ∃ info : RecursorVal,
        env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
        mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
          (recursorMinorOffset types index) source =
            .ok (info.rules, recursorMinorOffset types (index + 1)) := by
  obtain ⟨elimLevel, infos, source, _, hframe, hcounts, hrecursors⟩ := hoffsets.recursors
  exact ⟨elimLevel, infos, source, hframe, hcounts, hrecursors.sourceRules⟩

theorem run.safeMinorOffsets (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMinorOffsets nparams types.toArray numNested ctx root constructors env := by
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
  apply Lean4Lean.AddInductive.getLCtxWF
  apply Lean4Lean.AddInductive.bindWF
  intro isK
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  obtain ⟨_, _, _, _, hroot, _⟩ := hregistration.traces
  have hsafety : current.safety = .safe := hframe.safety.trans (hroot.safety.trans hsafety)
  rw [hsafety]
  refine (declareRecursors.offsetMetadata stats types.toArray elimLevel infos ctx.lparams current.lctx
    isK false current (by simpa only [hframe.env] using hregistration.resultWF)).mono ?_
  rintro env ⟨hfinal, hkeep, hrecursors⟩
  refine ⟨stats, root, constructors, ⟨hregistration, hfinal, ?_⟩,
    elimLevel, infos, current, isK, hframe, hcounts, hrecursors⟩
  intro name info hold
  apply hkeep name info
  simpa only [hframe.env] using hold

end Lean4Lean.AddInductive
