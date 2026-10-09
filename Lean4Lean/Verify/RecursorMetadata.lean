import Lean4Lean.Verify.RecursorRegistration

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata
open private Lean4Lean.AddInductive.stateExceptBindWF from Lean4Lean.Verify.RecursorRegistration

def declareRecursors.metadataVal (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (index : Nat) (rules : List RecursorRule) : RecursorVal :=
  let motives := infos.map (·.motive)
  let minors := infos.flatMap (·.minors)
  let info := infos[index]!
  let type := lctx.mkForall stats.params <|
    lctx.mkForall motives <|
    lctx.mkForall minors <|
    lctx.mkForall info.indices <|
    lctx.mkForall #[info.major] <|
    .app (mkAppN info.motive info.indices) info.major
  { name := mkRecName types[index]!.name, levelParams := getRecLevelParams elimLevel lparams,
    type := type.inferImplicit 1000 false, all := (types.map (·.name)).toList,
    numParams := stats.params.size, numIndices := stats.nindices[index]!,
    numMotives := motives.size, numMinors := minors.size, rules, k := isK, isUnsafe }

def InductiveStats.RecursorMetadata (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (env : Kernel.Environment) : Prop :=
  ∀ index, index < types.size → ∃ rules minorIndex nextIndex,
    mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
      minorIndex ctx = .ok (rules, nextIndex) ∧
    env.find? (mkRecName types[index]!.name) = some (.recInfo
      (declareRecursors.metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules))

def InductiveStats.DeclaredRecursorCounts (stats : InductiveStats) (nparams : Nat)
    (types : Array InductiveType) (env : Kernel.Environment) : Prop :=
  ∀ index, index < types.size → ∃ info : RecursorVal,
    env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
    info.numParams = nparams ∧ info.numIndices = stats.nindices[index]! ∧
    info.numMotives = types.size ∧ info.numMinors = (types.toList.flatMap (·.ctors)).length ∧
    info.all = (types.map (·.name)).toList

theorem InductiveStats.RecursorMetadata.sourceRules {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool} {ctx : Context}
    {env : Kernel.Environment}
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env) :
    ∀ index, index < types.size → ∃ (info : RecursorVal) (minorIndex nextIndex : Nat),
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (info.rules, nextIndex) := by
  intro index hindex
  obtain ⟨rules, minorIndex, nextIndex, hsource, hfind⟩ := hmetadata index hindex
  exact ⟨_, minorIndex, nextIndex, hfind, hsource⟩

theorem InductiveStats.RecursorMetadata.declaredCounts {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool} {ctx : Context}
    {env : Kernel.Environment} {nparams : Nat}
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hparams : stats.ParamsCount nparams types.size) (hmotives : infos.size = types.size)
    (hminors : (infos.flatMap (·.minors)).size = (types.toList.flatMap (·.ctors)).length) :
    stats.DeclaredRecursorCounts nparams types env := by
  intro index hindex
  obtain ⟨rules, _, _, _, hfind⟩ := hmetadata index hindex
  have hnonempty : types.size ≠ 0 := by omega
  have hcount : stats.params.size = nparams := by
    simpa [InductiveStats.ParamsCount, hnonempty] using hparams
  refine ⟨_, hfind, ?_⟩
  simp [declareRecursors.metadataVal, hcount, hmotives, hminors]

private theorem forIn'_metadata (items : List α) (initial : Kernel.Environment)
    (state : Nat) (ctx : Context)
    (step : (item : α) → item ∈ items → Kernel.Environment → StateT Nat M
      (ForInStep Kernel.Environment)) (property : α → Kernel.Environment → Prop)
    (hwf : initial.constants.WF)
    (hmono : ∀ item before after,
      (∀ name info, before.find? name = some info → after.find? name = some info) →
      property item before → property item after)
    (hstep : ∀ item hmem env state, env.constants.WF →
      (step item hmem env state ctx).WF fun result =>
        ∃ next, result.1 = .yield next ∧ next.constants.WF ∧
          (∀ name info, env.find? name = some info → next.find? name = some info) ∧ property item next) :
    (forIn' items initial step state ctx).WF fun result => result.1.constants.WF ∧
      (∀ name info, initial.find? name = some info → result.1.find? name = some info) ∧
      ∀ item ∈ items, property item result.1 := by
  induction items generalizing initial state with
  | nil => exact .pure ⟨hwf, fun _ _ hold => hold, by simp⟩
  | cons item items ih =>
    rw [List.forIn'_cons]
    refine (hstep item (by simp) initial state hwf).bind ?_
    rintro ⟨_, nextState⟩ ⟨next, rfl, hnext, hkeep, hself⟩
    refine (ih next nextState (fun entry hmem env => step entry (by simp [hmem]) env)
      hnext (fun entry hmem env state hwf => hstep entry (by simp [hmem]) env state hwf)).mono ?_
    rintro result ⟨hfinal, hrest, hitems⟩
    refine ⟨hfinal, fun name info hold => hrest name info (hkeep name info hold), ?_⟩
    intro entry hentry
    rcases List.mem_cons.mp hentry with rfl | hentry
    · exact hmono _ next result.1 hrest hself
    · exact hitems entry hentry

private theorem stateBindResultWF {action : StateT Nat M α} {next : α → StateT Nat M β}
    {state : Nat} {ctx : Context} {post : β × Nat → Prop}
    (hnext : ∀ result nextState, action state ctx = .ok (result, nextState) →
      (next result nextState ctx).WF post) : ((action >>= next) state ctx).WF post := by
  exact (show (action state ctx).WF (fun result => action state ctx = .ok result) from
    fun _ hresult => hresult).bind fun result hresult => hnext result.1 result.2 hresult

theorem declareRecursors.metadata (stats : InductiveStats) (types : Array InductiveType)
    (elimLevel : Level) (infos : Array RecInfo) (lparams : List Name)
    (lctx : LocalContext) (isK isUnsafe : Bool) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (declareRecursors stats types elimLevel infos lparams lctx isK isUnsafe ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env := by
  unfold declareRecursors
  dsimp only
  simp only [pure_bind, bind_pure]
  apply Except.WF.map
  · simp only [Std.Legacy.Range.forIn'_eq_forIn'_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    apply forIn'_metadata (property := fun index env => ∃ rules minorIndex nextIndex,
      mkRecRules types elimLevel stats index (infos.map (·.motive)) (infos.flatMap (·.minors))
        minorIndex ctx = .ok (rules, nextIndex) ∧
      env.find? (mkRecName types[index]!.name) = some (.recInfo
        (metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules)))
    · exact hwf
    · rintro index before after hkeep ⟨rules, minorIndex, nextIndex, hsource, hfind⟩
      exact ⟨rules, minorIndex, nextIndex, hsource, hkeep _ _ hfind⟩
    · intro index hindex env state henv
      have hbound : index < types.size := by simpa using hindex
      apply stateBindResultWF
      intro rules nextState hsource
      refine Lean4Lean.AddInductive.stateExceptBindWF (Lean4Lean.checkName.WF env
        (mkRecName types[index].name) ctx.allowPrimitive) ?_
      rintro _ ⟨hfresh, _⟩
      let record := metadataVal stats types elimLevel infos lparams lctx isK isUnsafe index rules
      have hfreshRecord : env.constants.find? (ConstantInfo.recInfo record).name = none := by
        simpa only [record, metadataVal, ConstantInfo.name, ConstantInfo.toConstantVal,
          getElem!_pos, hbound] using hfresh
      obtain ⟨hnext, hself, hkeep⟩ :=
        Lean4Lean.AddInductive.addFresh env (.recInfo record) henv hfreshRecord
      refine .pure ⟨_, rfl, ?_, ?_, rules, state, nextState, hsource, ?_⟩
      · simpa only [record, metadataVal, getElem!_pos, hbound] using hnext
      · simpa only [record, metadataVal, getElem!_pos, hbound] using hkeep
      · simpa only [record, metadataVal, ConstantInfo.name, ConstantInfo.toConstantVal,
          getElem!_pos, hbound] using hself
  · rintro result ⟨hfinal, hkeep, hitems⟩
    refine ⟨hfinal, hkeep, ?_⟩
    intro index hindex
    exact hitems index (by simpa using hindex)

end Lean4Lean.AddInductive
