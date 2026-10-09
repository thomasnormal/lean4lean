import Lean4Lean.Verify.RecursorMinorOffsets

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  Lean4Lean.AddInductive.withLocalDeclWF from Lean4Lean.Verify.InductiveStats
open private Lean4Lean.AddInductive.loopU_WF from Lean4Lean.Verify.RecursorRuleShape

private theorem loopCtorArgs_loop_fields (stats : InductiveStats) (type : Expr) (index : Nat)
    (fields recursiveFields : Array Expr) (fuel : Nat)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hfvars : stats.ParamsAreFVars)
    (hnext : ∀ result finalFields finalRecursive current, ctx.HeaderFrame current →
      finalFields.size = fields.size +
        (declareConstructors.arity 0 type - (stats.params.size - index)) →
      (next result finalFields finalRecursive current).WF post) :
    (mkRecInfos.loopCtorArgs.loop stats next type index fields recursiveFields fuel ctx).WF post := by
  induction fuel generalizing type index fields recursiveFields ctx with
  | zero => exact Except.WF.throw
  | succ fuel ih =>
    rw [mkRecInfos.loopCtorArgs.loop.eq_def]
    split
    · rename_i name domain body bi
      cases hparam : stats.params[index]? with
      | some param =>
        have hindex : index < stats.params.size := by
          by_contra hbound
          simp [Array.getElem?_eq_none (show stats.params.size ≤ index by omega)] at hparam
        have heq : stats.params[index] = param := by
          simpa only [Array.getElem?_eq_getElem hindex, Option.some.injEq] using hparam
        have hmem : param ∈ stats.params := heq ▸ Array.getElem_mem hindex
        apply ih
        intro result finalFields finalRecursive current hframe hfields
        apply hnext result finalFields finalRecursive current hframe
        rw [hfvars.arity_instantiate1 hmem body 0] at hfields
        have harity : declareConstructors.arity 0 (.forallE name domain body bi) =
            1 + declareConstructors.arity 0 body := declareConstructors.arity_eq_add body 1
        rw [harity]
        omega
      | none =>
        have hindex : stats.params.size ≤ index := by simpa using hparam
        apply Lean4Lean.AddInductive.withLocalDeclWF
        intro arg current harg _ _ hframe
        apply Lean4Lean.AddInductive.bindWF
        intro recursive
        apply ih
        intro result finalFields finalRecursive final hfinal hfields
        apply hnext result finalFields finalRecursive final (hframe.trans hfinal)
        rw [declareConstructors.arity_instantiate1_of_isFVar body arg 0 harg] at hfields
        have harity : declareConstructors.arity 0 (.forallE name domain body bi) =
            1 + declareConstructors.arity 0 body := declareConstructors.arity_eq_add body 1
        simp only [Array.size_push] at hfields
        rw [harity]
        omega
    · apply hnext _ fields recursiveFields ctx (.refl ctx)
      simp [declareConstructors.arity]

theorem mkRecInfos.loopCtorArgs.fields (stats : InductiveStats) (type : Expr)
    (next : Expr → Array Expr → Array Expr → M α) (ctx : Context) (post : α → Prop)
    (hfvars : stats.ParamsAreFVars)
    (hnext : ∀ result fields recursiveFields current, ctx.HeaderFrame current →
      fields.size = declareConstructors.arity 0 type - stats.params.size →
      (next result fields recursiveFields current).WF post) :
    (mkRecInfos.loopCtorArgs stats type next ctx).WF post := by
  unfold mkRecInfos.loopCtorArgs
  apply Lean4Lean.AddInductive.readWF
  apply loopCtorArgs_loop_fields stats type 0 #[] #[] ctx.fuel.inductiveFuel next ctx post hfvars
  intro result fields recursiveFields current hframe hfields
  apply hnext result fields recursiveFields current hframe
  simpa using hfields

def RecursorRuleFields (stats : InductiveStats) (ctors : List Constructor)
    (rules : List RecursorRule) : Prop :=
  rules.map (fun rule => (rule.ctor, rule.nfields)) =
    ctors.map (fun ctor => (ctor.name, declareConstructors.arity 0 ctor.type - stats.params.size))

theorem RecursorRuleFields.at {stats : InductiveStats} {ctors : List Constructor}
    {rules : List RecursorRule} (hfields : RecursorRuleFields stats ctors rules)
    (index : Nat) (ctor : Constructor) (hctor : ctors[index]? = some ctor) :
    ∃ rule, rules[index]? = some rule ∧ rule.ctor = ctor.name ∧
      rule.nfields = declareConstructors.arity 0 ctor.type - stats.params.size := by
  have hget : (rules.map (fun rule => (rule.ctor, rule.nfields)))[index]? =
      some (ctor.name, declareConstructors.arity 0 ctor.type - stats.params.size) := by
    rw [hfields]
    simp [hctor]
  cases hrule : rules[index]? with
  | none => simp [hrule] at hget
  | some rule =>
    have heq : (rule.ctor, rule.nfields) =
        (ctor.name, declareConstructors.arity 0 ctor.type - stats.params.size) := by
      simpa [hrule] using hget
    exact ⟨rule, rfl, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

private theorem forIn_fields (stats : InductiveStats) (ctors : List Constructor)
    (initial : Array RecursorRule) (state : Nat) (ctx : Context)
    (step : Constructor → Array RecursorRule → StateT Nat M (ForInStep (Array RecursorRule)))
    (hstep : ∀ ctor rules state, (step ctor rules state ctx).WF fun result =>
      ∃ rule, result.1 = .yield (rules.push rule) ∧ rule.ctor = ctor.name ∧
        rule.nfields = declareConstructors.arity 0 ctor.type - stats.params.size) :
    (forIn ctors initial step state ctx).WF fun result =>
      result.1.toList.map (fun rule => (rule.ctor, rule.nfields)) =
        initial.toList.map (fun rule => (rule.ctor, rule.nfields)) ++
          ctors.map (fun ctor => (ctor.name, declareConstructors.arity 0 ctor.type - stats.params.size)) := by
  induction ctors generalizing initial state with
  | nil => exact .pure (by simp)
  | cons ctor ctors ih =>
    rw [List.forIn_cons]
    refine (hstep ctor initial state).bind ?_
    rintro ⟨result, nextState⟩ ⟨rule, hyield, hname, hfields⟩
    dsimp only at hyield
    subst result
    refine (ih (initial.push rule) nextState).mono ?_
    intro result halignment
    simpa [Array.toList_push, hname, hfields, List.append_assoc] using halignment

theorem mkRecRules.fieldCounts (types : Array InductiveType) (elimLevel : Level)
    (stats : InductiveStats) (index : Nat) (motives minors : Array Expr)
    (state : Nat) (ctx : Context) (hfvars : stats.ParamsAreFVars) :
    (mkRecRules types elimLevel stats index motives minors state ctx).WF fun result =>
      RecursorRuleFields stats types[index]!.ctors result.1 := by
  unfold mkRecRules
  dsimp only
  apply Except.WF.map
  · apply forIn_fields
    intro ctor rules minorIndex
    refine Except.WF.bind (Q := fun result : RecursorRule × Nat =>
      result.1.ctor = ctor.name ∧
        result.1.nfields = declareConstructors.arity 0 ctor.type - stats.params.size) ?_ ?_
    · apply mkRecInfos.loopCtorArgs.fields
      · exact hfvars
      · intro type fields recursiveFields current _ hfields
        apply Lean4Lean.AddInductive.loopU_WF
        intro values final
        apply Lean4Lean.AddInductive.bindWF
        intro lctx
        exact .pure ⟨rfl, hfields⟩
    · rintro ⟨rule, nextIndex⟩ ⟨hname, hfields⟩
      exact .pure ⟨rule, rfl, hname, hfields⟩
  · intro result halignment
    simpa [RecursorRuleFields] using halignment

theorem InductiveStats.RecursorMetadata.ruleFields {stats : InductiveStats}
    {types : Array InductiveType} {elimLevel : Level} {infos : Array RecInfo}
    {lparams : List Name} {lctx : LocalContext} {isK isUnsafe : Bool}
    {ctx : Context} {env : Kernel.Environment}
    (hmetadata : stats.RecursorMetadata types elimLevel infos lparams lctx isK isUnsafe ctx env)
    (hfvars : stats.ParamsAreFVars) :
    ∀ index, index < types.size → ∃ info : RecursorVal,
      env.find? (mkRecName types[index]!.name) = some (.recInfo info) ∧
      RecursorRuleFields stats types[index]!.ctors info.rules := by
  intro index hindex
  obtain ⟨rules, initial, final, hsource, hfind⟩ := hmetadata index hindex
  exact ⟨_, hfind, mkRecRules.fieldCounts types elimLevel stats index
    (infos.map (·.motive)) (infos.flatMap (·.minors)) initial ctx hfvars _ hsource⟩

def RuleConstructorFieldMetadata (types : Array InductiveType) (env : Kernel.Environment) : Prop :=
  ∀ parent, parent < types.size → ∃ recursor : RecursorVal,
    env.find? (mkRecName types[parent]!.name) = some (.recInfo recursor) ∧
    ∀ (index : Nat) (ctor : Constructor), types[parent]!.ctors[index]? = some ctor →
      ∃ (rule : RecursorRule) (info : ConstructorVal),
        recursor.rules[index]? = some rule ∧ env.find? ctor.name = some (.ctorInfo info) ∧
        rule.ctor = info.name ∧ rule.nfields = info.numFields

theorem InductiveStats.SafeRunMetadata.ruleConstructorFields {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hmetadata : stats.SafeRunMetadata nparams types numNested original root constructors env) :
    RuleConstructorFieldMetadata types env := by
  obtain ⟨_, _, _, _, _, _, hrecursors⟩ := hmetadata.recursors
  intro parent hparent
  obtain ⟨recursor, hfind, hfields⟩ :=
    hrecursors.ruleFields hmetadata.registration.traces.2.2.1 parent hparent
  refine ⟨recursor, hfind, ?_⟩
  intro index ctor hctor
  obtain ⟨rule, hrule, hname, hcount⟩ := hfields.at index ctor hctor
  have hmem : types[parent]! ∈ types := by
    simpa only [getElem!_pos, hparent] using (Array.getElem_mem (xs := types) (i := parent) hparent)
  obtain ⟨hfindCtor, _⟩ := hmetadata.toSafeRunRegistration.constructorMetadata
    types[parent]! hmem index ctor hctor
  exact ⟨rule, _, hrule, hfindCtor, hname, hcount⟩

theorem InductiveStats.SafeRunMinorOffsets.ruleConstructorFields {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    RuleConstructorFieldMetadata types env :=
  hoffsets.metadata.ruleConstructorFields

theorem run.safeRuleConstructorFields (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      env.constants.WF ∧
      (∀ name info, ctx.env.find? name = some info → env.find? name = some info) ∧
      RuleConstructorFieldMetadata types.toArray env := by
  refine (run.safeMinorOffsets nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hoffsets⟩
  exact ⟨hoffsets.resultWF, hoffsets.metadata.toSafeRunRegistration.preservesOriginal,
    hoffsets.ruleConstructorFields⟩

end Lean4Lean.AddInductive
