import Lean4Lean.Verify.InductiveFrontendScope

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata

theorem restorationAddFresh (env : Environment) (info : ConstantInfo)
    (hwf : env.constants.WF) (hfresh : env.constants.find? info.name = none) :
    (env.add info).constants.WF ∧ (env.add info).find? info.name = some info ∧
      (∀ name old, env.find? name = some old → (env.add info).find? name = some old) :=
  Lean4Lean.AddInductive.addFresh env info hwf hfresh

end AddInductive

inductive FreshRegistrationTrace (allowed : ConstantInfo → Prop) : Environment → Environment → Prop
  | refl (env) : FreshRegistrationTrace allowed env env
  | step {original current} (previous : FreshRegistrationTrace allowed original current)
      (info : ConstantInfo) (record : allowed info) (fresh : current.constants.find? info.name = none) :
      FreshRegistrationTrace allowed original (current.add info)

theorem FreshRegistrationTrace.trans {allowed : ConstantInfo → Prop} {original current result : Environment}
    (first : FreshRegistrationTrace allowed original current)
    (second : FreshRegistrationTrace allowed current result) : FreshRegistrationTrace allowed original result := by
  induction second with
  | refl => exact first
  | step _ info record fresh ih => exact .step ih info record fresh

theorem FreshRegistrationTrace.preserves {allowed : ConstantInfo → Prop} {original result : Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF) :
    result.constants.WF ∧ (∀ name info, original.find? name = some info → result.find? name = some info) := by
  induction trace with
  | refl => exact ⟨hwf, fun _ _ hold => hold⟩
  | step previous info record fresh ih =>
    obtain ⟨hnext, _, hkeep⟩ := AddInductive.restorationAddFresh _ info ih.1 fresh
    exact ⟨hnext, fun name old hold => hkeep name old (ih.2 name old hold)⟩

theorem FreshRegistrationTrace.lookup {allowed : ConstantInfo → Prop} {original result : Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (hlookup : result.find? name = some info) :
    original.find? name = some info ∨ allowed info := by
  induction trace with
  | refl => exact .inl hlookup
  | @step result previous added record fresh ih =>
    have hcurrent := (previous.preserves hwf).1
    have hresult := (AddInductive.restorationAddFresh _ added hcurrent fresh).1
    have hfind : (result.add added).find? name =
        if added.name == name then some added else result.find? name := by
      rw [Kernel.Environment.find?, hresult.find?'_eq_find?, Kernel.Environment.add_constants,
        hcurrent.find?_insert, ← hcurrent.find?'_eq_find?]
      rfl
    rw [hfind] at hlookup
    split at hlookup
    · exact .inr (Option.some.inj hlookup ▸ record)
    · exact ih hlookup

theorem FreshRegistrationTrace.newLookup {allowed : ConstantInfo → Prop} {original result : Environment}
    (trace : FreshRegistrationTrace allowed original result) (hwf : original.constants.WF)
    (name : Name) (info : ConstantInfo) (habsent : original.find? name = none)
    (hlookup : result.find? name = some info) : allowed info := by
  rcases trace.lookup hwf name info hlookup with hold | hrecord
  · simp only [habsent] at hold
    cases hold
  · exact hrecord

def restoredRecursorRule (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (recNameMap : NameMap Name) (recName : Name) (rule : RecursorRule) : RecursorRule :=
  let newRecName := recNameMap.getD recName recName
  { rule with
    ctor := if newRecName == recName then rule.ctor else preprocessing.restoreCtorName staged rule.ctor
    rhs := preprocessing.restoreNested staged rule.rhs recNameMap }

def restoredRecursorVal (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (recName : Name) (info : RecursorVal) : RecursorVal :=
  { info with
    name := recNameMap.getD recName recName
    type := preprocessing.restoreNested staged info.type recNameMap
    all := allIndNames
    rules := info.rules.map (restoredRecursorRule preprocessing staged recNameMap recName) }

inductive RestoredInductiveRecord (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) : ConstantInfo → Prop
  | header (name : Name) (info : InductiveVal) (lookup : staged.find? name = some (.inductInfo info)) :
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap (.inductInfo { info with all := allIndNames })
  | constructor (name : Name) (info : ConstructorVal) (lookup : staged.find? name = some (.ctorInfo info)) :
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap
        (.ctorInfo { info with type := preprocessing.restoreNested staged info.type })
  | recursor (name : Name) (info : RecursorVal) (lookup : staged.find? name = some (.recInfo info)) :
      RestoredInductiveRecord preprocessing staged allIndNames recNameMap
        (.recInfo (restoredRecursorVal preprocessing staged allIndNames recNameMap name info))

abbrev InductiveRestorationM := StateT Environment (Except Exception)

private def registerRestored (info : ConstantInfo) (allowPrimitive : Bool) : InductiveRestorationM PUnit := do
  (← get).checkName info.name allowPrimitive
  modify (·.add info)

private theorem restorationBind {action : InductiveRestorationM α} {next : α → InductiveRestorationM β}
    {allowed : ConstantInfo → Prop} {env : Environment}
    (haction : (action env).WF fun result => FreshRegistrationTrace allowed env result.2)
    (hnext : ∀ value current, (next value current).WF fun result => FreshRegistrationTrace allowed current result.2) :
    ((action >>= next) env).WF fun result => FreshRegistrationTrace allowed env result.2 :=
  haction.bind fun result htrace => (hnext result.1 result.2).mono fun _ hnext => htrace.trans hnext

private theorem restorationExceptBind {action : Except Exception α} {next : α → InductiveRestorationM β}
    {env : Environment} {invariant : α → Prop} {post : β × Environment → Prop}
    (haction : action.WF invariant)
    (hnext : ∀ value, invariant value → (next value env).WF post) :
    ((liftM action >>= next) env).WF post := by
  change ((action >>= fun value => pure (value, env)) >>= fun result => next result.1 result.2).WF post
  simpa only [bind_assoc, pure_bind] using haction.bind hnext

private theorem registerRestored.trace (info : ConstantInfo) (allowPrimitive : Bool) (env : Environment)
    (allowed : ConstantInfo → Prop) (hrecord : allowed info) :
    (registerRestored info allowPrimitive env).WF fun result => FreshRegistrationTrace allowed env result.2 := by
  unfold registerRestored
  change ((liftM (env.checkName info.name allowPrimitive) >>= fun _ =>
    modify (fun current : Environment => current.add info) : InductiveRestorationM PUnit) env).WF _
  refine restorationExceptBind (checkName.WF env info.name allowPrimitive) ?_
  rintro _ ⟨hfresh, _⟩
  exact .pure (.step (.refl env) info hrecord hfresh)

private theorem restorationForIn (items : List α) (step : α → InductiveRestorationM (ForInStep PUnit))
    (allowed : ConstantInfo → Prop) (env : Environment)
    (hstep : ∀ item current, (step item current).WF fun result => FreshRegistrationTrace allowed current result.2) :
    (forIn (m := InductiveRestorationM) items PUnit.unit (fun item _ => step item) env).WF
      fun result => FreshRegistrationTrace allowed env result.2 := by
  induction items generalizing env with
  | nil => exact .pure (.refl env)
  | cons item items ih =>
    rw [List.forIn_cons]
    refine (hstep item env).bind ?_
    rintro ⟨value, current⟩ htrace
    cases value with
    | done value => exact .pure htrace
    | yield value =>
      cases value
      exact (ih current).mono fun _ hrest => htrace.trans hrest

private theorem restorationForM (items : List α) (step : α → InductiveRestorationM PUnit)
    (allowed : ConstantInfo → Prop) (env : Environment)
    (hstep : ∀ item current, (step item current).WF fun result => FreshRegistrationTrace allowed current result.2) :
    (items.forM step env).WF fun result => FreshRegistrationTrace allowed env result.2 := by
  simp only [List.forM_eq_forM]
  induction items generalizing env with
  | nil => exact .pure (.refl env)
  | cons item items ih =>
    rw [List.forM_cons]
    exact restorationBind (hstep item env) fun _ current => ih current

def restoreInductiveRecursor (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (recName : Name) : InductiveRestorationM PUnit := do
  let newRecName := recNameMap.getD recName recName
  let some (.recInfo recInfo) := staged.find? recName | unreachable!
  let newRecType := preprocessing.restoreNested staged recInfo.type recNameMap
  let newRules ← recInfo.rules.mapM fun rule => do
    let newRhs := preprocessing.restoreNested staged rule.rhs recNameMap
    let newCtorName := if newRecName == recName then rule.ctor else preprocessing.restoreCtorName staged rule.ctor
    return { rule with ctor := newCtorName, rhs := newRhs }
  registerRestored (.recInfo { recInfo with
    name := newRecName, type := newRecType, all := allIndNames, rules := newRules }) allowPrimitive

theorem restoreInductiveRecursor.trace (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (recName : Name) (env : Environment) :
    (restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive recName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 := by
  cases hlookup : staged.find? recName with
  | none =>
    simp only [restoreInductiveRecursor, hlookup, panicWithPosWithDecl, panic, panicCore]
    exact .pure (.refl env)
  | some info =>
    cases info <;> simp only [restoreInductiveRecursor, hlookup, panicWithPosWithDecl, panic, panicCore,
      List.mapM_pure, pure_bind] <;> try exact .pure (.refl env)
    exact registerRestored.trace _ _ env _ (RestoredInductiveRecord.recursor recName _ hlookup)

def restoreInductiveConstructor (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allowPrimitive : Bool) (ctorName : Name) : InductiveRestorationM (ForInStep PUnit) := do
  let some (.ctorInfo ctor) := staged.find? ctorName | do
    (unreachable! : InductiveRestorationM PUnit)
    return .yield PUnit.unit
  let newType := preprocessing.restoreNested staged ctor.type
  registerRestored (.ctorInfo { ctor with type := newType }) allowPrimitive
  return .yield PUnit.unit

theorem restoreInductiveConstructor.trace (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (ctorName : Name) (env : Environment) :
    (restoreInductiveConstructor preprocessing staged allowPrimitive ctorName env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 := by
  cases hlookup : staged.find? ctorName with
  | none =>
    simp only [restoreInductiveConstructor, hlookup, panicWithPosWithDecl, panic, panicCore]
    exact .pure (.refl env)
  | some info =>
    cases info <;> simp only [restoreInductiveConstructor, hlookup, panicWithPosWithDecl, panic, panicCore] <;>
      try exact .pure (.refl env)
    refine restorationBind (registerRestored.trace _ _ env _
      (RestoredInductiveRecord.constructor ctorName _ hlookup)) ?_
    intro _ current
    exact .pure (.refl current)

def restoreInductiveDatatype (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) : InductiveRestorationM (ForInStep PUnit) := do
  let some (.inductInfo ind) := staged.find? indType.name | do
    (unreachable! : InductiveRestorationM PUnit)
    return .yield PUnit.unit
  registerRestored (.inductInfo { ind with all := allIndNames }) allowPrimitive
  forIn ind.ctors PUnit.unit fun ctorName _ =>
    restoreInductiveConstructor preprocessing staged allowPrimitive ctorName
  restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive (mkRecName indType.name)
  return .yield PUnit.unit

theorem restoreInductiveDatatype.trace (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name) (allowPrimitive : Bool)
    (indType : InductiveType) (env : Environment) :
    (restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType env).WF
      fun result => FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged allIndNames recNameMap)
        env result.2 := by
  cases hlookup : staged.find? indType.name with
  | none =>
    simp only [restoreInductiveDatatype, hlookup, panicWithPosWithDecl, panic, panicCore]
    exact .pure (.refl env)
  | some info =>
    cases info <;> simp only [restoreInductiveDatatype, hlookup, panicWithPosWithDecl, panic, panicCore] <;>
      try exact .pure (.refl env)
    rename_i ind
    refine restorationBind (registerRestored.trace _ _ env _ (RestoredInductiveRecord.header indType.name ind hlookup)) ?_
    intro _ current
    refine restorationBind (restorationForIn ind.ctors _ _ current fun name next =>
      restoreInductiveConstructor.trace preprocessing staged allIndNames recNameMap allowPrimitive name next) ?_
    intro _ next
    refine restorationBind
      (restoreInductiveRecursor.trace preprocessing staged allIndNames recNameMap allowPrimitive _ next) ?_
    intro _ final
    exact .pure (.refl final)

def restoreInductiveEnvironment (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig) :
    InductiveRestorationM PUnit := do
  let allIndNames := types.map (·.name)
  let (recNames, recNameMap) := mkAuxRecNameMap staged types
  forIn types PUnit.unit fun indType _ =>
    restoreInductiveDatatype preprocessing staged allIndNames recNameMap allowPrimitive indType
  recNames.forM fun name => restoreInductiveRecursor preprocessing staged allIndNames recNameMap allowPrimitive name
  TypeChecker.M.run (← get) (safety := .safe) (lctx := preprocessing.lctx) (lparams := lparams) (fuel := fuel) do
    preprocessing.aux2nested.forM fun _ type => do _ ← TypeChecker.checkType (preprocessing.openAux type)

theorem restoreInductiveEnvironment.trace (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) (lparams : List Name) (allowPrimitive : Bool) (fuel : FuelConfig)
    (env : Environment) :
    (restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF fun result =>
      FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2) env result.2 := by
  unfold restoreInductiveEnvironment
  dsimp only
  refine restorationBind (restorationForIn types _ _ env fun indType current =>
    restoreInductiveDatatype.trace preprocessing staged _ _ allowPrimitive indType current) ?_
  intro _ current
  refine restorationBind (restorationForM _ _ _ current fun name next =>
    restoreInductiveRecursor.trace preprocessing staged _ _ allowPrimitive name next) ?_
  intro _ next
  change ((TypeChecker.M.run next (safety := .safe) (lctx := preprocessing.lctx)
    (lparams := lparams) (fuel := fuel) do
      preprocessing.aux2nested.forM fun _ type => do _ ← TypeChecker.checkType (preprocessing.openAux type)) >>=
        fun value => pure (value, next)).WF _
  exact Except.WF.bind (fun _ _ => trivial) fun _ _ => .pure (.refl next)

inductive InductiveFrontendBranch (preprocessing : ElimNestedInductive.Result) (staged : Environment)
    (types : List InductiveType) (original : Environment) : Environment → Prop
  | direct (noAux : preprocessing.aux2nested.size = 0) :
      InductiveFrontendBranch preprocessing staged types original staged
  | nested {result} (hasAux : preprocessing.aux2nested.size ≠ 0)
      (trace : FreshRegistrationTrace (RestoredInductiveRecord preprocessing staged (types.map (·.name))
        (mkAuxRecNameMap staged types).2) original result) :
      InductiveFrontendBranch preprocessing staged types original result

structure SafeInductiveFrontendScope (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig) (result : Environment) : Prop where
  originalWF : env.constants.WF
  sources : InductiveSourcesNoMVarNoFVar types
  stages : ∃ preprocessing, inductivePreprocessing env lparams nparams types fuel = .ok preprocessing ∧
    ∃ (staged : Environment) (stats : AddInductive.InductiveStats) (root : AddInductive.Context)
      (constructors : Environment),
      stats.SafeRunScope nparams preprocessing.types.toArray preprocessing.aux2nested.size
        (inductiveScopeContext env lparams allowPrimitive fuel) root constructors staged ∧
      InductiveFrontendBranch preprocessing staged types env result

theorem SafeInductiveFrontendScope.preserves {env result : Environment} {lparams : List Name}
    {nparams : Nat} {types : List InductiveType} {allowPrimitive : Bool} {fuel : FuelConfig}
    (scope : SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result) :
    result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) := by
  obtain ⟨_, _, _, _, _, _, hrun, hbranch⟩ := scope.stages
  cases hbranch with
  | direct => exact ⟨hrun.resultWF, hrun.toSafeRunRegistration.preservesOriginal⟩
  | nested _ htrace => exact htrace.preserves scope.originalWF

theorem Environment.addInductive.safeFrontend (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result := by
  unfold Environment.addInductive
  refine (Environment.checkInductiveSources.WF env types).bind ?_
  intro _ hsources
  refine Except.WF.bind (Q := fun preprocessing =>
    inductivePreprocessing env lparams nparams types fuel = .ok preprocessing) (fun _ hpre => hpre) ?_
  intro preprocessing hpre
  dsimp only
  refine (AddInductive.run.safeScope nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) rfl hmap .nil
    (ElimNestedInductive.ContextReserved.empty _)).bind ?_
  rintro staged ⟨stats, root, constructors, hrun⟩
  split
  · rename_i hnoaux
    exact .pure ⟨hmap, hsources, preprocessing, hpre, staged, stats, root, constructors, hrun, .direct hnoaux⟩
  · rename_i hnested
    have hrestored : ((·.2) <$> restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF
        (fun result => SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result) :=
      (restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel env).map
      fun _ htrace => ⟨hmap, hsources, preprocessing, hpre, staged, stats, root, constructors, hrun,
        InductiveFrontendBranch.nested hnested htrace⟩
    dsimp only [restoreInductiveEnvironment, restoreInductiveDatatype, restoreInductiveConstructor,
      restoreInductiveRecursor, registerRestored, StateT.run] at hrestored
    simpa only [StateT.run, ConstantInfo.name, ConstantInfo.toConstantVal,
      List.mapM_pure, pure_bind,
      panicWithPosWithDecl, panic, panicCore, bind_assoc, pure_bind, Bool.false_eq_true, if_false] using hrestored

theorem Environment.addInductive.safePreserves (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  (Environment.addInductive.safeFrontend env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ scope => scope.preserves

theorem addDecl.safeInductiveFrontend (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      ∃ allowPrimitive, SafeInductiveFrontendScope env lparams nparams types allowPrimitive fuel result := by
  unfold addDecl
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro allowPrimitive _
  exact (Environment.addInductive.safeFrontend env lparams nparams types allowPrimitive fuel hmap).mono
    fun _ scope => ⟨allowPrimitive, scope⟩

theorem addDecl.safeInductivePreserves (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF fun result =>
      result.constants.WF ∧ (∀ name info, env.find? name = some info → result.find? name = some info) :=
  (addDecl.safeInductiveFrontend env lparams nparams types check fuel hmap).mono
    fun _ ⟨_, scope⟩ => scope.preserves

end Lean4Lean
