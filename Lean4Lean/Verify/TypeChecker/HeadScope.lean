import Lean4Lean.Verify.TypeChecker.ComparisonHeadFrame
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.NameGenerator

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

def NativeHeadScoped (locals : LocalContext) (expression : Expr) : Prop :=
  NativeHeadClean expression ∧ ∀ identifier, expression = .fvar identifier →
    TypeChecker.Inner.isLetFVar locals identifier = false

def TypeChecker.HeadScopeCacheWF (locals : LocalContext) (state : TypeChecker.State) : Prop :=
  (∀ key value : Expr, state.whnfCoreCache[key]? = some value → NativeHeadScoped locals value) ∧
  (∀ key value : Expr, state.whnfCache[key]? = some value → NativeHeadScoped locals value)

def TypeChecker.HeadCacheNamesWF (state : TypeChecker.State) : Prop :=
  (∀ key value : Expr, state.whnfCoreCache[key]? = some value → value.FVarsIn state.ngen.Reserves) ∧
  (∀ key value : Expr, state.whnfCache[key]? = some value → value.FVarsIn state.ngen.Reserves)

def NativeLocalNamesWF (locals : LocalContext) (generator : NameGenerator) : Prop :=
  ∀ declaration ∈ locals.toList, generator.Reserves declaration.fvarId

theorem NativeLocalNamesWF.empty (generator : NameGenerator) : NativeLocalNamesWF {} generator := by
  intro declaration member
  simp [LocalContext.toList, PersistentArray.toList', PersistentArrayNode.toList'] at member

theorem NativeLocalNamesWF.mono {locals : LocalContext} {first second : NameGenerator}
    (reserved : NativeLocalNamesWF locals first) (increasing : first ≤ second) :
    NativeLocalNamesWF locals second :=
  fun declaration member => (reserved declaration member).mono increasing

theorem NativeLocalNamesWF.freshAbsent {locals : LocalContext} {generator : NameGenerator}
    (wellFormed : locals.WF) (reserved : NativeLocalNamesWF locals generator) :
    locals.find? ⟨generator.curr⟩ = none := by
  rw [wellFormed.find?_eq_find?_toList]
  apply List.find?_eq_none.mpr
  intro declaration member
  have different : (⟨generator.curr⟩ : FVarId) ≠ declaration.fvarId := by
    intro equality
    exact generator.not_reserves_self (equality ▸ reserved declaration member)
  simpa only [beq_iff_eq] using different

theorem NativeLocalNamesWF.mkLocalDecl {locals : LocalContext} {generator : NameGenerator}
    (reserved : NativeLocalNamesWF locals generator) (name : Name) (domain : Expr) (binder : BinderInfo) :
    NativeLocalNamesWF (locals.mkLocalDecl ⟨generator.curr⟩ name domain binder) generator.next := by
  intro declaration member
  rw [LocalContext.mkLocalDecl_toList] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact generator.next_reserves_self
  · exact (reserved declaration member).mono .next

theorem NativeLocalNamesWF.mkLetDecl {locals : LocalContext} {generator : NameGenerator}
    (reserved : NativeLocalNamesWF locals generator) (name : Name) (type value : Expr) :
    NativeLocalNamesWF (locals.mkLetDecl ⟨generator.curr⟩ name type value) generator.next := by
  intro declaration member
  rw [LocalContext.mkLetDecl_toList] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact generator.next_reserves_self
  · exact (reserved declaration member).mono .next

theorem NativeHeadScoped.lookupCongr {first second : LocalContext} {expression : Expr}
    (stable : NativeHeadScoped first expression)
    (same : ∀ identifier, expression = .fvar identifier → second.find? identifier = first.find? identifier) :
    NativeHeadScoped second expression := by
  refine ⟨stable.1, fun identifier equal => ?_⟩
  unfold TypeChecker.Inner.isLetFVar
  rw [same identifier equal]
  exact stable.2 identifier equal

theorem NativeHeadScoped.mkLocalDecl {locals : LocalContext} {expression : Expr}
    (wellFormed : locals.WF) (stable : NativeHeadScoped locals expression)
    (identifier : FVarId) (fresh : locals.find? identifier = none)
    (name : Name) (domain : Expr) (binder : BinderInfo) :
    NativeHeadScoped (locals.mkLocalDecl identifier name domain binder) expression := by
  refine ⟨stable.1, fun current equal => ?_⟩
  unfold TypeChecker.Inner.isLetFVar
  rw [(wellFormed.mkLocalDecl fresh).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList]
  by_cases same : current = identifier
  · subst current
    simp only [List.find?_cons, LocalDecl.fvarId, BEq.rfl]
  · have original := stable.2 current equal
    unfold TypeChecker.Inner.isLetFVar at original
    rw [wellFormed.find?_eq_find?_toList] at original
    simpa only [List.find?_cons, LocalDecl.fvarId, beq_eq_false_iff_ne.mpr same] using original

theorem NativeHeadScoped.mkLetDecl {locals : LocalContext} {expression : Expr} {generator : NameGenerator}
    (wellFormed : locals.WF) (reserved : NativeLocalNamesWF locals generator)
    (stable : NativeHeadScoped locals expression) (names : expression.FVarsIn generator.Reserves)
    (name : Name) (type value : Expr) :
    NativeHeadScoped (locals.mkLetDecl ⟨generator.curr⟩ name type value) expression := by
  apply stable.lookupCongr
  intro identifier equal
  have different : identifier ≠ ⟨generator.curr⟩ := by
    intro same
    subst identifier
    rw [equal] at names
    exact generator.not_reserves_self names
  rw [(wellFormed.mkLetDecl (reserved.freshAbsent wellFormed)).find?_eq_find?_toList,
    LocalContext.mkLetDecl_toList]
  simp only [List.find?_cons, LocalDecl.fvarId, beq_eq_false_iff_ne.mpr different]
  exact wellFormed.find?_eq_find?_toList.symm

theorem NativeHeadScoped.leaveLocalDecl {locals : LocalContext} {expression : Expr}
    (wellFormed : locals.WF) (identifier : FVarId) (fresh : locals.find? identifier = none)
    (name : Name) (domain : Expr) (binder : BinderInfo)
    (stable : NativeHeadScoped (locals.mkLocalDecl identifier name domain binder) expression) :
    NativeHeadScoped locals expression := by
  refine ⟨stable.1, fun current equal => ?_⟩
  by_cases same : current = identifier
  · subst current
    simp only [TypeChecker.Inner.isLetFVar, fresh]
  · have original := stable.2 current equal
    unfold TypeChecker.Inner.isLetFVar at original ⊢
    rw [(wellFormed.mkLocalDecl fresh).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList] at original
    rw [wellFormed.find?_eq_find?_toList]
    simpa only [List.find?_cons, LocalDecl.fvarId, beq_eq_false_iff_ne.mpr same] using original

theorem NativeHeadScoped.leaveLetDecl {locals : LocalContext} {expression : Expr}
    (wellFormed : locals.WF) (identifier : FVarId) (fresh : locals.find? identifier = none)
    (name : Name) (type value : Expr)
    (stable : NativeHeadScoped (locals.mkLetDecl identifier name type value) expression) :
    NativeHeadScoped locals expression := by
  refine ⟨stable.1, fun current equal => ?_⟩
  by_cases same : current = identifier
  · subst current
    simp only [TypeChecker.Inner.isLetFVar, fresh]
  · have original := stable.2 current equal
    unfold TypeChecker.Inner.isLetFVar at original ⊢
    rw [(wellFormed.mkLetDecl fresh).find?_eq_find?_toList, LocalContext.mkLetDecl_toList] at original
    rw [wellFormed.find?_eq_find?_toList]
    simpa only [List.find?_cons, LocalDecl.fvarId, beq_eq_false_iff_ne.mpr same] using original

theorem TypeChecker.HeadScopeCacheWF.empty (locals : LocalContext) : HeadScopeCacheWF locals {} := by
  constructor <;> intro key value found <;> simp at found

theorem TypeChecker.HeadScopeCacheWF.headCacheWF {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) : HeadCacheWF state :=
  ⟨fun key value found => (stable.1 key value found).1,
    fun key value found => (stable.2 key value found).1⟩

theorem TypeChecker.HeadScopeCacheWF.insertCore {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) (key value : Expr) (head : NativeHeadScoped locals value) :
    HeadScopeCacheWF locals { state with whnfCoreCache := state.whnfCoreCache.insert key value } := by
  refine ⟨?_, stable.2⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact head
  · exact stable.1 query result found

theorem TypeChecker.HeadScopeCacheWF.insertFull {locals : LocalContext} {state : TypeChecker.State}
    (stable : HeadScopeCacheWF locals state) (key value : Expr) (head : NativeHeadScoped locals value) :
    HeadScopeCacheWF locals { state with whnfCache := state.whnfCache.insert key value } := by
  refine ⟨stable.1, ?_⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact head
  · exact stable.2 query result found

theorem TypeChecker.HeadCacheNamesWF.empty : HeadCacheNamesWF {} := by
  constructor <;> intro key value found <;> simp at found

theorem TypeChecker.HeadCacheNamesWF.insertCore {state : TypeChecker.State}
    (reserved : HeadCacheNamesWF state) (key value : Expr) (names : value.FVarsIn state.ngen.Reserves) :
    HeadCacheNamesWF { state with whnfCoreCache := state.whnfCoreCache.insert key value } := by
  refine ⟨?_, reserved.2⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact names
  · exact reserved.1 query result found

theorem TypeChecker.HeadCacheNamesWF.insertFull {state : TypeChecker.State}
    (reserved : HeadCacheNamesWF state) (key value : Expr) (names : value.FVarsIn state.ngen.Reserves) :
    HeadCacheNamesWF { state with whnfCache := state.whnfCache.insert key value } := by
  refine ⟨reserved.1, ?_⟩
  intro query result found
  rw [Std.HashMap.getElem?_insert] at found
  split at found
  · cases found
    exact names
  · exact reserved.2 query result found

theorem TypeChecker.HeadCacheNamesWF.next {state : TypeChecker.State} (names : HeadCacheNamesWF state) :
    HeadCacheNamesWF { state with ngen := state.ngen.next } := by
  constructor
  · intro key value found
    exact (names.1 key value found).mono fun _ reserved => reserved.mono .next
  · intro key value found
    exact (names.2 key value found).mono fun _ reserved => reserved.mono .next

theorem TypeChecker.HeadScopeCacheWF.mkLocalDecl {locals : LocalContext} {state : TypeChecker.State}
    (wellFormed : locals.WF) (reserved : NativeLocalNamesWF locals state.ngen)
    (stable : HeadScopeCacheWF locals state) (name : Name) (domain : Expr) (binder : BinderInfo) :
    HeadScopeCacheWF (locals.mkLocalDecl ⟨state.ngen.curr⟩ name domain binder)
      { state with ngen := state.ngen.next } := by
  constructor
  · intro key value found
    exact (stable.1 key value found).mkLocalDecl wellFormed _ (reserved.freshAbsent wellFormed) name domain binder
  · intro key value found
    exact (stable.2 key value found).mkLocalDecl wellFormed _ (reserved.freshAbsent wellFormed) name domain binder

theorem TypeChecker.HeadScopeCacheWF.mkLetDecl {locals : LocalContext} {state : TypeChecker.State}
    (wellFormed : locals.WF) (reserved : NativeLocalNamesWF locals state.ngen)
    (stable : HeadScopeCacheWF locals state) (names : HeadCacheNamesWF state)
    (name : Name) (type value : Expr) :
    HeadScopeCacheWF (locals.mkLetDecl ⟨state.ngen.curr⟩ name type value)
      { state with ngen := state.ngen.next } := by
  constructor
  · intro key cached found
    exact (stable.1 key cached found).mkLetDecl wellFormed reserved (names.1 key cached found) name type value
  · intro key cached found
    exact (stable.2 key cached found).mkLetDecl wellFormed reserved (names.2 key cached found) name type value

theorem TypeChecker.HeadScopeCacheWF.leaveLocalDecl {locals : LocalContext} {state : TypeChecker.State}
    (wellFormed : locals.WF) (identifier : FVarId) (fresh : locals.find? identifier = none)
    (name : Name) (domain : Expr) (binder : BinderInfo)
    (stable : HeadScopeCacheWF (locals.mkLocalDecl identifier name domain binder) state) :
    HeadScopeCacheWF locals state :=
  ⟨fun key value found => (stable.1 key value found).leaveLocalDecl wellFormed identifier fresh name domain binder,
    fun key value found => (stable.2 key value found).leaveLocalDecl wellFormed identifier fresh name domain binder⟩

theorem TypeChecker.HeadScopeCacheWF.leaveLetDecl {locals : LocalContext} {state : TypeChecker.State}
    (wellFormed : locals.WF) (identifier : FVarId) (fresh : locals.find? identifier = none)
    (name : Name) (type value : Expr)
    (stable : HeadScopeCacheWF (locals.mkLetDecl identifier name type value) state) :
    HeadScopeCacheWF locals state :=
  ⟨fun key cached found => (stable.1 key cached found).leaveLetDecl wellFormed identifier fresh name type value,
    fun key cached found => (stable.2 key cached found).leaveLetDecl wellFormed identifier fresh name type value⟩

def TypeChecker.M.HeadScopeWF (action : TypeChecker.M Result) : Prop :=
  ∀ context state, context.lctx.WF → NativeLocalNamesWF context.lctx state.ngen →
    HeadScopeCacheWF context.lctx state → HeadCacheNamesWF state →
    ∀ result finalState, action context state = .ok (result, finalState) →
      state.ngen ≤ finalState.ngen ∧ HeadScopeCacheWF context.lctx finalState ∧ HeadCacheNamesWF finalState

theorem TypeChecker.M.HeadScopeWF.pure (result : Result) :
    (pure result : TypeChecker.M Result).HeadScopeWF := by
  intro context state wellFormed reserved stable names actual finalState accepted
  cases accepted
  exact ⟨.rfl, stable, names⟩

theorem TypeChecker.M.HeadScopeWF.throw (error : Exception) :
    (throw error : TypeChecker.M Result).HeadScopeWF := by
  intro context state wellFormed reserved stable names actual finalState accepted
  cases accepted

theorem TypeChecker.M.HeadScopeWF.bind {action : TypeChecker.M First}
    {continuation : First → TypeChecker.M Result}
    (valid : action.HeadScopeWF) (next : ∀ first, (continuation first).HeadScopeWF) :
    (action >>= continuation).HeadScopeWF := by
  intro context state wellFormed reserved stable names result finalState accepted
  cases run : action context state with
  | error error => simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, run] at accepted
  | ok intermediate =>
    rcases intermediate with ⟨first, middleState⟩
    simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind, run] at accepted
    have initial := valid context state wellFormed reserved stable names first middleState run
    have final := next first context middleState wellFormed (reserved.mono initial.1)
      initial.2.1 initial.2.2 result finalState accepted
    exact ⟨initial.1.trans final.1, final.2⟩

theorem TypeChecker.M.HeadScopeWF.withFreshId {continuation : Name → TypeChecker.M Result}
    (valid : ∀ name, (continuation name).HeadScopeWF) :
    (withFreshId continuation).HeadScopeWF := by
  intro context state wellFormed reserved stable names result finalState accepted
  have final := valid state.ngen.curr context { state with ngen := state.ngen.next }
    wellFormed (reserved.mono .next) stable names.next result finalState accepted
  exact ⟨NameGenerator.LE.next.trans final.1, final.2⟩

theorem withLocalDecl.headScopeWF (name : Name) (binder : BinderInfo) (domain : Expr)
    (continuation : Expr → TypeChecker.RecM Result) (methods : TypeChecker.Methods)
    (valid : ∀ expression, (continuation expression methods).HeadScopeWF) :
    (withLocalDecl name binder domain continuation methods).HeadScopeWF := by
  intro context state wellFormed reserved stable names result finalState accepted
  have fresh := reserved.freshAbsent wellFormed
  have final := valid (.fvar ⟨state.ngen.curr⟩)
    { context with lctx := context.lctx.mkLocalDecl ⟨state.ngen.curr⟩ name domain binder }
    { state with ngen := state.ngen.next } (wellFormed.mkLocalDecl fresh)
    (reserved.mkLocalDecl name domain binder) (stable.mkLocalDecl wellFormed reserved name domain binder)
    names.next result finalState accepted
  exact ⟨NameGenerator.LE.next.trans final.1,
    final.2.1.leaveLocalDecl wellFormed _ fresh name domain binder, final.2.2⟩

theorem withLetDecl.headScopeWF (name : Name) (type value : Expr)
    (continuation : Expr → TypeChecker.RecM Result) (methods : TypeChecker.Methods)
    (valid : ∀ expression, (continuation expression methods).HeadScopeWF) :
    (withLetDecl name type value continuation methods).HeadScopeWF := by
  intro context state wellFormed reserved stable names result finalState accepted
  have fresh := reserved.freshAbsent wellFormed
  have final := valid (.fvar ⟨state.ngen.curr⟩)
    { context with lctx := context.lctx.mkLetDecl ⟨state.ngen.curr⟩ name type value }
    { state with ngen := state.ngen.next } (wellFormed.mkLetDecl fresh)
    (reserved.mkLetDecl name type value) (stable.mkLetDecl wellFormed reserved names name type value)
    names.next result finalState accepted
  exact ⟨NameGenerator.LE.next.trans final.1,
    final.2.1.leaveLetDecl wellFormed _ fresh name type value, final.2.2⟩

end Lean4Lean
