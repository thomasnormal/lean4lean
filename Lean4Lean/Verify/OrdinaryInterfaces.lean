import Lean4Lean.Verify.PrimitiveInterfaces

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private primitive_contains from Lean4Lean.Verify.Environment

structure NativePrimitiveFrame (before after : Kernel.Environment) : Prop where
  map_wf : after.constants.WF
  constants : ∀ {name}, Kernel.Environment.primitives.contains name →
    after.constants.find? name = before.constants.find? name

theorem NativePrimitiveFrame.refl {env : Kernel.Environment} (hmap : env.constants.WF) :
    NativePrimitiveFrame env env :=
  ⟨hmap, fun {_} _ => rfl⟩

theorem NativePrimitiveFrame.trans {before middle after : Kernel.Environment}
    (first : NativePrimitiveFrame before middle) (second : NativePrimitiveFrame middle after) :
    NativePrimitiveFrame before after :=
  ⟨second.map_wf, fun {_} hprim => (second.constants hprim).trans (first.constants hprim)⟩

theorem NativePrimitiveFrame.find? {before after : Kernel.Environment} {name : Name}
    (hframe : NativePrimitiveFrame before after) (hmap : before.constants.WF)
    (hprim : Kernel.Environment.primitives.contains name) : after.find? name = before.find? name := by
  simpa only [Kernel.Environment.find?, hframe.map_wf.find?'_eq_find?, hmap.find?'_eq_find?]
    using hframe.constants hprim

theorem NativePrimitiveFrame.addConst {env : Kernel.Environment} {ci : ConstantInfo}
    (hmap : env.constants.WF) (hfresh : env.constants.find? ci.name = none)
    (hprim : Kernel.Environment.primitives.contains ci.name = false) :
    NativePrimitiveFrame env (env.add ci) := by
  refine ⟨hmap.insert _ _ hfresh, ?_⟩
  intro name hname
  change (env.constants.insert ci.name ci).find? name = env.constants.find? name
  rw [hmap.find?_insert]
  split
  · rename_i heq
    have heq : ci.name = name := beq_iff_eq.mp heq
    rw [heq] at hprim
    rw [hprim] at hname
    contradiction
  · rfl

theorem addDefinition.nativePrimitiveFrame (env : Kernel.Environment) (v : DefinitionVal)
    (fuel : FuelConfig) (hmap : env.constants.WF) (hunsafe : v.safety ≠ .unsafe)
    (hfresh : env.find? v.name = none)
    (hprimitive : Kernel.Environment.primitives.contains v.name = false)
    {env' : Kernel.Environment}
    (hresult : addDefinition env v true fuel = .ok env') :
    NativePrimitiveFrame env env' := by
  unfold addDefinition at hresult
  simp only [if_true, pure_bind] at hresult
  cases hs : v.safety
  · exact (hunsafe hs).elim
  all_goals
    simp [hprimitive] at hresult
    simp only [Functor.map, Except.map] at hresult
    split at hresult <;> cases hresult
    apply NativePrimitiveFrame.addConst (ci := .defnInfo v) hmap ?_ ?_
    · simpa only [Kernel.Environment.find?, hmap.find?'_eq_find?, ConstantInfo.name] using hfresh
    · simpa only [ConstantInfo.name] using hprimitive

theorem NativePrimitiveFrame.foldlM {Item State Error : Type}
    (getEnv : State → Kernel.Environment) (step : State → Item → Except Error State)
    (items : List Item) (initial : State) (hmap : (getEnv initial).constants.WF)
    (hstep : ∀ item current, (getEnv current).constants.WF →
      (step current item).WF fun next => NativePrimitiveFrame (getEnv current) (getEnv next)) :
    (items.foldlM step initial).WF fun final => NativePrimitiveFrame (getEnv initial) (getEnv final) := by
  induction items generalizing initial with
  | nil => exact .pure (.refl hmap)
  | cons item items ih =>
    rw [List.foldlM_cons]
    exact (hstep item initial hmap).bind fun next hfirst =>
      (ih next hfirst.map_wf).mono fun _ hrest => hfirst.trans hrest

theorem NativePrimitiveSafety.of_frame {before after : Kernel.Environment}
    (hsafe : NativePrimitiveSafety before) (hframe : NativePrimitiveFrame before after) :
    NativePrimitiveSafety after :=
  ⟨hframe.map_wf, fun {_ _} hfind hprim => hsafe.safe (hframe.constants hprim ▸ hfind) hprim⟩

theorem Aligned.constants_eq_of_lookup {before after : ConstMap} {env env' : VEnv}
    (hbefore : Aligned safety before env) (hafter : Aligned safety after env')
    (hle : env ≤ env') (hlookup : after.find? name = before.find? name) :
    env'.constants name = env.constants name := by
  cases hconstant : env.constants name with
  | some constant => exact hle.constants hconstant
  | none =>
    cases hfinal : env'.constants name with
    | none => rfl
    | some constant =>
      obtain ⟨info, hfind, hsafety⟩ := hafter.find?_iff.mpr ⟨constant, hfinal⟩
      obtain ⟨original, horiginal⟩ := hbefore.find?_iff.mp ⟨info, hlookup ▸ hfind, hsafety⟩
      rw [hconstant] at horiginal
      contradiction

theorem VEnv.HasPrimitives.mono_of_primitiveConstants {env env' : VEnv}
    (hp : env.HasPrimitives) (hle : env ≤ env')
    (hconst : ∀ name, Kernel.Environment.primitives.contains name →
      env'.constants name = env.constants name) : env'.HasPrimitives := by
  have hliterals : env'.HasPrimitiveLiterals := {
    bool := fun present => by
      obtain ⟨⟨falseInfo, hfalse⟩, ⟨trueInfo, htrue⟩⟩ := hp.bool
        (by simpa only [VEnv.contains, hconst ``Bool (primitive_contains _ (by simp))] using present)
      exact ⟨⟨falseInfo, hle.constants hfalse⟩, ⟨trueInfo, hle.constants htrue⟩⟩
    boolFalse := fun lookup => hp.boolFalse (hconst ``Bool.false (primitive_contains _ (by simp)) ▸ lookup)
    boolTrue := fun lookup => hp.boolTrue (hconst ``Bool.true (primitive_contains _ (by simp)) ▸ lookup)
    nat := fun present => by
      obtain ⟨⟨zeroInfo, hzero⟩, ⟨succInfo, hsucc⟩⟩ := hp.nat
        (by simpa only [VEnv.contains, hconst ``Nat (primitive_contains _ (by simp))] using present)
      exact ⟨⟨zeroInfo, hle.constants hzero⟩, ⟨succInfo, hle.constants hsucc⟩⟩
    natZero := fun lookup => hp.natZero (hconst ``Nat.zero (primitive_contains _ (by simp)) ▸ lookup)
    natSucc := fun lookup => hp.natSucc (hconst ``Nat.succ (primitive_contains _ (by simp)) ▸ lookup) }
  apply hp.mono_of_literals hle hliterals
  intro name hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact hconst _ (primitive_contains _ (by simp))

theorem CheckerEnv.hasPrimitives_of_frame {before after : Kernel.Environment} {env env' : VEnv}
    (hbefore : CheckerEnv safety before env) (hafter : CheckerEnv safety after env')
    (hle : env ≤ env') (hp : env.HasPrimitives) (hframe : NativePrimitiveFrame before after) :
    env'.HasPrimitives :=
  hp.mono_of_primitiveConstants hle fun _ hprim =>
    hbefore.aligned.constants_eq_of_lookup hafter.aligned hle (hframe.constants hprim)

theorem addDefinition.refinesPrimitiveFrame {env : Kernel.Environment} {ves : VEnvs}
    (wf : ves.WF env) (v : DefinitionVal) (hunsafe : v.safety ≠ .unsafe)
    (hfresh : env.find? v.name = none)
    (hprimitive : Kernel.Environment.primitives.contains v.name = false)
    (fuel : FuelConfig := {}) :
    (addDefinition env v true fuel).WF fun env' =>
      ∃ ves', VEnvs.WF env' ves' ∧ NativePrimitiveFrame env env' ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety ∧
          CheckerEnv safety env' (ves'.venv safety) ∧
          (ves'.venv safety).HasPrimitives := by
  intro env' hresult
  obtain ⟨ves', hwf, hle⟩ := addDefinition.WF wf v fuel env' hresult
  have hframe := addDefinition.nativePrimitiveFrame env v fuel
    (wf.tr (safety := .safe)).map_wf hunsafe
    hfresh hprimitive hresult
  refine ⟨ves', hwf, hframe, ?_⟩
  intro safety
  have hbefore := (wf.tr (safety := safety)).checkerEnv
  have hafter := (hwf.tr (safety := safety)).checkerEnv
  exact ⟨hle safety, hafter,
    hbefore.hasPrimitives_of_frame hafter (hle safety)
      (wf.hasPrimitives (safety := safety)) hframe⟩

theorem AddInductive.declareInductiveTypes.preservesPrimitives
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (hmap : ctx.env.constants.WF) (hallow : ctx.allowPrimitive = false) :
    (declareInductiveTypes stats numParams types numNested isUnsafe ctx).WF
      (NativePrimitiveFrame ctx.env) := by
  unfold declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  apply NativePrimitiveFrame.foldlM id _ _ _ hmap
  intro info env hmap
  exact (checkName.WF env info.name ctx.allowPrimitive).bind fun _ ⟨hfresh, hprim⟩ =>
    .pure (NativePrimitiveFrame.addConst (ci := .inductInfo info) hmap hfresh (hprim hallow))

theorem AddInductive.declareConstructors.preservesPrimitives
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (types : Array InductiveType) (isUnsafe : Bool)
    (hmap : ctx.env.constants.WF) (hallow : ctx.allowPrimitive = false) :
    (declareConstructors stats types isUnsafe ctx).WF (NativePrimitiveFrame ctx.env) := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  apply NativePrimitiveFrame.foldlM id _ _ _ hmap
  intro type env hmap
  refine Except.WF.bind ?_ (fun state hframe => .pure hframe)
  apply NativePrimitiveFrame.foldlM Prod.snd _ _ _ hmap
  intro ctor state hmap
  refine (checkName.WF state.2 ctor.name ctx.allowPrimitive).bind fun _ ⟨hfresh, hprim⟩ => ?_
  exact .pure (NativePrimitiveFrame.addConst hmap hfresh (hprim hallow))

theorem AddInductive.checkInductiveTypes.preservesHeaderConstructorPrimitives
    (ctx : AddInductive.Context) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (hmap : ctx.env.constants.WF)
    (hallow : ctx.allowPrimitive = false) :
    (checkInductiveTypes numParams types (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types numNested isUnsafe) do
        checkConstructors types stats isUnsafe
        declareConstructors stats types isUnsafe) ctx).WF (NativePrimitiveFrame ctx.env) := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current _ hframe
  have hallow' : current.allowPrimitive = false := hframe.allowPrimitive.trans hallow
  refine (declareInductiveTypes.preservesPrimitives current stats numParams types numNested isUnsafe
    (by simpa only [hframe.env] using hmap) hallow').bind ?_
  intro nativeHeaders headerFrame
  refine (show (checkConstructors types stats isUnsafe
    { current with env := nativeHeaders }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
  intro _ _
  refine (declareConstructors.preservesPrimitives { current with env := nativeHeaders }
    stats types isUnsafe headerFrame.map_wf hallow').mono ?_
  intro nativeCtors constructorFrame
  simpa only [hframe.env] using headerFrame.trans constructorFrame

theorem AddInductive.declareInductiveTypes.refinesOrdinaryInterfaces
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (hchecker : CheckerEnv safety ctx.env venv) (hp : venv.HasPrimitives)
    (hsafe : NativePrimitiveSafety ctx.env) (hallow : ctx.allowPrimitive = false)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hsize : stats.nindices.size = types.size)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) types.toList headers)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF venv) :
    (declareInductiveTypes stats numParams types numNested isUnsafe ctx).WF fun result =>
      ∃ final, venv.addInductHeaders headers = some final ∧ CheckerEnv safety result final ∧
        final.HasPrimitives ∧ NativePrimitiveSafety result ∧ NativePrimitiveFrame ctx.env result := by
  intro result accepted
  obtain ⟨final, hadd, hfinal⟩ := declareInductiveTypes.refinesChecker
    ctx stats numParams types numNested isUnsafe hchecker hsafety hsize hheaders htypes result accepted
  have hframe := declareInductiveTypes.preservesPrimitives ctx stats numParams types numNested isUnsafe
    hchecker.map_wf hallow result accepted
  exact ⟨final, hadd, hfinal,
    hchecker.hasPrimitives_of_frame hfinal (VEnv.addInductHeaders.le hadd) hp hframe,
    hsafe.of_frame hframe, hframe⟩

theorem AddInductive.declareConstructors.refinesOrdinaryInterfaces
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (types : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (hchecker : CheckerEnv safety ctx.env venv) (hp : venv.HasPrimitives)
    (hsafe : NativePrimitiveSafety ctx.env) (hallow : ctx.allowPrimitive = false)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors) types.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats types isUnsafe ctx).WF fun result =>
      ∃ final, venv.addConstructorHeaders (vtypes.flatMap (fun type : VInductiveType => type.ctors)) =
        some final ∧ CheckerEnv safety result final ∧ final.HasPrimitives ∧
        NativePrimitiveSafety result ∧ NativePrimitiveFrame ctx.env result := by
  intro result accepted
  obtain ⟨final, hadd, hfinal⟩ := declareConstructors.refinesChecker
    ctx stats types isUnsafe hchecker hsafety hctors htypes result accepted
  have hframe := declareConstructors.preservesPrimitives ctx stats types isUnsafe
    hchecker.map_wf hallow result accepted
  exact ⟨final, hadd, hfinal,
    hchecker.hasPrimitives_of_frame hfinal (VEnv.addConstructorHeaders.le hadd) hp hframe,
    hsafe.of_frame hframe, hframe⟩

theorem AddInductive.checkInductiveTypes.refinesOrdinaryInterfaces
    (ctx : AddInductive.Context) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers vtypes : List VInductiveType}
    (hchecker : CheckerEnv safety ctx.env venv) (hp : venv.HasPrimitives)
    (hsafe : NativePrimitiveSafety ctx.env) (hallow : ctx.allowPrimitive = false)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) types.toList headers)
    (headerTypes : ∀ header ∈ headers, header.toVConstant.WF venv)
    (hctors : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
        List.Forall₂ (TrConstructor headerEnv ctx.lparams) type.ctors vtype.ctors) types.toList vtypes)
    (constructorTypes : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
        ctor.toVConstant.WF headerEnv) :
    (checkInductiveTypes numParams types (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types numNested isUnsafe) do
        checkConstructors types stats isUnsafe
        declareConstructors stats types isUnsafe) ctx).WF fun result =>
      ∃ headerEnv final, venv.addInductHeaders headers = some headerEnv ∧
        headerEnv.addConstructorHeaders (vtypes.flatMap (fun type : VInductiveType => type.ctors)) =
          some final ∧ CheckerEnv safety result final ∧ final.HasPrimitives ∧
        NativePrimitiveSafety result ∧ NativePrimitiveFrame ctx.env result := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current hsizes hframe
  have hallow' : current.allowPrimitive = false := hframe.allowPrimitive.trans hallow
  refine (declareInductiveTypes.refinesOrdinaryInterfaces current stats numParams types numNested isUnsafe
    (by simpa only [hframe.env] using hchecker) hp (by simpa only [hframe.env] using hsafe) hallow'
    hsafety hsizes.1 (by simpa only [hframe.lparams] using hheaders) headerTypes).bind ?_
  rintro nativeHeaders ⟨headerEnv, haddHeaders, headerChecker, headerPrimitives, headerSafe, headerFrame⟩
  refine (show (checkConstructors types stats isUnsafe
    { current with env := nativeHeaders }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
  intro _ _
  refine (declareConstructors.refinesOrdinaryInterfaces { current with env := nativeHeaders }
    stats types isUnsafe headerChecker headerPrimitives headerSafe hallow' hsafety
    (by simpa only [hframe.lparams] using hctors headerEnv haddHeaders)
    (constructorTypes headerEnv haddHeaders)).mono ?_
  rintro nativeCtors ⟨final, haddCtors, finalChecker, finalPrimitives, finalSafe, constructorFrame⟩
  exact ⟨headerEnv, final, haddHeaders, haddCtors, finalChecker, finalPrimitives, finalSafe,
    by simpa only [hframe.env] using headerFrame.trans constructorFrame⟩

end Lean4Lean
