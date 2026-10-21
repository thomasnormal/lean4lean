import Lean4Lean.Verify.ConstructorHeaders

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment

section Semantic
variable {env env' headerEnv ctorEnv : VEnv} {headers : List VInductiveType}
  {ctors : List VConstVal} {name : Name}

structure VEnv.HasPrimitiveLiterals (env : VEnv) : Prop where
  bool : env.contains ``Bool → env.contains ``Bool.false ∧ env.contains ``Bool.true
  boolFalse : env.constants ``Bool.false = some ci → ci = { uvars := 0, type := .bool }
  boolTrue : env.constants ``Bool.true = some ci → ci = { uvars := 0, type := .bool }
  nat : env.contains ``Nat → env.contains ``Nat.zero ∧ env.contains ``Nat.succ
  natZero : env.constants ``Nat.zero = some ci → ci = { uvars := 0, type := .nat }
  natSucc : env.constants ``Nat.succ = some ci →
    ci = { uvars := 0, type := .forallE .nat .nat }

theorem VEnv.HasPrimitives.literals (hp : env.HasPrimitives) : env.HasPrimitiveLiterals :=
  ⟨hp.bool, hp.boolFalse, hp.boolTrue, hp.nat, hp.natZero, hp.natSucc⟩

theorem VEnv.addInductHeaders.constants_eq
    (hadd : env.addInductHeaders headers = some env')
    (hn : ∀ header ∈ headers, header.name ≠ name) : env'.constants name = env.constants name := by
  induction headers generalizing env with
  | nil => cases hadd; rfl
  | cons header headers ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (ih hrest (fun remaining hmem => hn remaining (by simp [hmem]))).trans
      (by rw [VEnv.addConst_constants_eq hstep]; simp [hn header (by simp)])

theorem VEnv.addConstructorHeaders.constants_eq
    (hadd : env.addConstructorHeaders ctors = some env')
    (hn : ∀ ctor ∈ ctors, ctor.name ≠ name) : env'.constants name = env.constants name := by
  induction ctors generalizing env with
  | nil => cases hadd; rfl
  | cons ctor ctors ih =>
    obtain ⟨next, hstep, hrest⟩ := Option.bind_eq_some_iff.mp hadd
    exact (ih hrest (fun remaining hmem => hn remaining (by simp [hmem]))).trans
      (by rw [VEnv.addConst_constants_eq hstep]; simp [hn ctor (by simp)])

def VInductDecl.stagedNames (decl : VInductDecl) : List Name :=
  decl.types.map (·.name) ++ (decl.types.flatMap (·.ctors)).map (·.name)

theorem VInductDecl.stagedConstants_eq (decl : VInductDecl)
    (hheaders : env.addInductHeaders decl.types = some headerEnv)
    (hctors : headerEnv.addConstructorHeaders (decl.types.flatMap (·.ctors)) = some ctorEnv)
    (hn : name ∉ decl.stagedNames) : ctorEnv.constants name = env.constants name := by
  refine (VEnv.addConstructorHeaders.constants_eq hctors ?_).trans
    (VEnv.addInductHeaders.constants_eq hheaders ?_)
  · intro ctor hmem hname
    apply hn
    simp only [stagedNames, List.mem_append]
    exact .inr (hname ▸ List.mem_map_of_mem hmem)
  · intro header hmem hname
    apply hn
    simp only [stagedNames, List.mem_append]
    exact .inl (hname ▸ List.mem_map_of_mem hmem)

private theorem PrimSpec.Holds.mono_of_same {env env' : VEnv} {s : PrimSpec} {n : Name}
    (H : s.Holds env n) (hle : env ≤ env')
    (same : env'.constants n = env.constants n) : s.Holds env' n := by
  have old : env'.contains n → env.contains n := fun ⟨_, h⟩ => ⟨_, same ▸ h⟩
  have new {m} : env.contains m → env'.contains m := fun ⟨_, h⟩ => ⟨_, hle.constants h⟩
  cases s with
  | containsImplies ns => exact fun h m hm => new (H (old h) m hm)
  | typeEq => exact fun _ h => H _ (same ▸ h)
  | reflectsNatNat => exact fun h => ⟨(H (old h)).1.mono hle, fun a => ((H (old h)).2 a).mono hle⟩
  | reflectsNatNatNat =>
    exact fun h => ⟨(H (old h)).1.mono hle, fun a b => ((H (old h)).2 a b).mono hle⟩
  | reflectsNatNatBool =>
    exact fun h => ⟨(H (old h)).1.mono hle, fun a b => ((H (old h)).2 a b).mono hle⟩
  | reflectsBitwise =>
    exact fun h => ⟨fun _ hc => (H (old h)).1 _ (same ▸ hc),
      fun env'' hle' => (H (old h)).2 env'' (hle.trans hle')⟩
  | stringOfList =>
    intro _ h
    obtain ⟨h1, h2, h3⟩ := H _ (same ▸ h)
    exact ⟨h1, h2.mono hle, h3.mono hle⟩

theorem VEnv.HasPrimitives.mono_of_literals (hp : env.HasPrimitives) (hle : env ≤ env')
    (hliterals : env'.HasPrimitiveLiterals)
    (hconst : ∀ name ∈ [``Char.ofNat, ``String.ofList, ``Nat.add, ``Nat.mul, ``Nat.pow,
      ``Nat.pred, ``Nat.sub, ``Nat.beq, ``Nat.ble, ``Nat.shiftLeft,
      ``Nat.div, ``Nat.shiftRight, ``Nat.mod, ``Nat.gcd, ``Nat.bitwise,
      ``Nat.land, ``Nat.lor, ``Nat.xor], env'.constants name = env.constants name) :
    env'.HasPrimitives := by
  intro p hp'
  rcases p with ⟨name, spec⟩
  simp [primSpecs] at hp'
  rcases hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro h m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (hliterals.bool h).1
    · exact (hliterals.bool h).2
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro ci h; exact hliterals.boolFalse h
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro ci h; exact hliterals.boolTrue h
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro h m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact (hliterals.nat h).1
    · exact (hliterals.nat h).2
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro ci h; exact hliterals.natZero h
  · simp only [PrimSpec.Holds, Prod.fst, Prod.snd]
    intro ci h; exact hliterals.natSucc h
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.add, .reflectsNatNatNat Nat.add) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.pred, .reflectsNatNat Nat.pred) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.sub, .reflectsNatNatNat Nat.sub) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.mul, .reflectsNatNatNat Nat.mul) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.pow, .reflectsNatNatNat Nat.pow) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.gcd, .reflectsNatNatNat Nat.gcd) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.mod, .reflectsNatNatNat Nat.mod) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.div, .reflectsNatNatNat Nat.div) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.beq, .reflectsNatNatBool Nat.beq) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.ble, .reflectsNatNatBool Nat.ble) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.bitwise, .reflectsBitwise) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.land, .reflectsNatNatNat Nat.land) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.lor, .reflectsNatNatNat Nat.lor) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.xor, .reflectsNatNatNat Nat.xor) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.shiftLeft, .reflectsNatNatNat Nat.shiftLeft) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Nat.shiftRight, .reflectsNatNatNat Nat.shiftRight) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``String.ofList, .stringOfList) (by simp [primSpecs])) hle (hconst _ (by simp))
  · exact PrimSpec.Holds.mono_of_same (hp (``Char.ofNat, .typeEq (.forallE .nat .char)) (by simp [primSpecs])) hle (hconst _ (by simp))

theorem boolInductDecl.hasPrimitives (hp : env.HasPrimitives)
    (hheaders : env.addInductHeaders boolInductDecl.types = some headerEnv)
    (hctors : headerEnv.addConstructorHeaders (boolInductDecl.types.flatMap (·.ctors)) = some ctorEnv) :
    ctorEnv.HasPrimitives := by
  have hle := (VEnv.addInductHeaders.le hheaders).trans (VEnv.addConstructorHeaders.le hctors)
  have unchanged (name : Name) (hn : name ∉ [``Bool, ``Bool.false, ``Bool.true]) :
      ctorEnv.constants name = env.constants name :=
    boolInductDecl.stagedConstants_eq hheaders hctors (by simpa [VInductDecl.stagedNames, boolInductDecl] using hn)
  have hfalse : ctorEnv.constants ``Bool.false = some { uvars := 0, type := .bool } := by
    exact VEnv.addConstructorHeaders.constants hctors
      (ctor := { name := ``Bool.false, uvars := 0, type := .bool }) (by simp [boolInductDecl, VExpr.bool])
  have htrue : ctorEnv.constants ``Bool.true = some { uvars := 0, type := .bool } := by
    exact VEnv.addConstructorHeaders.constants hctors
      (ctor := { name := ``Bool.true, uvars := 0, type := .bool }) (by simp [boolInductDecl, VExpr.bool])
  have hliterals : ctorEnv.HasPrimitiveLiterals := {
    bool := fun _ => ⟨⟨_, hfalse⟩, ⟨_, htrue⟩⟩
    boolFalse := fun lookup => Option.some.inj (lookup.symm.trans hfalse)
    boolTrue := fun lookup => Option.some.inj (lookup.symm.trans htrue)
    nat := fun present => by
      obtain ⟨⟨zero, hz⟩, ⟨succ, hs⟩⟩ := hp.nat (by simpa [VEnv.contains, unchanged ``Nat (by simp)] using present)
      exact ⟨⟨zero, hle.constants hz⟩, ⟨succ, hle.constants hs⟩⟩
    natZero := fun lookup => hp.natZero (unchanged ``Nat.zero (by simp) ▸ lookup)
    natSucc := fun lookup => hp.natSucc (unchanged ``Nat.succ (by simp) ▸ lookup) }
  apply hp.mono_of_literals hle hliterals
  intro name hmem
  apply unchanged name
  intro hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hmem

theorem natInductDecl.hasPrimitives (hp : env.HasPrimitives)
    (hheaders : env.addInductHeaders natInductDecl.types = some headerEnv)
    (hctors : headerEnv.addConstructorHeaders (natInductDecl.types.flatMap (·.ctors)) = some ctorEnv) :
    ctorEnv.HasPrimitives := by
  have hle := (VEnv.addInductHeaders.le hheaders).trans (VEnv.addConstructorHeaders.le hctors)
  have unchanged (name : Name) (hn : name ∉ [``Nat, ``Nat.zero, ``Nat.succ]) :
      ctorEnv.constants name = env.constants name :=
    natInductDecl.stagedConstants_eq hheaders hctors (by simpa [VInductDecl.stagedNames, natInductDecl] using hn)
  have hzero : ctorEnv.constants ``Nat.zero = some { uvars := 0, type := .nat } := by
    exact VEnv.addConstructorHeaders.constants hctors
      (ctor := { name := ``Nat.zero, uvars := 0, type := .nat }) (by simp [natInductDecl, VExpr.nat])
  have hsucc : ctorEnv.constants ``Nat.succ = some { uvars := 0, type := .forallE .nat .nat } := by
    exact VEnv.addConstructorHeaders.constants hctors
      (ctor := { name := ``Nat.succ, uvars := 0, type := .forallE .nat .nat }) (by simp [natInductDecl, VExpr.nat])
  have hliterals : ctorEnv.HasPrimitiveLiterals := {
    bool := fun present => by
      obtain ⟨⟨fci, hf⟩, ⟨tci, ht⟩⟩ := hp.bool (by simpa [VEnv.contains, unchanged ``Bool (by simp)] using present)
      exact ⟨⟨fci, hle.constants hf⟩, ⟨tci, hle.constants ht⟩⟩
    boolFalse := fun lookup => hp.boolFalse (unchanged ``Bool.false (by simp) ▸ lookup)
    boolTrue := fun lookup => hp.boolTrue (unchanged ``Bool.true (by simp) ▸ lookup)
    nat := fun _ => ⟨⟨_, hzero⟩, ⟨_, hsucc⟩⟩
    natZero := fun lookup => Option.some.inj (lookup.symm.trans hzero)
    natSucc := fun lookup => Option.some.inj (lookup.symm.trans hsucc) }
  apply hp.mono_of_literals hle hliterals
  intro name hmem
  apply unchanged name
  intro hname
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp at hmem

end Semantic

structure NativePrimitiveSafety (env : Kernel.Environment) : Prop where
  map_wf : env.constants.WF
  safe : ∀ {name ci}, env.constants.find? name = some ci →
    Kernel.Environment.primitives.contains name → ci.safety = .safe ∧ ci.levelParams = []

theorem NativePrimitiveSafety.of_native {env : Kernel.Environment} (hmap : env.constants.WF)
    (hsafe : ∀ {name ci}, env.find? name = some ci →
      Kernel.Environment.primitives.contains name → ci.safety = .safe ∧ ci.levelParams = []) :
    NativePrimitiveSafety env := by
  refine ⟨hmap, ?_⟩
  intro name ci hfind hprim
  apply hsafe ?_ hprim
  simpa only [Kernel.Environment.find?, hmap.find?'_eq_find?] using hfind

theorem NativePrimitiveSafety.find? {env : Kernel.Environment} (hsafe : NativePrimitiveSafety env)
    (hfind : env.find? name = some ci) (hprim : Kernel.Environment.primitives.contains name) :
    ci.safety = .safe ∧ ci.levelParams = [] :=
  hsafe.safe (by simpa only [Kernel.Environment.find?, hsafe.map_wf.find?'_eq_find?] using hfind) hprim

theorem NativePrimitiveSafety.addConst {env : Kernel.Environment} {ci : ConstantInfo}
    (hsafe : NativePrimitiveSafety env) (hfresh : env.constants.find? ci.name = none)
    (hnew : Kernel.Environment.primitives.contains ci.name → ci.safety = .safe ∧ ci.levelParams = []) :
    NativePrimitiveSafety (env.add ci) := by
  refine ⟨hsafe.map_wf.insert _ _ hfresh, ?_⟩
  intro name info hfind hprim
  change (env.constants.insert ci.name ci).find? name = some info at hfind
  rw [hsafe.map_wf.find?_insert] at hfind
  split at hfind
  · rename_i hname
    have hname : ci.name = name := beq_iff_eq.mp hname
    cases hfind
    exact hnew (hname.symm ▸ hprim)
  · exact hsafe.safe hfind hprim

private theorem NativePrimitiveSafety.foldlM {Item State Error : Type}
    (getEnv : State → Kernel.Environment) (step : State → Item → Except Error State)
    (items : List Item) (initial : State) (hsafe : NativePrimitiveSafety (getEnv initial))
    (hstep : ∀ item current, NativePrimitiveSafety (getEnv current) →
      (step current item).WF (fun next => NativePrimitiveSafety (getEnv next))) :
    (items.foldlM step initial).WF fun final => NativePrimitiveSafety (getEnv final) := by
  induction items generalizing initial with
  | nil => exact .pure hsafe
  | cons item items ih =>
    rw [List.foldlM_cons]
    exact (hstep item initial hsafe).bind fun next hnext => ih next hnext

theorem AddInductive.declareInductiveTypes.preservesPrimitiveSafety
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (hsafe : NativePrimitiveSafety ctx.env)
    (hguard : ctx.allowPrimitive = false ∨ isUnsafe = false ∧ ctx.lparams = []) :
    (declareInductiveTypes stats numParams types numNested isUnsafe ctx).WF NativePrimitiveSafety := by
  unfold declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  rw [Array.toList_zipWith, ← List.map_uncurry_zip_eq_zipWith, List.foldlM_map]
  apply NativePrimitiveSafety.foldlM id _ _ _ hsafe
  intro input env hsafe
  rcases input with ⟨type, index⟩
  refine (checkName.WF hsafe.map_wf type.name ctx.allowPrimitive).bind fun _ ⟨hfresh, hprim⟩ => ?_
  have hfresh' : (id env).constants.find?
      (ConstantInfo.inductInfo (Function.uncurry (fun indType numIndices => {
        name := indType.name, levelParams := ctx.lparams, type := indType.type,
        numParams := numParams, numIndices := numIndices,
        all := (Array.map (fun x => x.name) types).toList,
        ctors := List.map (fun x => x.name) indType.ctors, numNested := numNested,
        isRec := isRec types stats.indConsts, isUnsafe := isUnsafe,
        isReflexive := isReflexive types stats.indConsts }) (type, index))).name = none := by
    rw [Kernel.Environment.find?, hsafe.map_wf.find?'_eq_find?] at hfresh
    simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, Function.uncurry] using hfresh
  refine .pure (hsafe.addConst hfresh' ?_)
  intro hcontains
  dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal, Function.uncurry] at hcontains
  rcases hguard with hallow | ⟨hunsafe, hparams⟩
  · cases hprimitive : Kernel.Environment.primitives.contains type.name with
    | false => rw [hprimitive] at hcontains; contradiction
    | true =>
      have hallow' : ctx.allowPrimitive = true := hprim (by simp [hprimitive])
      cases hallow ▸ hallow'
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
      ConstantInfo.levelParams, ConstantInfo.toConstantVal, hunsafe] using
      And.intro (Eq.refl DefinitionSafety.safe) hparams

theorem AddInductive.declareConstructors.preservesPrimitiveSafety
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (types : Array InductiveType) (isUnsafe : Bool) (hsafe : NativePrimitiveSafety ctx.env)
    (hguard : ctx.allowPrimitive = false ∨ isUnsafe = false ∧ ctx.lparams = []) :
    (declareConstructors stats types isUnsafe ctx).WF NativePrimitiveSafety := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  apply NativePrimitiveSafety.foldlM id _ _ _ hsafe
  intro type env hsafe
  refine Except.WF.bind ?_ (fun state hnext => .pure hnext)
  apply NativePrimitiveSafety.foldlM Prod.snd _ _ _ hsafe
  intro ctor state hsafe
  refine (checkName.WF hsafe.map_wf ctor.name ctx.allowPrimitive).bind fun _ ⟨hfresh, hprim⟩ => ?_
  have hfresh' : state.2.constants.find?
      (ConstantInfo.ctorInfo {
        name := ctor.name, levelParams := ctx.lparams, type := ctor.type, induct := type.name,
        cidx := state.fst, numParams := stats.params.size, numFields :=
          assert! AddInductive.declareConstructors.arity 0 ctor.type ≥ stats.params.size;
          AddInductive.declareConstructors.arity 0 ctor.type - stats.params.size,
        isUnsafe := isUnsafe }).name = none := by
    simpa only [Kernel.Environment.find?, hsafe.map_wf.find?'_eq_find?, ConstantInfo.name,
      ConstantInfo.toConstantVal] using hfresh
  refine .pure (hsafe.addConst hfresh' ?_)
  intro hcontains
  dsimp only [ConstantInfo.name, ConstantInfo.toConstantVal] at hcontains
  rcases hguard with hallow | ⟨hunsafe, hparams⟩
  · cases hprimitive : Kernel.Environment.primitives.contains ctor.name with
    | false => rw [hprimitive] at hcontains; contradiction
    | true =>
      have hallow' : ctx.allowPrimitive = true := hprim (by simp [hprimitive])
      cases hallow ▸ hallow'
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial,
      ConstantInfo.levelParams, ConstantInfo.toConstantVal, hunsafe] using
      And.intro (Eq.refl DefinitionSafety.safe) hparams

theorem AddInductive.checkInductiveTypes.preservesHeaderConstructorPrimitiveSafety
    (ctx : AddInductive.Context) (numParams : Nat) (types : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (hsafe : NativePrimitiveSafety ctx.env)
    (hguard : ctx.allowPrimitive = false ∨ isUnsafe = false ∧ ctx.lparams = []) :
    (checkInductiveTypes numParams types (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types numNested isUnsafe) do
        checkConstructors types stats isUnsafe
        declareConstructors stats types isUnsafe) ctx).WF NativePrimitiveSafety := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current _ hframe
  have hguard' : current.allowPrimitive = false ∨ isUnsafe = false ∧ current.lparams = [] := by
    simpa only [hframe.allowPrimitive, hframe.lparams] using hguard
  refine (declareInductiveTypes.preservesPrimitiveSafety current stats numParams types numNested isUnsafe
    (by simpa only [hframe.env] using hsafe) hguard').bind ?_
  intro nativeHeaders headerSafe
  refine (show (checkConstructors types stats isUnsafe
    { current with env := nativeHeaders }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
  intro _ _
  exact declareConstructors.preservesPrimitiveSafety { current with env := nativeHeaders }
    stats types isUnsafe headerSafe hguard'

theorem Environment.PrimitiveInductiveDecl.safeMonomorphic
    (hshape : PrimitiveInductiveDecl lparams numParams types isUnsafe) :
    isUnsafe = false ∧ lparams = [] := by
  cases hshape <;> exact ⟨rfl, rfl⟩

theorem AddInductive.checkInductiveTypes.refinesPrimitiveInterfaces
    (ctx : AddInductive.Context) (numParams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    (hchecker : CheckerEnv safety ctx.env venv) (hp : venv.HasPrimitives)
    (hsafe : NativePrimitiveSafety ctx.env)
    (hprimitive : Environment.checkPrimitiveInductive
      ctx.env ctx.lparams numParams types isUnsafe = .ok true) :
    (checkInductiveTypes numParams types.toArray (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
        checkConstructors types.toArray stats isUnsafe
        declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (·.ctors)) = some ctorEnv ∧
        CheckerEnv safety env' ctorEnv ∧ ctorEnv.HasPrimitives ∧ NativePrimitiveSafety env' := by
  intro env' accepted
  obtain ⟨decl, headerEnv, ctorEnv, hdecl, haddHeaders, headerWF, htr, haddCtors, hfinal⟩ :=
    refinesPrimitiveHeaderConstructorChecker ctx numParams types numNested isUnsafe
      hchecker hprimitive env' accepted
  have hshape := (Environment.checkPrimitiveInductive.eq_true_iff
    ctx.env ctx.lparams numParams types isUnsafe).mp hprimitive
  have hsafety := preservesHeaderConstructorPrimitiveSafety ctx numParams types.toArray numNested isUnsafe
    hsafe (.inr hshape.safeMonomorphic) env' accepted
  have hp' : ctorEnv.HasPrimitives := by
    rcases hdecl with rfl | rfl
    · exact boolInductDecl.hasPrimitives hp haddHeaders haddCtors
    · exact natInductDecl.hasPrimitives hp haddHeaders haddCtors
  exact ⟨decl, headerEnv, ctorEnv, hdecl, haddHeaders, headerWF, htr, haddCtors, hfinal, hp', hsafety⟩

end Lean4Lean
