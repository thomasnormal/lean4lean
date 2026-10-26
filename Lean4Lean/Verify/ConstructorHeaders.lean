import Lean4Lean.Theory.ConstructorHeaders
import Lean4Lean.Verify.InductiveHeaders

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.Aligned.constants_eq_none from Lean4Lean.Verify.InductiveHeaders
open private Lean4Lean.boolInductDecl.tr Lean4Lean.natInductDecl.tr
  from Lean4Lean.Verify.Inductive

private theorem forall₂_mono {α β : Type} {R S : α → β → Prop}
    (h : ∀ a b, R a b → S a b) : ∀ {as bs}, List.Forall₂ R as bs → List.Forall₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hhead htail => .cons (h _ _ hhead) (forall₂_mono h htail)

private theorem registerConstructorHeaders.WF {safety : DefinitionSafety}
    {env : Kernel.Environment} {venv : VEnv} {lparams : List Name}
    {ctors : List Constructor} {headers : List VConstVal} (index : Nat) (allowPrimitive : Bool)
    (makeInfo : Nat → Constructor → ConstructorVal)
    (hmap : ∀ venv index ctor header, TrConstructor venv lparams ctor header →
      (makeInfo index ctor).name = header.name ∧
        TrConstant safety venv (.ctorInfo (makeInfo index ctor)) header.toVConstant)
    (haligned : Aligned safety env.constants venv)
    (hctors : List.Forall₂ (TrConstructor venv lparams) ctors headers) :
    (ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
      state.2.checkName ctor.name allowPrimitive
      pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo state.1 ctor)))) (index, env)).WF
      fun state => ∃ venv', venv.addConstructorHeaders headers = some venv' ∧
        Aligned safety state.2.constants venv' := by
  induction ctors generalizing index env venv headers with
  | nil => cases hctors; exact .pure ⟨venv, rfl, haligned⟩
  | cons ctor ctors ih =>
    cases hctors with
    | cons hctor hrest =>
      rename_i header headers
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (checkName.WF haligned.map_wf ctor.name allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
      obtain ⟨hname, hinfo⟩ := hmap venv index ctor header hctor
      have hfresh' : env.constants.find? ctor.name = none := by
        simpa only [Kernel.Environment.find?, haligned.map_wf.find?'_eq_find?] using hfresh
      have hvfresh : venv.constants header.name = none :=
        hctor.1 ▸ haligned.constants_eq_none hfresh'
      obtain ⟨next, hstep⟩ : ∃ next, venv.addConst header.name header.toVConstant = some next := by
        simp [VEnv.addConst, hvfresh]
      have hnext := haligned.const
        (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal, hname, hctor.1] using hfresh') hinfo
        (hname.symm ▸ hstep) rfl
      have hle := VEnv.addConst_le hstep
      refine (ih (index + 1) hnext
        (forall₂_mono (fun _ _ htr => htr.mono hle) hrest)).mono ?_
      intro state hresult
      obtain ⟨venv', hadd, haligned'⟩ := hresult
      exact ⟨venv', by simpa [VEnv.addConstructorHeaders, hstep] using hadd, haligned'⟩

private theorem registerConstructorTypes.WF {safety : DefinitionSafety}
    {env : Kernel.Environment} {venv : VEnv} {lparams : List Name}
    {types : List InductiveType} {vtypes : List VInductiveType} (allowPrimitive : Bool)
    (makeInfo : InductiveType → Nat → Constructor → ConstructorVal)
    (hmap : ∀ venv type index ctor header, TrConstructor venv lparams ctor header →
      (makeInfo type index ctor).name = header.name ∧
        TrConstant safety venv (.ctorInfo (makeInfo type index ctor)) header.toVConstant)
    (haligned : Aligned safety env.constants venv)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv lparams) type.ctors vtype.ctors) types vtypes) :
    (types.foldlM (fun (env : Kernel.Environment) (type : InductiveType) => do
      let state ← type.ctors.foldlM (fun (state : Nat × Kernel.Environment) (ctor : Constructor) => do
        state.2.checkName ctor.name allowPrimitive
        pure (state.1 + 1, state.2.add (.ctorInfo (makeInfo type state.1 ctor)))) (0, env)
      pure state.2) env).WF fun env' =>
        ∃ venv', venv.addConstructorHeaders
          (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
          Aligned safety env'.constants venv' := by
  induction types generalizing env venv vtypes with
  | nil => cases hctors; exact .pure ⟨venv, rfl, haligned⟩
  | cons type types ih =>
    cases hctors with
    | cons hctor hrest =>
      rename_i vtype vtypes
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (registerConstructorHeaders.WF 0 allowPrimitive (makeInfo type)
        (fun venv => hmap venv type) haligned hctor).bind fun state hresult => ?_
      obtain ⟨next, hstep, hnext⟩ := hresult
      have hle := VEnv.addConstructorHeaders.le hstep
      refine (ih hnext
        (forall₂_mono (fun _ _ hctors =>
          forall₂_mono (fun _ _ htr => htr.mono hle) hctors) hrest)).mono ?_
      intro env' hresult
      obtain ⟨venv', hadd, haligned'⟩ := hresult
      exact ⟨venv', by simpa [List.flatMap_cons, VEnv.addConstructorHeaders.append, hstep]
        using hadd, haligned'⟩

theorem AddInductive.declareConstructors.refines (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        Aligned safety env'.constants venv' := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  let makeInfo (type : InductiveType) (index : Nat) (ctor : Constructor) : ConstructorVal := {
    name := ctor.name, levelParams := ctx.lparams, type := ctor.type, induct := type.name,
    cidx := index, numParams := stats.params.size, isUnsafe
    numFields := assert! AddInductive.declareConstructors.arity 0 ctor.type ≥ stats.params.size;
      AddInductive.declareConstructors.arity 0 ctor.type - stats.params.size }
  apply registerConstructorTypes.WF ctx.allowPrimitive makeInfo ?_ haligned hctors
  intro venv type index ctor header htr
  refine ⟨htr.1, ?_, htr.2.1, htr.2.2⟩
  simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial] using hsafety

theorem AddInductive.declareConstructors.ordered (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hordered : venv.Ordered)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        Aligned safety env'.constants venv' ∧ venv'.Ordered :=
  (declareConstructors.refines ctx stats indTypes isUnsafe haligned hsafety hctors).mono
    fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, haligned', VEnv.addConstructorHeaders.ordered hordered htypes hadd⟩

theorem AddInductive.declareConstructors.refinesWF (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        venv'.WF ∧ Aligned safety env'.constants venv' :=
  (declareConstructors.refines ctx stats indTypes isUnsafe haligned hsafety hctors).mono
    fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, VEnv.addConstructorHeaders.wf hvenv htypes hadd, haligned'⟩

theorem AddInductive.declareConstructors.preservesValues (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    (hmap : ctx.env.constants.WF) :
    (declareConstructors stats indTypes isUnsafe ctx).WF (NativeValueFrame ctx.env) := by
  unfold declareConstructors
  dsimp only
  rw [← Array.foldlM_toList]
  apply NativeValueFrame.foldlM id _ _ _ hmap
  intro type env hmap
  refine Except.WF.bind ?_ (fun state hframe => .pure hframe)
  apply NativeValueFrame.foldlM Prod.snd _ _ _ hmap
  intro ctor state hmap
  refine (checkName.WF hmap ctor.name ctx.allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
  exact .pure (NativeValueFrame.addConst hmap
    (by simpa only [Kernel.Environment.find?, hmap.find?'_eq_find?, ConstantInfo.name,
      ConstantInfo.toConstantVal] using hfresh) rfl)

theorem AddInductive.declareConstructors.refinesChecker (ctx : AddInductive.Context)
    (stats : AddInductive.InductiveStats) (indTypes : Array InductiveType) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {vtypes : List VInductiveType}
    (hchecker : CheckerEnv safety ctx.env venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hctors : List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
      List.Forall₂ (TrConstructor venv ctx.lparams) type.ctors vtype.ctors)
      indTypes.toList vtypes)
    (htypes : ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
      ctor.toVConstant.WF venv) :
    (declareConstructors stats indTypes isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addConstructorHeaders
        (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some venv' ∧
        CheckerEnv safety env' venv' := by
  intro env' accepted
  obtain ⟨venv', hadd, hvenv, haligned⟩ :=
    declareConstructors.refinesWF ctx stats indTypes isUnsafe hchecker.aligned hchecker.wf
      hsafety hctors htypes env' accepted
  have hframe := declareConstructors.preservesValues ctx stats indTypes isUnsafe
    hchecker.map_wf env' accepted
  exact ⟨venv', hadd, hchecker.of_valueFrame hframe (VEnv.addConstructorHeaders.le hadd)
    hvenv haligned⟩

theorem AddInductive.checkInductiveTypes.preservesHeaderConstructorValues
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (hmap : ctx.env.constants.WF) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      withEnv (← declareInductiveTypes stats numParams indTypes numNested isUnsafe) do
        checkConstructors indTypes stats isUnsafe
        declareConstructors stats indTypes isUnsafe) ctx).WF (NativeValueFrame ctx.env) := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current _ hframe
  refine (declareInductiveTypes.preservesValues current stats numParams indTypes numNested isUnsafe
    (by simpa only [hframe.env] using hmap)).bind ?_
  intro nativeHeaders headerFrame
  refine (show (checkConstructors indTypes stats isUnsafe
    { current with env := nativeHeaders }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
  intro _ _
  refine (declareConstructors.preservesValues { current with env := nativeHeaders }
    stats indTypes isUnsafe headerFrame.map_wf).mono ?_
  intro nativeCtors constructorFrame
  simpa only [hframe.env] using headerFrame.trans constructorFrame

theorem AddInductive.checkInductiveTypes.refinesHeaderConstructorWF
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    {vtypes : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (headerTypes : ∀ header ∈ headers, header.toVConstant.WF venv)
    (hctors : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      List.Forall₂ (fun (type : InductiveType) (vtype : VInductiveType) =>
        List.Forall₂ (TrConstructor headerEnv ctx.lparams) type.ctors vtype.ctors)
        indTypes.toList vtypes)
    (constructorTypes : ∀ headerEnv, venv.addInductHeaders headers = some headerEnv →
      ∀ ctor ∈ vtypes.flatMap (fun type : VInductiveType => type.ctors),
        ctor.toVConstant.WF headerEnv) :
    (checkInductiveTypes numParams indTypes (fun stats => do
      let nativeHeaders ← declareInductiveTypes stats numParams indTypes numNested isUnsafe
      withEnv nativeHeaders (declareConstructors stats indTypes isUnsafe)) ctx).WF fun env' =>
      ∃ headerEnv ctorEnv,
        venv.addInductHeaders headers = some headerEnv ∧ headerEnv.WF ∧
        headerEnv.addConstructorHeaders
          (vtypes.flatMap (fun type : VInductiveType => type.ctors)) = some ctorEnv ∧
        ctorEnv.WF ∧ Aligned safety env'.constants ctorEnv := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats ctx' hsizes hframe
  refine (declareInductiveTypes.refinesWF ctx' stats numParams indTypes numNested isUnsafe
    (by simpa [hframe.env] using haligned) hvenv hsafety hsizes.1
    (by simpa [hframe.lparams] using hheaders) headerTypes).bind ?_
  rintro nativeHeaders ⟨headerEnv, haddHeaders, headerWF, headerAligned⟩
  have hctorModels := hctors headerEnv haddHeaders
  have hconstructorTypes := constructorTypes headerEnv haddHeaders
  refine (declareConstructors.refinesWF { ctx' with env := nativeHeaders } stats indTypes isUnsafe
    (by simpa [hframe.env, headerAligned]) headerWF hsafety
    (by simpa [hframe.lparams] using hctorModels) hconstructorTypes).mono ?_
  rintro ctorNative ⟨ctorEnv, haddCtors, ctorWF, ctorAligned⟩
  exact ⟨headerEnv, ctorEnv, haddHeaders, headerWF, haddCtors, ctorWF, ctorAligned⟩

theorem AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorWF
    (ctx : AddInductive.Context) (numParams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hprimitive : Environment.checkPrimitiveInductive
      ctx.env ctx.lparams numParams types isUnsafe = .ok true) :
    (checkInductiveTypes numParams types.toArray (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
        checkConstructors types.toArray stats isUnsafe
        declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) = some ctorEnv ∧
        ctorEnv.WF ∧ Aligned safety env'.constants ctorEnv := by
  have register (decl : VInductDecl)
      (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
      (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) types decl.types)
      (htypes : decl.HeadersWF venv)
      (htranslation : ∀ headerEnv, venv.addInductHeaders decl.types = some headerEnv →
        TrInductDecl venv headerEnv ctx.lparams numParams types decl)
      (hctors : ∀ headerEnv, venv.addInductHeaders decl.types = some headerEnv →
        ∀ ctor ∈ decl.types.flatMap (fun type => type.ctors), ctor.toVConstant.WF headerEnv) :
      (checkInductiveTypes numParams types.toArray (fun stats => do
        withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
          checkConstructors types.toArray stats isUnsafe
          declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
        ∃ headerEnv ctorEnv,
          venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
          TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
          headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) = some ctorEnv ∧
          ctorEnv.WF ∧ Aligned safety env'.constants ctorEnv := by
    apply checkInductiveTypes.frameHeaderSizes
    intro stats current hsizes hframe
    refine (declareInductiveTypes.refinesWF current stats numParams types.toArray numNested isUnsafe
      (by simpa only [hframe.env] using haligned) hvenv hsafety hsizes.1
      (by simpa only [List.toList_toArray, hframe.lparams] using hheaders)
      (fun header hmem => (htypes header hmem).2)).bind ?_
    rintro nativeHeaders ⟨headerEnv, haddHeaders, headerWF, headerAligned⟩
    have htr := htranslation headerEnv haddHeaders
    have ctorModels := forall₂_mono (fun _ _ translated => translated.2.2.2) htr.2.2
    refine (show (checkConstructors types.toArray stats isUnsafe
      { current with env := nativeHeaders }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
    intro _ _
    refine (declareConstructors.refinesWF { current with env := nativeHeaders }
      stats types.toArray isUnsafe headerAligned headerWF hsafety
      (by simpa only [List.toList_toArray, hframe.lparams] using ctorModels)
      (hctors headerEnv haddHeaders)).mono ?_
    rintro nativeCtors ⟨ctorEnv, haddCtors, ctorWF, ctorAligned⟩
    exact ⟨headerEnv, ctorEnv, haddHeaders, headerWF, htr, haddCtors, ctorWF, ctorAligned⟩
  have hdecl := (Environment.checkPrimitiveInductive.eq_true_iff
    ctx.env ctx.lparams numParams types isUnsafe).mp hprimitive
  generalize huniverses : ctx.lparams = universes at hdecl
  cases hdecl with
  | bool =>
    refine (register boolInductDecl DefinitionSafety.le_safe
      (by simpa [huniverses, boolInductDecl] using
        (List.Forall₂.cons ⟨rfl, rfl, TrExprS.sort rfl⟩ List.Forall₂.nil))
      boolInductDecl.headersWF
      (fun headerEnv hadd => by
        simpa only [huniverses] using Lean4Lean.boolInductDecl.tr venv hadd)
      (fun _ hadd => boolInductDecl.constructorWF hadd)).mono ?_
    rintro env' ⟨headerEnv, ctorEnv, result⟩
    exact ⟨boolInductDecl, headerEnv, ctorEnv, .inl rfl,
      by simpa only [huniverses] using result⟩
  | nat binderName binderInfo =>
    refine (register natInductDecl DefinitionSafety.le_safe
      (by simpa [huniverses, natInductDecl] using
        (List.Forall₂.cons ⟨rfl, rfl, TrExprS.sort rfl⟩ List.Forall₂.nil))
      natInductDecl.headersWF
      (fun headerEnv hadd => by
        simpa only [huniverses] using Lean4Lean.natInductDecl.tr venv binderName binderInfo hadd)
      (fun _ hadd => natInductDecl.constructorWF hadd)).mono ?_
    rintro env' ⟨headerEnv, ctorEnv, result⟩
    exact ⟨natInductDecl, headerEnv, ctorEnv, .inr rfl,
      by simpa only [huniverses] using result⟩

theorem AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorChecker
    (ctx : AddInductive.Context) (numParams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    (hchecker : CheckerEnv safety ctx.env venv)
    (hprimitive : Environment.checkPrimitiveInductive
      ctx.env ctx.lparams numParams types isUnsafe = .ok true) :
    (checkInductiveTypes numParams types.toArray (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
        checkConstructors types.toArray stats isUnsafe
        declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) = some ctorEnv ∧
        CheckerEnv safety env' ctorEnv := by
  intro env' accepted
  obtain ⟨decl, headerEnv, ctorEnv, hdecl, haddHeaders, headerWF, htr, haddCtors, ctorWF, haligned⟩ :=
    refinesPrimitiveHeaderConstructorWF ctx numParams types numNested isUnsafe
      hchecker.aligned hchecker.wf hprimitive env' accepted
  have hframe := preservesHeaderConstructorValues ctx numParams types.toArray numNested isUnsafe
    hchecker.map_wf env' accepted
  exact ⟨decl, headerEnv, ctorEnv, hdecl, haddHeaders, headerWF, htr, haddCtors,
    hchecker.of_valueFrame hframe
      ((VEnv.addInductHeaders.le haddHeaders).trans (VEnv.addConstructorHeaders.le haddCtors))
      ctorWF haligned⟩

/- The primitive preflight also supplies the semantic declaration model itself.  Pair that
   receipt with the checked header/constructor registration so the staged frontend exposes a
   genuine `VDecl.WF` witness.  Recursors remain outside this theorem: they are added by the
   later `AddInductWithRecursorsEvidence` boundary. -/
theorem AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorVDeclWF
    (ctx : AddInductive.Context) (numParams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    (haligned : Aligned safety ctx.env.constants venv) (hvenv : venv.WF)
    (hprimitive : Environment.checkPrimitiveInductive
      ctx.env ctx.lparams numParams types isUnsafe = .ok true) :
    (checkInductiveTypes numParams types.toArray (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
        checkConstructors types.toArray stats isUnsafe
        declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧ decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧
        ctorEnv.WF ∧ VDecl.WF venv (.induct decl) ctorEnv ∧
        Aligned safety env'.constants ctorEnv := by
  refine (AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorWF
    ctx numParams types numNested isUnsafe haligned hvenv hprimitive).mono ?_
  rintro env' ⟨decl, headerEnv, ctorEnv, hkind, hheaderAdd, hheaderWF, htr, hctorAdd,
    hctorWF, haligned'⟩
  have hp := (Environment.checkPrimitiveInductive.eq_true_iff
    ctx.env ctx.lparams numParams types isUnsafe).mp hprimitive
  generalize huniverses : ctx.lparams = universes at hp
  cases hp with
  | bool =>
    have hdeclEq : decl = boolInductDecl := by
      rcases hkind with hdecl | hdecl
      · exact hdecl
      · subst decl
        have hcross := htr.2
        simp [natInductDecl] at hcross
        have hn := hcross.1
        simp at hn
    subst decl
    have hadd : venv.addInduct boolInductDecl = some ctorEnv := by
      unfold VEnv.addInduct
      rw [hheaderAdd]
      exact hctorAdd
    exact ⟨boolInductDecl, headerEnv, ctorEnv, .inl rfl, boolInductDecl.headersWF,
      boolInductDecl.wf_public venv, hheaderAdd, hheaderWF,
      (by simpa [huniverses] using htr), hctorAdd, hctorWF,
      .induct (boolInductDecl.wf_public venv) hadd, haligned'⟩
  | nat binderName binderInfo =>
    have hdeclEq : decl = natInductDecl := by
      rcases hkind with hdecl | hdecl
      · subst decl
        have hcross := htr.2
        simp [boolInductDecl] at hcross
        have hn := hcross.1
        simp at hn
      · exact hdecl
    subst decl
    have hadd : venv.addInduct natInductDecl = some ctorEnv := by
      unfold VEnv.addInduct
      rw [hheaderAdd]
      exact hctorAdd
    exact ⟨natInductDecl, headerEnv, ctorEnv, .inr rfl, natInductDecl.headersWF,
      natInductDecl.wf_public venv, hheaderAdd, hheaderWF,
      (by simpa [huniverses] using htr), hctorAdd, hctorWF,
      .induct (natInductDecl.wf_public venv) hadd, haligned'⟩

/- Consume the same staged receipt against a checker environment.  The
   `NativeValueFrame` transport keeps safe-value checking explicit while the
   semantic `VDecl.WF` witness records the registered inductive declaration. -/
theorem AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerVDeclWF
    (ctx : AddInductive.Context) (numParams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) {safety : DefinitionSafety} {venv : VEnv}
    (hchecker : CheckerEnv safety ctx.env venv)
    (hprimitive : Environment.checkPrimitiveInductive
      ctx.env ctx.lparams numParams types isUnsafe = .ok true) :
    (checkInductiveTypes numParams types.toArray (fun stats => do
      withEnv (← declareInductiveTypes stats numParams types.toArray numNested isUnsafe) do
        checkConstructors types.toArray stats isUnsafe
        declareConstructors stats types.toArray isUnsafe) ctx).WF fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧ decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv ctx.lparams numParams types decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧
        ctorEnv.WF ∧ VDecl.WF venv (.induct decl) ctorEnv ∧
        CheckerEnv safety env' ctorEnv := by
  intro env' accepted
  obtain ⟨decl, headerEnv, ctorEnv, hkind, hheaders, hdeclWF, hheaderAdd, hheaderWF,
      htr, hctorAdd, hctorWF, hdeclVWF, haligned'⟩ :=
    (AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorVDeclWF
      ctx numParams types numNested isUnsafe hchecker.aligned hchecker.wf hprimitive)
      env' accepted
  have hframe := AddInductive.checkInductiveTypes.preservesHeaderConstructorValues
    ctx numParams types.toArray numNested isUnsafe hchecker.map_wf env' accepted
  exact ⟨decl, headerEnv, ctorEnv, hkind, hheaders, hdeclWF, hheaderAdd, hheaderWF,
    htr, hctorAdd, hctorWF, hdeclVWF,
    hchecker.of_valueFrame hframe
      ((VEnv.addInductHeaders.le hheaderAdd).trans
        (VEnv.addConstructorHeaders.le hctorAdd)) hctorWF haligned'⟩

end Lean4Lean
