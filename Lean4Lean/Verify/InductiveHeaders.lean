import Lean4Lean.Verify.Inductive
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.InductiveStats

namespace Lean4Lean
open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment

def TrInductiveHeader (env : VEnv) (lparams : List Name)
    (type : InductiveType) (header : VInductiveType) : Prop :=
  type.name = header.name ∧ lparams.length = header.uvars ∧
    TrExprS env lparams [] type.type header.type

theorem TrInductiveType.header {env ctorEnv : VEnv} {lparams : List Name}
    {type : InductiveType} {header : VInductiveType}
    (htr : TrInductiveType env ctorEnv lparams type header) :
    TrInductiveHeader env lparams type header := ⟨htr.1, htr.2.1, htr.2.2.1⟩

private theorem Aligned.constants_eq_none {safety : DefinitionSafety}
    {constants : ConstMap} {venv : VEnv} {name : Name}
    (haligned : Aligned safety constants venv) (hfresh : constants.find? name = none) :
    venv.constants name = none := by
  apply Option.not_isSome_iff_eq_none.1
  rw [Option.isSome_iff_exists]
  rintro ⟨constant, hconstant⟩
  obtain ⟨info, hinfo, _⟩ := haligned.find?_iff.2 ⟨constant, hconstant⟩
  rw [hfresh] at hinfo
  contradiction

private theorem registerInductiveHeaders.WF {safety : DefinitionSafety}
    {env : Kernel.Environment} {venv : VEnv} {infos : List InductiveVal}
    {headers : List VInductiveType} (allowPrimitive : Bool)
    (haligned : Aligned safety env.constants venv)
    (hheaders : List.Forall₂ (fun info header => info.name = header.name ∧
      TrConstant safety venv (.inductInfo info) header.toVConstant) infos headers) :
    (infos.foldlM (fun (env : Kernel.Environment) (info : InductiveVal) => do
      Kernel.Environment.checkName env info.name allowPrimitive
      pure (env.add (.inductInfo info))) env).WF fun env' =>
        ∃ venv', venv.addInductHeaders headers = some venv' ∧
          Aligned safety env'.constants venv' := by
  induction infos generalizing env venv headers with
  | nil =>
    cases hheaders
    exact .pure ⟨venv, rfl, haligned⟩
  | cons info infos ih =>
    cases hheaders with
    | cons hinfo hrest =>
      rename_i header headers
      simp only [List.foldlM_cons, bind_assoc, pure_bind]
      refine (checkName.WF env info.name allowPrimitive).bind fun _ ⟨hfresh, _⟩ => ?_
      have hvfresh : venv.constants header.name = none :=
        hinfo.1 ▸ haligned.constants_eq_none hfresh
      obtain ⟨nextVenv, hstep⟩ :
          ∃ nextVenv, venv.addConst header.name header.toVConstant = some nextVenv := by
        simp [VEnv.addConst, hvfresh]
      have hnext := haligned.const hfresh hinfo.2 (hinfo.1.symm ▸ hstep) rfl
      have hle := VEnv.addConst_le hstep
      refine (ih hnext (hrest.imp fun info header htr => ⟨htr.1, htr.2.mono hle⟩)).mono ?_
      intro env' hresult
      obtain ⟨venv', hadd, haligned'⟩ := hresult
      exact ⟨venv', by simpa [VEnv.addInductHeaders, hstep] using hadd, haligned'⟩

private theorem zipInductiveHeaders {safety : DefinitionSafety} {venv : VEnv}
    {lparams : List Name} {types : List InductiveType} {indices : List Nat}
    {headers : List VInductiveType} (makeInfo : InductiveType → Nat → InductiveVal)
    (hmap : ∀ type index header, TrInductiveHeader venv lparams type header →
      (makeInfo type index).name = header.name ∧
        TrConstant safety venv (.inductInfo (makeInfo type index)) header.toVConstant)
    (hsize : indices.length = types.length)
    (hheaders : List.Forall₂ (TrInductiveHeader venv lparams) types headers) :
    List.Forall₂ (fun info header => info.name = header.name ∧
      TrConstant safety venv (.inductInfo info) header.toVConstant)
      (types.zipWith makeInfo indices) headers := by
  induction hheaders generalizing indices with
  | nil => simp at hsize; subst indices; exact .nil
  | cons hheader hheaders ih =>
    cases indices with
    | nil => simp at hsize
    | cons index indices =>
      exact .cons (hmap _ index _ hheader) (ih (by simpa using hsize))

theorem AddInductive.declareInductiveTypes.refines
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hsize : stats.nindices.size = indTypes.size)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers) :
    (declareInductiveTypes stats numParams indTypes numNested isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addInductHeaders headers = some venv' ∧
        Aligned safety env'.constants venv' := by
  unfold declareInductiveTypes
  dsimp only
  rw [← Array.foldlM_toList]
  apply registerInductiveHeaders.WF ctx.allowPrimitive haligned
  rw [Array.toList_zipWith]
  refine zipInductiveHeaders _ ?_ (by simpa using hsize) hheaders
  intro type index header htr
  refine ⟨htr.1, ?_, htr.2.1, htr.2.2⟩
  simpa [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial] using hsafety

theorem AddInductive.declareInductiveTypes.ordered
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hordered : venv.Ordered)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hsize : stats.nindices.size = indTypes.size)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF venv) :
    (declareInductiveTypes stats numParams indTypes numNested isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addInductHeaders headers = some venv' ∧
        Aligned safety env'.constants venv' ∧ venv'.Ordered :=
  (declareInductiveTypes.refines ctx stats numParams indTypes numNested isUnsafe
    haligned hsafety hsize hheaders).mono fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, haligned', VEnv.addInductHeaders.ordered hordered htypes hadd⟩

theorem AddInductive.declareInductiveTypes.refinesWF
    (ctx : AddInductive.Context) (stats : AddInductive.InductiveStats)
    (numParams : Nat) (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hsize : stats.nindices.size = indTypes.size)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF venv) :
    (declareInductiveTypes stats numParams indTypes numNested isUnsafe ctx).WF fun env' =>
      ∃ venv', venv.addInductHeaders headers = some venv' ∧
        venv'.WF ∧ Aligned safety env'.constants venv' :=
  (declareInductiveTypes.refines ctx stats numParams indTypes numNested isUnsafe
    haligned hsafety hsize hheaders).mono fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, VEnv.addInductHeaders.wf hvenv htypes hadd, haligned'⟩

theorem AddInductive.checkInductiveTypes.refinesHeaders
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers) :
    (checkInductiveTypes numParams indTypes
      (fun stats => declareInductiveTypes stats numParams indTypes numNested isUnsafe) ctx).WF
      fun env' => ∃ venv', venv.addInductHeaders headers = some venv' ∧
        Aligned safety env'.constants venv' := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats ctx' hsizes hframe
  apply declareInductiveTypes.refines ctx' stats numParams indTypes numNested isUnsafe
    (by simpa [hframe.env] using haligned) hsafety hsizes.1
    (by simpa [hframe.lparams] using hheaders)

theorem AddInductive.checkInductiveTypes.refinesHeadersWF
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv)
    (hvenv : venv.WF)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF venv) :
    (checkInductiveTypes numParams indTypes
      (fun stats => declareInductiveTypes stats numParams indTypes numNested isUnsafe) ctx).WF
      fun env' => ∃ venv', venv.addInductHeaders headers = some venv' ∧
        venv'.WF ∧ Aligned safety env'.constants venv' := by
  apply checkInductiveTypes.frameHeaderSizes
  intro stats ctx' hsizes hframe
  apply declareInductiveTypes.refinesWF ctx' stats numParams indTypes numNested isUnsafe
    (by simpa [hframe.env] using haligned) hvenv hsafety hsizes.1
    (by simpa [hframe.lparams] using hheaders) htypes

theorem AddInductive.checkInductiveTypes.orderedHeaders
    (ctx : AddInductive.Context) (numParams : Nat) (indTypes : Array InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    {safety : DefinitionSafety} {venv : VEnv} {headers : List VInductiveType}
    (haligned : Aligned safety ctx.env.constants venv) (hordered : venv.Ordered)
    (hsafety : safety ≤ if isUnsafe then .unsafe else .safe)
    (hheaders : List.Forall₂ (TrInductiveHeader venv ctx.lparams) indTypes.toList headers)
    (htypes : ∀ header ∈ headers, header.toVConstant.WF venv) :
    (checkInductiveTypes numParams indTypes
      (fun stats => declareInductiveTypes stats numParams indTypes numNested isUnsafe) ctx).WF
      fun env' => ∃ venv', venv.addInductHeaders headers = some venv' ∧
        Aligned safety env'.constants venv' ∧ venv'.Ordered :=
  (checkInductiveTypes.refinesHeaders ctx numParams indTypes numNested isUnsafe
    haligned hsafety hheaders).mono fun _ ⟨venv', hadd, haligned'⟩ =>
      ⟨venv', hadd, haligned', VEnv.addInductHeaders.ordered hordered htypes hadd⟩

end Lean4Lean
