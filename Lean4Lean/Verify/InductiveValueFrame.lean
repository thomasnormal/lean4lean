import Lean4Lean.Verify.ConstructorHeaders
import Lean4Lean.Verify.InductiveFrontendRestoration

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel
open private Lean4Lean.registerRestored from Lean4Lean.Verify.InductiveFrontendRestoration

namespace AddInductive
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

theorem run.preservesValues (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF (NativeValueFrame ctx.env) := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply checkInductiveTypes.frame
  intro stats current hframe
  refine (declareInductiveTypes.preservesValues current stats nparams types.toArray numNested
    _ (by simpa only [hframe.env] using hwf)).bind ?_
  intro headers hheaders
  refine (show (checkConstructors types.toArray stats _
    { current with env := headers }).WF (fun _ => True) from fun _ _ => trivial).bind ?_
  intro _ _
  refine (declareConstructors.preservesValues { current with env := headers }
    stats types.toArray _ hheaders.map_wf).bind ?_
  intro constructors hconstructors
  apply Lean4Lean.AddInductive.bindWF
  intro elimLevel
  apply mkRecInfos.frame
  intro infos source hsource
  apply Lean4Lean.AddInductive.bindWF
  intro lctx
  apply Lean4Lean.AddInductive.bindWF
  intro isK
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  refine (declareRecursors.preservesValues stats types.toArray elimLevel infos ctx.lparams
    lctx isK _ source (by simpa only [hsource.env] using hconstructors.map_wf)).mono ?_
  intro result hrecursors
  have hrecursors : NativeValueFrame constructors result := by
    simpa only [hsource.env] using hrecursors
  simpa only [hframe.env] using hheaders.trans (hconstructors.trans hrecursors)

end AddInductive

theorem FreshRegistrationTrace.preservesValues {allowed : ConstantInfo → Prop}
    {original result : Environment} (trace : FreshRegistrationTrace allowed original result)
    (hwf : original.constants.WF) (hvalues : ∀ info, allowed info → info.value? = none) :
    NativeValueFrame original result := by
  obtain ⟨hresult, hkeep⟩ := trace.preserves hwf
  refine ⟨hresult, ?_, ?_⟩
  · intro name info hlookup
    simpa only [Kernel.Environment.find?, hresult.find?'_eq_find?] using
      hkeep name info (by simpa only [Kernel.Environment.find?, hwf.find?'_eq_find?] using hlookup)
  · intro name info value hlookup hvalue
    have hlookup : result.find? name = some info := by
      simpa only [Kernel.Environment.find?, hresult.find?'_eq_find?] using hlookup
    rcases trace.lookup hwf name info hlookup with hold | hrecord
    · simpa only [Kernel.Environment.find?, hwf.find?'_eq_find?] using hold
    · rw [hvalues info hrecord] at hvalue
      cases hvalue

theorem RestoredInductiveRecord.value?_eq_none
    {preprocessing : ElimNestedInductive.Result} {staged : Environment}
    {allIndNames : List Name} {recNameMap : NameMap Name} {info : ConstantInfo}
    (record : RestoredInductiveRecord preprocessing staged allIndNames recNameMap info) :
    info.value? = none := by
  cases record <;> rfl

theorem Environment.addInductive.safePreservesValues (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (allowPrimitive : Bool) (fuel : FuelConfig)
    (hwf : env.constants.WF) :
    (Environment.addInductive env lparams nparams types false allowPrimitive fuel).WF
      (NativeValueFrame env) := by
  unfold Environment.addInductive
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro _ _
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro preprocessing _
  dsimp only
  refine (AddInductive.run.preservesValues nparams preprocessing.types preprocessing.aux2nested.size
    (inductiveScopeContext env lparams allowPrimitive fuel) hwf).bind ?_
  intro staged hstaged
  split
  · exact .pure hstaged
  · have hrestored : ((·.2) <$>
        restoreInductiveEnvironment preprocessing staged types lparams allowPrimitive fuel env).WF
          (NativeValueFrame env) :=
      (restoreInductiveEnvironment.trace preprocessing staged types lparams allowPrimitive fuel env).map
        fun _ htrace => htrace.preservesValues hwf
          (fun _ hrecord => hrecord.value?_eq_none)
    dsimp only [restoreInductiveEnvironment, restoreInductiveDatatype, restoreInductiveConstructor,
      restoreInductiveRecursor, Lean4Lean.registerRestored, StateT.run] at hrestored
    simpa only [StateT.run, ConstantInfo.name, ConstantInfo.toConstantVal,
      List.mapM_pure, pure_bind, panicWithPosWithDecl, panic, panicCore,
      bind_assoc, Bool.false_eq_true, if_false] using hrestored

theorem addDecl.safeInductivePreservesValues (env : Environment) (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) (check : Bool) (fuel : FuelConfig)
    (hwf : env.constants.WF) :
    (addDecl env (.inductDecl lparams nparams types false) check fuel).WF
      (NativeValueFrame env) := by
  unfold addDecl
  refine Except.WF.bind (Q := fun _ => True) (fun _ _ => trivial) ?_
  intro allowPrimitive _
  exact Environment.addInductive.safePreservesValues env lparams nparams types allowPrimitive fuel hwf

end Lean4Lean
