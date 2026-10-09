import Lean4Lean.Verify.InductiveRegistration
import Lean4Lean.Verify.RecursorRegistration
import Lean4Lean.Verify.RecursorInfoFrame

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

structure InductiveStats.SafeRunRegistration (stats : InductiveStats)
    (nparams : Nat) (types : Array InductiveType) (numNested : Nat)
    (original root : Context) (constructors env : Kernel.Environment) : Prop where
  registration : stats.SafeConstructorRegistration nparams types numNested original root constructors
  resultWF : env.constants.WF
  fromConstructors : ∀ name info, constructors.find? name = some info → env.find? name = some info

theorem InductiveStats.SafeRunRegistration.preservesOriginal {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hregistration : stats.SafeRunRegistration nparams types numNested original root constructors env) :
    ∀ name info, original.env.find? name = some info → env.find? name = some info :=
  fun name info hold => hregistration.fromConstructors name info
    (hregistration.registration.preservesOriginal name info hold)

theorem InductiveStats.SafeRunRegistration.headerMetadata {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hregistration : stats.SafeRunRegistration nparams types numNested original root constructors env) :
    stats.HeaderMetadata nparams types numNested false original.lparams env :=
  fun parent hparent => hregistration.fromConstructors _ _
    (hregistration.registration.resultHeaderMetadata parent hparent)

theorem InductiveStats.SafeRunRegistration.constructorMetadata {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hregistration : stats.SafeRunRegistration nparams types numNested original root constructors env) :
    stats.ConstructorMetadata original.lparams types false env := by
  intro parent hparent index ctor hctor
  obtain ⟨hfind, harity⟩ := hregistration.registration.constructorMetadata parent hparent index ctor hctor
  exact ⟨hregistration.fromConstructors _ _ hfind, harity⟩

theorem InductiveStats.SafeRunRegistration.declaredParameters {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hregistration : stats.SafeRunRegistration nparams types numNested original root constructors env) :
    DeclaredParameterMetadata nparams types env :=
  stats.declaredParameterMetadata nparams types numNested false original.lparams env
    hregistration.registration.traces.2.1 hregistration.headerMetadata hregistration.constructorMetadata

theorem run.safeRegistration (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunRegistration nparams types.toArray numNested ctx root constructors env := by
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
  apply mkRecInfos.frame
  intro infos current hframe
  apply Lean4Lean.AddInductive.bindWF
  intro lctx
  apply Lean4Lean.AddInductive.bindWF
  intro isK
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  refine (declareRecursors.preserves stats types.toArray elimLevel infos ctx.lparams lctx isK
    _ current (by simpa only [hframe.env] using hregistration.resultWF)).mono ?_
  rintro env ⟨hfinal, hkeep⟩
  refine ⟨stats, root, constructors, hregistration, hfinal, ?_⟩
  intro name info hold
  apply hkeep name info
  simpa only [hframe.env] using hold

theorem run.safePreserves (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      env.constants.WF ∧
        ∀ name info, ctx.env.find? name = some info → env.find? name = some info := by
  refine (run.safeRegistration nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hregistration⟩
  exact ⟨hregistration.resultWF, hregistration.preservesOriginal⟩

end Lean4Lean.AddInductive
