import Lean4Lean.Verify.PrimitiveInductivePreprocessing
import Lean4Lean.Verify.ConstructorHeaders

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

/- The canonical primitive receipts have two executable boundaries: the full frontend
   scope and the staged header/constructor checker.  Keep them together so a consumer
   can use the source preprocessing receipt and the semantic registration receipt from
   one theorem, without hiding either executable obligation. -/
theorem addDecl.safeCanonicalBoolRegistration
    (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (hmap : env.constants.WF) (venv : VEnv)
    (hchecker : CheckerEnv .safe (inductiveScopeContext env [] true fuel).env venv) :
    (addDecl env (.inductDecl [] 0 [canonicalBoolType] false) check fuel).WF (fun result =>
      ∃ allowPrimitive,
        NonNestedInductiveScope env [] 0 [canonicalBoolType] allowPrimitive fuel result) ∧
    (AddInductive.checkInductiveTypes 0 [canonicalBoolType].toArray (fun stats => do
      AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0
        [canonicalBoolType].toArray 0 false) do
        AddInductive.checkConstructors [canonicalBoolType].toArray stats false
        AddInductive.declareConstructors stats [canonicalBoolType].toArray false)
      (inductiveScopeContext env [] true fuel)).WF (fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧ decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv [] 0 [canonicalBoolType] decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧ ctorEnv.WF ∧ VDecl.WF venv (.induct decl) ctorEnv ∧
        CheckerEnv .safe env' ctorEnv) := by
  refine ⟨addDecl.safeCanonicalBool env check fuel hmap, ?_⟩
  apply AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerWithModelAndVDeclWF
    (inductiveScopeContext env [] true fuel) 0 [canonicalBoolType] 0 false hchecker
  apply (Environment.checkPrimitiveInductive.eq_true_iff env [] 0 [canonicalBoolType] false).mpr
  simpa only [canonicalBoolType] using
    (Environment.PrimitiveInductiveDecl.bool :
      Environment.PrimitiveInductiveDecl [] 0 [canonicalBoolType] false)

theorem addDecl.safeCanonicalNatRegistration
    (env : Kernel.Environment) (check : Bool) (fuel : FuelConfig)
    (binderName : Name) (binderInfo : BinderInfo) (hmap : env.constants.WF) (venv : VEnv)
    (hchecker : CheckerEnv .safe (inductiveScopeContext env [] true fuel).env venv) :
    (addDecl env (.inductDecl [] 0 [canonicalNatType binderName binderInfo] false) check fuel).WF
      (fun result => ∃ allowPrimitive,
        NonNestedInductiveScope env [] 0 [canonicalNatType binderName binderInfo]
          allowPrimitive fuel result) ∧
    (AddInductive.checkInductiveTypes 0 [canonicalNatType binderName binderInfo].toArray
      (fun stats => do
        AddInductive.withEnv (← AddInductive.declareInductiveTypes stats 0
          [canonicalNatType binderName binderInfo].toArray 0 false) do
          AddInductive.checkConstructors [canonicalNatType binderName binderInfo].toArray stats false
          AddInductive.declareConstructors stats [canonicalNatType binderName binderInfo].toArray false)
      (inductiveScopeContext env [] true fuel)).WF (fun env' =>
      ∃ decl headerEnv ctorEnv, (decl = boolInductDecl ∨ decl = natInductDecl) ∧
        decl.HeadersWF venv ∧ decl.WF venv ∧
        venv.addInductHeaders decl.types = some headerEnv ∧ headerEnv.WF ∧
        TrInductDecl venv headerEnv [] 0 [canonicalNatType binderName binderInfo] decl ∧
        headerEnv.addConstructorHeaders (decl.types.flatMap (fun type => type.ctors)) =
          some ctorEnv ∧ ctorEnv.WF ∧ VDecl.WF venv (.induct decl) ctorEnv ∧
        CheckerEnv .safe env' ctorEnv) := by
  refine ⟨addDecl.safeCanonicalNat env check fuel binderName binderInfo hmap, ?_⟩
  apply AddInductive.checkInductiveTypes.refinesPrimitiveHeaderConstructorCheckerWithModelAndVDeclWF
    (inductiveScopeContext env [] true fuel) 0 [canonicalNatType binderName binderInfo] 0 false hchecker
  apply (Environment.checkPrimitiveInductive.eq_true_iff env [] 0
    [canonicalNatType binderName binderInfo] false).mpr
  simpa only [canonicalNatType] using
    (Environment.PrimitiveInductiveDecl.nat binderName binderInfo :
      Environment.PrimitiveInductiveDecl [] 0 [canonicalNatType binderName binderInfo] false)

end Lean4Lean
