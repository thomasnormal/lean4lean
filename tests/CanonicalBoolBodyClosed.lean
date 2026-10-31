import Lean4Lean.Verify.CanonicalBoolPassSupport

namespace CanonicalBoolBodyClosedTest
open Lean hiding Environment Exception
open Lean4Lean
open Lean4Lean.AddInductive

example {finalInfos : Array RecInfo} {info : RecInfo} {major motive : FVarId}
    (finalInfosEq : finalInfos = #[info])
    (finalIndicesEq : info.indices = #[])
    (finalMajorEq : info.major = .fvar major)
    (finalMotiveEq : info.motive = .fvar motive) :
    (recursorTypeBody finalInfos 0).looseBVarRange' = 0 := by
  simp [Expr.looseBVarRange', Lean.mkAppN, recursorTypeBody, finalInfosEq,
    finalIndicesEq, finalMajorEq, finalMotiveEq]

end CanonicalBoolBodyClosedTest
