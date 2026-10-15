import Lean4Lean.Verify.InductiveFrontendRestoration

namespace Lean4Lean

open Lean hiding Environment Exception
open private Lean.Kernel.Environment.add from Lean.Environment

namespace NativeInductive

def insertInfos (constants : ConstMap) : List ConstantInfo → ConstMap
  | [] => constants
  | info :: infos => (insertInfos constants infos).insert info.name info

theorem FreshRegistrationTrace.constants_eq
    (trace : FreshRegistrationTrace allowed original result) :
    ∃ infos, result.constants = insertInfos original.constants infos := by
  induction trace with
  | refl => exact ⟨[], rfl⟩
  | @step current previous info record fresh ih =>
    rcases ih with ⟨infos, ih⟩
    refine ⟨info :: infos, ?_⟩
    simp only [Kernel.Environment.add_constants, insertInfos]
    rw [ih]

end NativeInductive

end Lean4Lean
