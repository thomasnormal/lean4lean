import Lean4Lean.Verify.InductiveNativeAlignment

namespace Lean4Lean.Tests.InductiveNativeAlignment

open Lean Lean4Lean Lean4Lean.NativeInductive

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned .safe constants env) :
    Aligned .safe resultConstants result :=
  evidence.aligned haligned

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (haligned : Aligned .unsafe constants env) :
    Aligned .unsafe resultConstants result :=
  evidence.aligned haligned

end Lean4Lean.Tests.InductiveNativeAlignment
