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

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.headerEnv.WF :=
  evidence.headerEnvWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) : evidence.constructorEnv.WF :=
  evidence.constructorEnvWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) : result.WF :=
  evidence.resultWF henv hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result ∧
      result.WF :=
  evidence.registrationWF henv hrecursors

end Lean4Lean.Tests.InductiveNativeAlignment
