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
    (haligned : Aligned .safe constants env) :
    Aligned .safe evidence.constructorConstants evidence.constructorEnv :=
  haligned.addInductEvidence (evidence.to_addInductEvidence haligned.map_wf)

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (safety : DefinitionSafety) (hconstants : constants.WF) :
    AddInductEvidence safety constants env decl evidence.constructorConstants
      evidence.constructorEnv :=
  evidence.to_addInductEvidence_at safety hconstants

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
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    AddInductWithRecursorsEvidence .safe constants env decl
      evidence.constructorConstants evidence.constructorEnv
      (evidence.recursors.map (·.info)) (evidence.recursors.map (·.model))
      resultConstants result :=
  evidence.to_addInductWithRecursorsEvidence hconstants hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result :=
  (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).to_addInductWithRecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    env ≤ result :=
  (evidence.to_addInductWithRecursorsEvidence hconstants hrecursors).le

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) : result.WF :=
  evidence.resultWF henv hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : evidence.constructorEnv.WF)
    (hsource : ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF evidence.constructorEnv :=
  evidence.recursorWF_of_sourceTypehood henv hsource

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) :
    ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic :=
  evidence.sourceTypehood_of_recursorWF hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : evidence.constructorEnv.WF) :
    (∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) ↔
    (∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF evidence.constructorEnv) :=
  evidence.sourceTypehood_iff_recursorWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors, entry.model.toVConstant.WF
      evidence.constructorEnv) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result ∧
      result.WF :=
  evidence.registrationWF henv hrecursors

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF)
    (hsource : ∀ entry ∈ evidence.recursors, ∃ semantic,
      TrExprS evidence.constructorEnv entry.info.levelParams [] entry.info.type semantic ∧
      evidence.constructorEnv.IsType entry.info.levelParams.length [] semantic) :
    env.addInductWithRecursors decl (evidence.recursors.map (·.model)) = some result ∧
      result.WF :=
  evidence.registrationWF_of_sourceTypehood henv hsource

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result) :
    VDecl.WF env (.induct decl) evidence.constructorEnv :=
  evidence.inductiveDeclWF

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (henv : env.WF) :
    evidence.constructorEnv.WF :=
  evidence.inductiveHistoryWF henv

example {constants resultConstants : ConstMap} {env result : VEnv} {decl : VInductDecl}
    {Q : Bool} (history : TrEnvInductive .safe constants Q env)
    (evidence : RegistrationEvidence constants env decl resultConstants result)
    (hconstants : constants.WF)
    (hrecursors : ∀ entry ∈ evidence.recursors,
      entry.model.toVConstant.WF evidence.constructorEnv) :
    TrEnvInductive .safe resultConstants Q result :=
  evidence.to_trEnvInductive history hconstants hrecursors

example {env env' : VEnv} {declaration : VDecl}
    (henv : env.WF) (hdecl : VDecl.WF env declaration env') : env'.WF :=
  VEnv.WF.decl henv hdecl

end Lean4Lean.Tests.InductiveNativeAlignment
