import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.ConstructorHeaders

namespace Lean4Lean
namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' :=
  by
    simp only [VInductDecl.WF] at hdecl
    obtain ⟨hheaders, hctors⟩ := hdecl
    unfold VEnv.addInduct at henv'
    obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp henv'
    have hheaders' := VEnv.addInductHeaders.ordered henv
      (fun header hmem => (hheaders header hmem).2) hheader
    exact VEnv.addConstructorHeaders.ordered hheaders'
      (fun ctor hmem => (hctors headers hheader ctor hmem).2) hconstructor
