import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.Typing.Basic

namespace Lean4Lean

def VEnv.addInductHeaders (env : VEnv) : List VInductiveType → Option VEnv
  | [] => some env
  | header :: headers => do
    let env ← env.addConst header.name header.toVConstant
    env.addInductHeaders headers

def VInductDecl.constructorHeaders (declaration : VInductDecl) : List VConstVal :=
  declaration.types.flatMap (fun header => header.ctors)

def VEnv.addConstructorHeaders (env : VEnv) : List VConstVal → Option VEnv
  | [] => some env
  | ctor :: ctors => do
    let env ← env.addConst ctor.name ctor.toVConstant
    env.addConstructorHeaders ctors

def VInductDecl.HeadersWF (env : VEnv) (decl : VInductDecl) : Prop :=
  ∀ header ∈ decl.types, header.uvars = decl.uvars ∧ header.toVConstant.WF env

def VInductDecl.WF (env : VEnv) (decl : VInductDecl) : Prop :=
  decl.HeadersWF env ∧
    ∀ env', env.addInductHeaders decl.types = some env' →
      ∀ ctor ∈ decl.constructorHeaders,
        ctor.uvars = decl.uvars ∧ ctor.WF env'

def VEnv.addInduct (env : VEnv) (decl : VInductDecl) : Option VEnv :=
  env.addInductHeaders decl.types >>= fun env =>
    env.addConstructorHeaders decl.constructorHeaders
