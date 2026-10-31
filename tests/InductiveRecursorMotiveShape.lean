import Lean4Lean.Verify.InductiveRecursorApplicationNative

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

example
    {stats : InductiveStats} {types : Array InductiveType} {elimLevel : Level}
    {parent : Nat} {original current : Context} {info : RecInfo}
    (source : RecursorInfoIndexSource stats types elimLevel parent original info current)
    (scope : current.lctx.BindingScope)
    {index : Nat} {identifier : FVarId} {name : Name} {domain : Expr}
    {binder : BinderInfo}
    (lookup : current.lctx.find? info.motive.fvarId! =
      some (.cdecl index identifier name domain binder .default)) :
    domain = current.lctx.mkForall info.indices
      (current.lctx.mkForall #[info.major] (.sort elimLevel)) :=
  source.motiveDomainShape scope lookup

end Lean4Lean.AddInductive
