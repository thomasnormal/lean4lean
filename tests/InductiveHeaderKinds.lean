import Lean4Lean.Verify.InductiveHeaderKinds

namespace InductiveHeaderKindsTest
open Lean hiding Environment Exception
open Lean4Lean Lean4Lean.AddInductive

example (kind : VEnv.SortArity environment universes context count type)
    (environmentWF : environment.WF)
    (contextWF : OnCtx context (environment.IsType universes)) :
    environment.IsType universes context type :=
  kind.isType environmentWF contextWF

example (types : Array InductiveType)
    (next : InductiveStats → M resultType) (checker : TypeChecker.VContext) (reader : Context)
    (aligned : HeaderCheckerAligned checker reader)
    (initialWF : ({} : TypeChecker.VState).WF checker)
    (reserved : ElimNestedInductive.ContextReserved reader.lctx reader.ngen)
    (different : ({} : TypeChecker.VState).ngen.namePrefix ≠ reader.ngen.namePrefix)
    (constants : CanonicalAnnotationConstants checker.venv)
    (definitions : CanonicalAnnotationDefinitions checker.venv) (nonempty : 0 < types.size) :
    (checkInductiveTypes 0 types next reader).WF fun _ => ∃ semantic count,
      checker.TrExprS types[0]!.type semantic ∧
      checker.venv.SortArity checker.lparams.length checker.vlctx.toCtx count semantic :=
  checkInductiveTypes.firstHeaderKind types next checker reader aligned initialWF reserved different
    constants definitions nonempty

end InductiveHeaderKindsTest
