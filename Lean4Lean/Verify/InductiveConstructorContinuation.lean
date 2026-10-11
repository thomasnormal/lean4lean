import Lean4Lean.Verify.InductiveConstructorTransport

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem HeaderAxiomContinuation.acceptedConstructors
    (stage : HeaderAxiomContinuation root original nparams types stats reader actual)
    (isUnsafe : Bool) (fresh : ConstructorsFresh actual types)
    (constructors : NativeConstructorParentClosure actual)
    (recursors : ∀ name information, actual.find? name = some (.recInfo information) →
      ∃ header, stage.shadow.find? information.getMajorInduct = some (.inductInfo header))
    (quotInit : actual.quotInit = stage.shadow.quotInit) :
    (checkConstructors types stats isUnsafe { reader with env := actual }).WF fun _ =>
      checkConstructors types stats isUnsafe { reader with env := stage.shadow } = .ok () ∧
        stats.AcceptedConstructorTraces types isUnsafe { reader with env := stage.shadow } := by
  intro result accepted
  cases result
  have metadata := NativeRecursiveHeaderFrame.beforeConstructors stage.lookups stage.constructorHeaders
    fresh constructors recursors quotInit
  have transported := checkConstructors.headerAxiomTransport types stats isUnsafe
    { reader with env := actual } stage.shadow metadata () accepted
  exact ⟨transported, checkConstructors.acceptedTraces types stats isUnsafe
    { reader with env := stage.shadow } () transported⟩

end Lean4Lean.AddInductive
