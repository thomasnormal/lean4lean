import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Theory.Typing.QuotInjectivity
import Lean.Util.CollectAxioms

open Lean Lean4Lean

namespace ProofValueAuditTest

private def definitionValue : Nat := 7
private opaque opaqueValue : Nat := 11
private theorem theoremValue : True := True.intro

private def readValue (name : Name) : MetaM Expr := do
  let information ← getConstInfo name
  let some value := information.value? (allowOpaque := true)
    | throwError "proof access: missing definition/theorem/opaque value {name}"
  return value

/-- Inspect types and proof bodies, including opaque declarations. -/
private def dependencies (roots : Array Name) (forbidden : List Name) : MetaM NameSet := do
  let environment ← getEnv
  let mut pending := roots
  let mut visited : NameSet := {}
  for _ in [:1000000] do
    if pending.isEmpty then break
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    if forbidden.contains name then throwError "proof access: forbidden dependency {name}"
    visited := visited.insert name
    let some information := environment.find? name
      | throwError "proof access: missing dependency {name}"
    pending := pending ++ information.type.getUsedConstants
    if let some value := information.value? (allowOpaque := true) then
      pending := pending ++ value.getUsedConstants
    else
      match information with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        throwError "proof access: silently omitted value {name}"
      | _ => pure ()
    if let .inductInfo inductiveInfo := information then
      pending := pending ++ inductiveInfo.ctors.toArray
  unless pending.isEmpty do throwError "proof access: dependency traversal exceeded its bound"
  return visited

private def expectForbidden (root forbidden : Name) : MetaM Unit := do
  let mut rejected := false
  try
    let _ ← dependencies #[root] [forbidden]
  catch exception =>
    let actual ← exception.toMessageData.toString
    let expected ← (m!"proof access: forbidden dependency {forbidden}").toString
    unless actual == expected do throw exception
    rejected := true
  unless rejected do throwError "proof access: theorem proof body was silently skipped"

run_meta
  for name in [``definitionValue, ``opaqueValue, ``theoremValue] do
    let value ← readValue name
    if value.hasSorry then throwError "proof access: local control has a direct admission"
    let axioms ← collectAxioms name
    unless axioms.isEmpty do throwError "proof access: local control gained an axiom {name}"
  let information ← getConstInfo ``theoremValue
  unless information matches .thmInfo _ do throwError "proof access: theorem control changed kind"
  let information ← getConstInfo ``opaqueValue
  unless information matches .opaqueInfo _ do throwError "proof access: opaque control changed kind"
  let admitted ← readValue ``TrProj.instL
  unless admitted.hasSorry do throwError "proof access: inherited admitted proof control changed"
  let reached ← dependencies #[``TrExprS.instL]
    [``VEnv.NormalEq.parRed, ``VEnv.NormalEq.parRedS, ``VEnv.IsDefEq.church_rosser,
      ``VEnv.IsDefEqU.quot_inj, ``VEnv.IsDefEqU.weakN_iff]
  unless reached.contains ``TrProj.instL && reached.contains ``sorryAx do
    throwError "proof access: proof-body admission path was not traversed"
  expectForbidden ``TrExprS.instL ``TrProj.instL
  expectForbidden ``TrExprS.instL ``sorryAx
  let opaqueReached ← dependencies #[``opaqueValue] []
  unless opaqueReached.contains ``Nat do throwError "proof access: opaque control traversal is empty"
  logInfo "proof access: definition/theorem/opaque values inspected; inherited projection admission reached through a theorem body; both forbidden-dependency controls rejected; known-false strengthening/confluence roots excluded"

end ProofValueAuditTest
