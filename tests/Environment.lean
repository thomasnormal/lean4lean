import Lean4Lean.Environment

-- Run with: lake env lean tests/Environment.lean
open Lean Lean4Lean

run_meta
  let base : List Declaration := [
    .axiomDecl { name := `P, levelParams := [], type := .sort .zero, isUnsafe := false },
    .axiomDecl { name := `p, levelParams := [], type := .const `P [], isUnsafe := false },
    .axiomDecl { name := `Q, levelParams := [], type := .sort .zero, isUnsafe := false }]
  let check (decls : List Declaration) := decls.foldlM (fun env decl => addDeclVerified env decl)
    (Kernel.Environment.empty `FrontendTest)
  let good := base ++ [.thmDecl {
    name := `valid, levelParams := [], type := .const `P [], value := .const `p [] }]
  unless (check good).isOk do
    throwError "rejected a valid axiom/theorem pipeline from the empty environment"
  let bad := base ++ [.thmDecl {
    name := `invalid, levelParams := [], type := .const `Q [], value := .const `p [] }]
  if (check bad).isOk then
    throwError "accepted a proof of P as a proof of unrelated Q"
  let induct : Declaration := .inductDecl [] 0 [{
    name := `Fresh, type := .sort (.succ .zero), ctors := [{ name := `Fresh.mk, type := .const `Fresh [] }] }]
    false
  if (check [induct]).isOk then
    throwError "the restricted frontend accepted an inductive declaration"
