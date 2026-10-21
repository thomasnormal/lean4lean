import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.ConstructorHeaders

namespace Lean4Lean
namespace VEnv

theorem addInduct.exists
    (headersFresh : ∀ header ∈ decl.types, env.constants header.name = none)
    (headersDistinct : (decl.types.map (·.name)).Nodup)
    (constructorsDistinct : (decl.constructorHeaders.map VConstVal.name).Nodup)
    (constructorsFresh : ∀ headerEnv, env.addInductHeaders decl.types = some headerEnv →
      ∀ ctor ∈ decl.constructorHeaders, headerEnv.constants ctor.name = none) :
    ∃ env', addInduct env decl = some env' := by
  obtain ⟨headerEnv, hheader⟩ := addInductHeaders.exists headersFresh headersDistinct
  obtain ⟨env', hconstructor⟩ := addConstructorHeaders.exists
    (constructorsFresh headerEnv hheader) constructorsDistinct
  refine ⟨env', ?_⟩
  simpa [VEnv.addInduct, hheader] using hconstructor

theorem addInduct.le
    (hadd : addInduct env decl = some env') : env ≤ env' := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  exact (addInductHeaders.le hheader).trans (addConstructorHeaders.le hconstructor)

theorem addInduct.header
    (header : VInductiveType) (hadd : addInduct env decl = some env')
    (hmem : header ∈ decl.types) :
    env'.constants header.name = some header.toVConstant := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  exact (addConstructorHeaders.le hconstructor).constants
    (addInductHeaders.constants hheader hmem)

theorem addInduct.constructor
    (ctor : VConstVal) (hadd : addInduct env decl = some env')
    (hmem : ctor ∈ decl.constructorHeaders) :
    env'.constants ctor.name = some ctor.toVConstant := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  exact addConstructorHeaders.constants hconstructor hmem

theorem addInduct.headerFresh
    (header : VInductiveType) (hadd : addInduct env decl = some env')
    (hmem : header ∈ decl.types) :
    env.constants header.name = none := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  exact addInductHeaders.fresh hheader hmem

theorem addInduct.constructorFresh
    (ctor : VConstVal) (hadd : addInduct env decl = some env')
    (hmem : ctor ∈ decl.constructorHeaders) :
    env.constants ctor.name = none := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  cases found : env.constants ctor.name with
  | none => rfl
  | some value =>
    have found' := (addInductHeaders.le hheader).constants found
    rw [addConstructorHeaders.fresh hconstructor hmem] at found'
    cases found'

theorem addInduct.constants_eq
    (hadd : addInduct env decl = some env')
    (notHeader : ∀ header ∈ decl.types, header.name ≠ name)
    (notConstructor : ∀ ctor ∈ decl.constructorHeaders, ctor.name ≠ name) :
    env'.constants name = env.constants name := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  rw [addConstructorHeaders.otherConstants hconstructor]
  · exact addInductHeaders.otherConstants hheader notHeader
  · intro ctor hmem
    exact notConstructor ctor hmem

theorem addInduct.defeqs_eq
    (hadd : addInduct env decl = some env') : env'.defeqs = env.defeqs := by
  unfold VEnv.addInduct at hadd
  obtain ⟨headers, hheader, hconstructor⟩ := Option.bind_eq_some_iff.mp hadd
  exact (addConstructorHeaders.defeqs_eq hconstructor).trans
    (addInductHeaders.defeqs_eq hheader)

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

theorem addInductWithRecursors.exists
    (headersFresh : ∀ header ∈ decl.types, env.constants header.name = none)
    (headersDistinct : (decl.types.map (·.name)).Nodup)
    (constructorsDistinct : (decl.constructorHeaders.map VConstVal.name).Nodup)
    (constructorsFresh : ∀ headerEnv, env.addInductHeaders decl.types = some headerEnv →
      ∀ ctor ∈ decl.constructorHeaders, headerEnv.constants ctor.name = none)
    (recursorsDistinct : (recursors.map VConstVal.name).Nodup)
    (recursorsFresh : ∀ inductEnv, env.addInduct decl = some inductEnv →
      ∀ recursor ∈ recursors, inductEnv.constants recursor.name = none) :
    ∃ env', addInductWithRecursors env decl recursors = some env' := by
  obtain ⟨inductEnv, hinduct⟩ := addInduct.exists headersFresh headersDistinct
    constructorsDistinct constructorsFresh
  obtain ⟨env', hrecursors⟩ := addConstructorHeaders.exists
    (recursorsFresh inductEnv hinduct) recursorsDistinct
  refine ⟨env', ?_⟩
  simpa [VEnv.addInductWithRecursors, hinduct] using hrecursors

theorem addInductWithRecursors.le
    (hadd : addInductWithRecursors env decl recursors = some env') : env ≤ env' := by
  unfold VEnv.addInductWithRecursors at hadd
  obtain ⟨inductEnv, hinduct, hrecursors⟩ := Option.bind_eq_some_iff.mp hadd
  exact (addInduct.le hinduct).trans (addConstructorHeaders.le hrecursors)

theorem addInductWithRecursors.recursor
    (recursor : VConstVal) (hadd : addInductWithRecursors env decl recursors = some env')
    (hmem : recursor ∈ recursors) :
    env'.constants recursor.name = some recursor.toVConstant := by
  unfold VEnv.addInductWithRecursors at hadd
  obtain ⟨inductEnv, hinduct, hrecursors⟩ := Option.bind_eq_some_iff.mp hadd
  exact addConstructorHeaders.constants hrecursors hmem

theorem addInductWithRecursors.recursorFresh
    (recursor : VConstVal) (hadd : addInductWithRecursors env decl recursors = some env')
    (hmem : recursor ∈ recursors) :
    env.constants recursor.name = none := by
  unfold VEnv.addInductWithRecursors at hadd
  obtain ⟨inductEnv, hinduct, hrecursors⟩ := Option.bind_eq_some_iff.mp hadd
  cases found : env.constants recursor.name with
  | none => rfl
  | some value =>
    have found' := (addInduct.le hinduct).constants found
    rw [addConstructorHeaders.fresh hrecursors hmem] at found'
    cases found'

theorem addInductWithRecursors.defeqs_eq
    (hadd : addInductWithRecursors env decl recursors = some env') :
    env'.defeqs = env.defeqs := by
  unfold VEnv.addInductWithRecursors at hadd
  obtain ⟨inductEnv, hinduct, hrecursors⟩ := Option.bind_eq_some_iff.mp hadd
  exact (addConstructorHeaders.defeqs_eq hrecursors).trans (addInduct.defeqs_eq hinduct)

theorem addInductWithRecursors.constants_eq
    (hadd : addInductWithRecursors env decl recursors = some env')
    (notHeader : ∀ header ∈ decl.types, header.name ≠ name)
    (notConstructor : ∀ ctor ∈ decl.constructorHeaders, ctor.name ≠ name)
    (notRecursor : ∀ recursor ∈ recursors, recursor.name ≠ name) :
    env'.constants name = env.constants name := by
  unfold VEnv.addInductWithRecursors at hadd
  obtain ⟨inductEnv, hinduct, hrecursors⟩ := Option.bind_eq_some_iff.mp hadd
  rw [addConstructorHeaders.otherConstants hrecursors]
  · exact addInduct.constants_eq hinduct notHeader notConstructor
  · exact notRecursor

theorem addInductWithRecursors_WF (henv : Ordered env) (hdecl : decl.WF env)
    (hrecursors : ∀ inductEnv, addInduct env decl = some inductEnv →
      ∀ recursor ∈ recursors, recursor.WF inductEnv)
    (henv' : addInductWithRecursors env decl recursors = some env') : Ordered env' := by
  unfold VEnv.addInductWithRecursors at henv'
  obtain ⟨inductEnv, hinduct, hconstructor⟩ := Option.bind_eq_some_iff.mp henv'
  have hinductWF := addInduct_WF henv hdecl hinduct
  exact addConstructorHeaders.ordered hinductWF
    (fun recursor hmem => hrecursors inductEnv hinduct recursor hmem) hconstructor
