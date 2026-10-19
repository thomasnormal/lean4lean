import Lean4Lean.Theory.Typing.HeadInjectivity.Model.ClassApplication
import Lean.Util.CollectAxioms

namespace ModelClassesTest
open Lean Lean4Lean Lean4Lean.VEnv Lean4Lean.VEnv.Model

def one : VLevel := .succ .zero
def altZero : VLevel := .max .zero .zero
def altOne : VLevel := .max .zero one

theorem zeroEq : VLevel.zero ≈ altZero :=
  VLevel.equiv_def.mpr fun _ => by simp [altZero, VLevel.eval]

theorem oneEq : one ≈ altOne :=
  VLevel.equiv_def.mpr fun _ => by simp [altOne, one, VLevel.eval]

theorem zeroSyntax : altZero ≠ VLevel.zero := by intro h; cases h
theorem oneSyntax : altOne ≠ one := by intro h; cases h

theorem sortEquality : VEnv.empty.IsDefEq 0 []
    (.sort .zero) (.sort altZero) (.sort one) :=
  .sortDF (by trivial) (by trivial) zeroEq

-- The second link has a syntactically different sort from the first.
theorem heterogeneousChain : VEnv.empty.TypeChain 0 [] (.sort .zero) (.sort .zero) := by
  have second : VEnv.empty.IsDefEq 0 [] (.sort altZero) (.sort .zero) (.sort altOne) :=
    .defeqDF (.sortDF (by trivial) (by trivial) oneEq) sortEquality.symm
  exact (TypeChain.single sortEquality).tail second

theorem collapsedLevelMember : VEnv.empty.IsDefEq 0 []
    (.sort .zero) (.sort altZero) (.sort altOne) := by
  have member : ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] (.sort altOne))
      (.sort .zero) (.sort altZero) := .of_lvEq (.sort (by trivial) (by trivial) zeroEq)
  have typeMember : TyCls VEnv.empty 0 [] (.sort altOne) (.sort one) :=
    .inr (.single (.inr (.inl (.sort (by trivial) (by trivial) oneEq.symm))))
  exact ElCls.collapse .empty (by trivial) (HasType.sort (by trivial)) typeMember member

def idTerm : VExpr := .lam (.sort one) (.bvar 0)
def idType : VExpr := .forallE (.sort one) (.sort one)

theorem idTyped : VEnv.empty.HasType 0 [] idTerm idType :=
  .lamDF (HasType.sort (by trivial)) (.bvar .zero)

def argClass : VExpr → Prop :=
  ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 [] (.sort one)) (.sort .zero)

theorem argClassTyped : TypedElCls VEnv.empty 0 []
    (TyCls VEnv.empty 0 [] (.sort one)) argClass :=
  .of_hasType (HasType.sort (by trivial))

theorem otherMember : argClass (.sort altZero) :=
  .mem_of_defeq sortEquality

-- Beta uses a non-anchor member of the argument class.
theorem betaAtOtherMember :
    appCls VEnv.empty 0 [] (vcls VEnv.empty 0 [] VExpr.Subst.id idTerm idType)
      argClass (TyCls VEnv.empty 0 []
        ((VExpr.sort one).subst (VExpr.Subst.id.cons (.sort altZero)))) =
    vcls VEnv.empty 0 [] (VExpr.Subst.id.cons (.sort altZero))
      (.bvar 0) (.sort one) := by
  exact vcls_beta .empty (by trivial) (show Ctx.SubstEq VEnv.empty 0 [] VExpr.Subst.id VExpr.Subst.id [] from .nil)
    (HasType.sort (by trivial)) (.bvar .zero) argClassTyped otherMember

theorem actualApplication :
    vcls VEnv.empty 0 [] VExpr.Subst.id (.app idTerm (.sort .zero))
      ((VExpr.sort one).inst (.sort .zero)) =
    appCls VEnv.empty 0 [] (vcls VEnv.empty 0 [] VExpr.Subst.id idTerm idType)
      (ElCls VEnv.empty 0 [] (TyCls VEnv.empty 0 []
        ((VExpr.sort one).subst VExpr.Subst.id)) ((VExpr.sort .zero).subst VExpr.Subst.id))
      (TyCls VEnv.empty 0 []
        ((VExpr.sort one).subst (VExpr.Subst.id.cons ((VExpr.sort .zero).subst VExpr.Subst.id)))) :=
  vcls_app .empty (by trivial) .nil idTyped (HasType.sort (by trivial))

-- The two anchors are actually different expressions related by sortDF.
def leftAnchor : VExpr.Subst := VExpr.Subst.id.cons (.sort .zero)
def rightAnchor : VExpr.Subst := VExpr.Subst.id.cons (.sort altZero)

theorem relatedAnchors : Ctx.SubstEq VEnv.empty 0 [] leftAnchor rightAnchor [.sort one] :=
  .cons .nil (HasType.sort (by trivial)) sortEquality

theorem distinctAnchors : leftAnchor 0 ≠ rightAnchor 0 := by
  intro h
  have : VLevel.zero = altZero := VExpr.sort.inj h
  exact zeroSyntax this.symm

theorem dependentIdentityTyped : VEnv.empty.HasType 0 [.sort one]
    (.lam (.bvar 0) (.bvar 0)) (.forallE (.bvar 0) (.bvar 1)) :=
  .lamDF (.bvar .zero) (.bvar .zero)

theorem relatedAnchorClasses :
    vcls VEnv.empty 0 [] leftAnchor (.lam (.bvar 0) (.bvar 0))
      (.forallE (.bvar 0) (.bvar 1)) =
    vcls VEnv.empty 0 [] rightAnchor (.lam (.bvar 0) (.bvar 0))
      (.forallE (.bvar 0) (.bvar 1)) :=
  vcls_substEq .empty (by trivial) relatedAnchors dependentIdentityTyped

theorem relatedAnchorChain : VEnv.empty.TypeChain 0 []
    ((VExpr.bvar 0).subst leftAnchor) ((VExpr.bvar 0).subst rightAnchor) :=
  (TypeChain.refl (HasType.bvar Lookup.zero)).substDF .empty (by trivial) relatedAnchors

theorem neutralEta :
    vcls VEnv.empty 0 [idType] VExpr.Subst.id
      (.lam (.sort one) (.app (VExpr.bvar 0).lift (.bvar 0))) idType =
    vcls VEnv.empty 0 [idType] VExpr.Subst.id (.bvar 0) idType := by
  have ctx : OnCtx [idType] (VEnv.empty.IsType 0) :=
    ⟨(by trivial), _, .forallE (HasType.sort (by trivial)) (HasType.sort (by trivial))⟩
  have hf : VEnv.empty.HasType 0 [idType] (.bvar 0) idType := .bvar .zero
  exact vcls_eta .empty ctx (Ctx.SubstEq.id .empty ctx) hf

run_meta
  let roots := [``TypeChain.single, ``TypeChain.refl, ``TypeChain.trans,
    ``TypeChain.symm, ``TypeChain.map, ``TypeChain.defeqDF,
    ``TypeChain.isType_l, ``TypeChain.isType_r, ``TypeChain.weakN,
    ``TypeChain.instN, ``TypeChain.subst, ``TypeChain.substDF,
    ``LvEq.defeq, ``LvEq.instL, ``TypeChain.of_lvEq,
    ``TyCls.chain_of_isType, ``TyCls.mem_iff_chain, ``TyCls.defeq, ``TyCls.defeq_rev,
    ``ElCls.collapse, ``TypedElCls.mem, ``TypedElCls.defeq, ``TypedElCls.hasType,
    ``SubstEq.symm, ``SubstEq.right, ``vcls_app, ``vcls_beta,
    ``TypeChain.tyCls_subst_of_ctx, ``vcls_substEq, ``vcls_defeq, ``vcls_eta,
    ``vcls_closed, ``vcls_conv, ``zeroEq, ``oneEq, ``zeroSyntax, ``oneSyntax,
    ``sortEquality, ``heterogeneousChain, ``collapsedLevelMember, ``idTyped,
    ``argClassTyped, ``otherMember, ``betaAtOtherMember, ``actualApplication,
    ``relatedAnchors, ``distinctAnchors, ``dependentIdentityTyped,
    ``relatedAnchorClasses, ``relatedAnchorChain, ``neutralEta]
  let manifests : List (Name × List Name) := [
    (`Lean4Lean.VEnv.TypeChain.single, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.refl, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.trans, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.symm, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.map, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.defeqDF, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.isType_l, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.isType_r, [`propext]),
    (`Lean4Lean.VEnv.TypeChain.weakN, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.TypeChain.instN, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.TypeChain.subst, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.TypeChain.substDF, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.LvEq.defeq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.LvEq.instL, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypeChain.of_lvEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TyCls.chain_of_isType, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TyCls.mem_iff_chain, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TyCls.defeq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TyCls.defeq_rev, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.ElCls.collapse, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedElCls.mem, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedElCls.defeq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypedElCls.hasType, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SubstEq.symm, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.SubstEq.right, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_app, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_beta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.TypeChain.tyCls_subst_of_ctx, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_substEq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_defeq, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_eta, [`Quot.sound, `propext]),
    (`Lean4Lean.VEnv.Model.vcls_closed, [`propext]),
    (`Lean4Lean.VEnv.Model.vcls_conv, [`Quot.sound, `propext]),
    (`ModelClassesTest.zeroEq, [`Quot.sound, `propext]),
    (`ModelClassesTest.oneEq, [`Quot.sound, `propext]),
    (`ModelClassesTest.zeroSyntax, []),
    (`ModelClassesTest.oneSyntax, []),
    (`ModelClassesTest.sortEquality, [`Quot.sound, `propext]),
    (`ModelClassesTest.heterogeneousChain, [`Quot.sound, `propext]),
    (`ModelClassesTest.collapsedLevelMember, [`Quot.sound, `propext]),
    (`ModelClassesTest.idTyped, [`propext]),
    (`ModelClassesTest.argClassTyped, [`propext]),
    (`ModelClassesTest.otherMember, [`Quot.sound, `propext]),
    (`ModelClassesTest.betaAtOtherMember, [`Quot.sound, `propext]),
    (`ModelClassesTest.actualApplication, [`Quot.sound, `propext]),
    (`ModelClassesTest.relatedAnchors, [`Quot.sound, `propext]),
    (`ModelClassesTest.distinctAnchors, []),
    (`ModelClassesTest.dependentIdentityTyped, [`propext]),
    (`ModelClassesTest.relatedAnchorClasses, [`Quot.sound, `propext]),
    (`ModelClassesTest.relatedAnchorChain, [`Quot.sound, `propext]),
    (`ModelClassesTest.neutralEta, [`Quot.sound, `propext])]
  let forbidden := [`Lean4Lean.VEnv.NormalEq.parRed, `Lean4Lean.VEnv.NormalEq.parRedS,
    `Lean4Lean.VEnv.IsDefEq.church_rosser, `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    `Lean4Lean.VEnv.IsDefEqU.quot_inj, `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    `Lean4Lean.VEnv.HasType.weakN_iff, `Lean4Lean.VEnv.NormalEq.trans,
    `Lean4Lean.VEnv.IsDefEqU.sort_inv, `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    `Classical.choice]
  let environment ← getEnv
  unless roots.length == manifests.length do throwError "model-class manifest count changed"
  for root in roots do
    let some (_, expectedAxioms) := manifests.find? (fun entry => entry.1 == root)
      | throwError "missing model-class manifest {root}"
    let info ← getConstInfo root
    if info matches .axiomInfo _ then throwError "new model-class axiom {root}"
    let some proof := info.value? | throwError "missing model-class proof {root}"
    if proof.hasSorry then throwError "direct model-class admission {root}"
    let axioms ← collectAxioms root
    unless axioms.size == expectedAxioms.length && expectedAxioms.all axioms.contains do
      throwError "model-class axiom manifest changed for {root}: {repr axioms}"
    let mut pending := #[root]
    let mut visited : NameSet := {}
    for _ in [:1000000] do
      if pending.isEmpty then break
      let name := pending.back!
      pending := pending.pop
      if visited.contains name then continue
      visited := visited.insert name
      if forbidden.contains name then throwError "forbidden model-class dependency {name} in {root}"
      if let some declaration := environment.find? name then
        if declaration.type.hasSorry then throwError "admitted model-class type {name} in {root}"
        pending := pending ++ declaration.type.getUsedConstants
        if let .inductInfo inductiveInfo := declaration then
          pending := pending ++ inductiveInfo.ctors.toArray
        if let some value := declaration.value? then
          if value.hasSorry then throwError "model-class admission {name} in {root}"
          pending := pending ++ value.getUsedConstants
    unless pending.isEmpty do throwError "model-class traversal exceeded bound"
    let required :=
      if root == ``ElCls.collapse then [``TyCls.defeq, ``LvEq.defeq]
      else if root == ``vcls_beta then
        [``ElCls.collapse, ``TypedElCls.defeq, ``IsDefEq.beta, ``IsDefEq.substDF]
      else if root == ``vcls_app then [``ElCls.collapse, ``IsDefEq.appDF]
      else if root == ``vcls_substEq then [``IsDefEq.substDF, ``TyCls.eq_of_defeq]
      else if root == ``SubstEq.symm then [``IsDefEq.substDF]
      else if root == ``TypeChain.substDF then
        [``TypeChain.subst, ``IsDefEq.substDF, ``TypeChain.isType_r]
      else if root == ``vcls_eta then [``vcls_defeq, ``IsDefEq.eta]
      else if root == ``LvEq.instL then [``EqUpToLevels.instL_of_levels]
      else if root == ``heterogeneousChain then [``IsDefEq.defeqDF, ``TypeChain.tail]
      else if root == ``collapsedLevelMember then [``ElCls.collapse]
      else if root == ``betaAtOtherMember then [``vcls_beta, ``otherMember]
      else if root == ``actualApplication then [``vcls_app]
      else if root == ``relatedAnchorClasses then [``vcls_substEq, ``relatedAnchors]
      else if root == ``relatedAnchorChain then [``TypeChain.substDF, ``relatedAnchors]
      else if root == ``neutralEta then [``vcls_eta]
      else []
    unless required.all visited.contains do
      throwError "model-class proof bypassed required dependencies in {root}: {repr required}"
    logInfo m!"AUDIT {root}|{visited.size}|#[]|{repr axioms}"

end ModelClassesTest
