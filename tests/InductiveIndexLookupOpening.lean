import Lean4Lean.Verify.InductiveIndexLookupOpening
import Lean.Util.CollectAxioms

open Lean Lean4Lean Lean4Lean.AddInductive
open Lean4Lean.ElimNestedInductive (ContextReserved SourceReserved)

namespace InductiveIndexLookupOpeningTest

private def tagged : MData := { entries := [(`LookupOpeningTag, .ofNat 1)] }

private def sortType : Expr := .sort (.succ .zero)

private def equalityDomain (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.succ .zero]) carrier first second

private def proofEquality (carrier first second : Expr) : Expr :=
  mkApp3 (.const ``Eq [.zero]) carrier first second

private def dependent : Expr := .forallE `carrier sortType
  (.forallE `element (.bvar 0)
    (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0))
      (.forallE `again
        (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
        sortType .default) .instImplicit) .strictImplicit) .implicit

private theorem dependentShape : SortTelescope dependent :=
  .forallE `carrier sortType .implicit
    (.forallE `element (.bvar 0) .strictImplicit
      (.forallE `witness (equalityDomain (.bvar 1) (.bvar 0) (.bvar 0)) .instImplicit
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 2) (.bvar 1) (.bvar 1)) (.bvar 0) (.bvar 0))
          .default (.sort (.succ .zero)))))

private def wrapped (data : MData) : Expr :=
  .mdata data (.letE `unused (.const ``Nat []) (.lit (.natVal 0)) dependent true)

private theorem wrappedTrace (data : MData) : WrappedSortTelescope (wrapped data) dependent := by
  unfold wrapped
  apply WrappedSortTelescope.mdata
  apply WrappedSortTelescope.letE
  rw [Expr.instantiate1_eq]
  change WrappedSortTelescope dependent dependent
  exact .telescope dependentShape

private def header (name : Name) (type : Expr) : InductiveType := { name, type, ctors := [] }

private def provedTypes (data : MData) : Array InductiveType := #[
  header `LookupOpeningWrapped (wrapped data), header `LookupOpeningAnnotated (.mdata data dependent)]

private theorem provedHeaders (data : MData) : WrappedHeaderTelescope (provedTypes data) := by
  intro parent bound
  have cases : parent = 0 ∨ parent = 1 := by
    have small : parent < 2 := by simpa [provedTypes] using bound
    omega
  rcases cases with rfl | rfl
  · exact ⟨dependent, wrappedTrace data⟩
  · exact ⟨dependent, .mdata data (.telescope dependentShape)⟩

private theorem singletonInjection (source target : FVarId) : IndexPairInjection [(source, target)] := by
  simp [IndexPairInjection]

private theorem singletonLookup (source target : FVarId) : indexLookup [(source, target)] source = target :=
  indexLookup_of_mem (singletonInjection source target) (by simp)

private theorem depthTwoLooseReplacement :
    (Expr.bvar 2).instantiate1' (.bvar 0) 2 = .bvar 2 := rfl

private theorem depthTwoBelowUnchanged :
    (Expr.bvar 1).instantiate1' (.bvar 0) 2 = .bvar 1 := rfl

private theorem depthTwoAboveDecrements :
    (Expr.bvar 4).instantiate1' (.bvar 0) 2 = .bvar 3 := rfl

private theorem nestedLooseReplacement :
    (Expr.lam `local sortType (.bvar 1) .implicit).instantiate1' (.bvar 0) 0 =
      .lam `local sortType (.bvar 1) .implicit := rfl

private theorem duplicateFirstMatch (source first second : FVarId) :
    indexLookup [(source, first), (source, second)] source = first := by
  simp [indexLookup]

private theorem missingFreshnessChangesReplacement (source first second : FVarId) (different : first ≠ second) :
    indexRenameExpr ([(source, first)] ++ [(source, second)]) ((Expr.bvar 0).instantiate1' (.fvar source) 0) ≠
      (Expr.bvar 0).instantiate1' (.fvar second) 0 := by
  simp [Expr.instantiate1', indexRenameExpr, indexLookup, different]

private theorem missingBodySupportChangesExistingFVar (source target : FVarId) (different : source ≠ target) :
    indexRenameExpr [(source, target)] (.fvar source) ≠ indexRenameExpr [] (.fvar source) := by
  simp [indexRenameExpr, indexLookup, Ne.symm different]

private theorem identityExtensionCanIgnoreBodySupport (id : FVarId) :
    indexRenameExpr [(id, id)] (.fvar id) = indexRenameExpr [] (.fvar id) := by
  simp [indexRenameExpr, indexLookup]

private theorem rawLiftCommutes (pairs : List (FVarId × FVarId)) (body : Expr) (start amount : Nat) :
    indexRenameExpr pairs (body.liftLooseBVars' start amount) =
      (indexRenameExpr pairs body).liftLooseBVars' start amount :=
  indexRenameExpr_liftLooseBVars' pairs body start amount

private theorem rawSubstitutionDepthCommutes (pairs : List (FVarId × FVarId))
    (body replacement : Expr) (depth : Nat) :
    indexRenameExpr pairs (body.instantiate1' replacement depth) =
      (indexRenameExpr pairs body).instantiate1' (indexRenameExpr pairs replacement) depth :=
  indexRenameExpr_instantiate1' pairs body replacement depth

private theorem rawSubstitutionCommutes (pairs : List (FVarId × FVarId)) (body replacement : Expr) :
    indexRenameExpr pairs (body.instantiate1 replacement) =
      (indexRenameExpr pairs body).instantiate1 (indexRenameExpr pairs replacement) :=
  indexRenameExpr_instantiate1 pairs body replacement

private theorem rawSignaturePreserved (pairs : List (FVarId × FVarId)) (body : Expr) :
    Expr.binderSignature (indexRenameExpr pairs body) = Expr.binderSignature body :=
  indexRenameExpr_binderSignature pairs body

private theorem relatedLift {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) (start amount : Nat) :
    IndexLookupRenaming pairs (left.liftLooseBVars' start amount) (right.liftLooseBVars' start amount) :=
  related.liftLooseBVars' start amount

private theorem relatedSubstitutionDepth {pairs : List (FVarId × FVarId)}
    {left right leftValue rightValue : Expr} (related : IndexLookupRenaming pairs left right)
    (values : IndexLookupRenaming pairs leftValue rightValue) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' leftValue depth) (right.instantiate1' rightValue depth) :=
  related.instantiate1' values depth

private theorem relatedSubstitution {pairs : List (FVarId × FVarId)}
    {left right leftValue rightValue : Expr} (related : IndexLookupRenaming pairs left right)
    (values : IndexLookupRenaming pairs leftValue rightValue) :
    IndexLookupRenaming pairs (left.instantiate1 leftValue) (right.instantiate1 rightValue) :=
  related.instantiate1 values

private theorem relatedSignature {pairs : List (FVarId × FVarId)} {left right : Expr}
    (related : IndexLookupRenaming pairs left right) : Expr.binderSignature left = Expr.binderSignature right :=
  related.binderSignature

private theorem freshKeyMaps {pairs : List (FVarId × FVarId)} {source target : FVarId}
    (fresh : source ∉ pairs.map Prod.fst) : indexLookup (pairs ++ [(source, target)]) source = target :=
  indexLookup_append_fresh fresh

private theorem otherLookupPreserved {pairs : List (FVarId × FVarId)} {source target id : FVarId}
    (different : id ≠ source) : indexLookup (pairs ++ [(source, target)]) id = indexLookup pairs id :=
  indexLookup_append_of_ne different

private theorem avoidingBodyPreserved {pairs : List (FVarId × FVarId)}
    {source target : FVarId} {body : Expr} (avoids : IndexAvoids source body) :
    indexRenameExpr (pairs ++ [(source, target)]) body = indexRenameExpr pairs body :=
  indexRenameExpr_append_of_avoids avoids

private theorem finiteSupportAvoids {params : List FVarId} {body : Expr} {source : FVarId}
    (within : IndexFVarsWithin params body) (outside : source ∉ params) : IndexAvoids source body :=
  within.avoids outside

private theorem fixedExpression {pairs : List (FVarId × FVarId)} {params : List FVarId} {value : Expr}
    (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) :
    indexRenameExpr pairs value = value := indexRenameExpr_fixedParameters support within

private theorem freshOpeningDepth {pairs : List (FVarId × FVarId)} {left right : Expr}
    {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (avoids : IndexAvoids source left) (fresh : source ∉ pairs.map Prod.fst) (depth : Nat) :
    IndexLookupRenaming (pairs ++ [(source, target)])
      (left.instantiate1' (.fvar source) depth) (right.instantiate1' (.fvar target) depth) :=
  related.openFreshIndex' avoids fresh depth

private theorem freshOpening {pairs : List (FVarId × FVarId)} {left right : Expr}
    {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (avoids : IndexAvoids source left) (fresh : source ∉ pairs.map Prod.fst) :
    IndexLookupRenaming (pairs ++ [(source, target)])
      (left.instantiate1 (.fvar source)) (right.instantiate1 (.fvar target)) :=
  related.openFreshIndex avoids fresh

private theorem mappedOpeningDepth {pairs : List (FVarId × FVarId)} {left right : Expr}
    {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (injection : IndexPairInjection pairs) (listed : (source, target) ∈ pairs) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' (.fvar source) depth) (right.instantiate1' (.fvar target) depth) :=
  related.openMappedIndex' injection listed depth

private theorem mappedOpening {pairs : List (FVarId × FVarId)} {left right : Expr}
    {source target : FVarId} (related : IndexLookupRenaming pairs left right)
    (injection : IndexPairInjection pairs) (listed : (source, target) ∈ pairs) :
    IndexLookupRenaming pairs (left.instantiate1 (.fvar source)) (right.instantiate1 (.fvar target)) :=
  related.openMappedIndex injection listed

private theorem fixedOpeningDepth {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {left right value : Expr} (related : IndexLookupRenaming pairs left right)
    (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' value depth) (right.instantiate1' value depth) :=
  related.openFixedParameters' support within depth

private theorem fixedOpening {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {left right value : Expr} (related : IndexLookupRenaming pairs left right)
    (support : IndexParameterSupport pairs params) (within : IndexFVarsWithin params value) :
    IndexLookupRenaming pairs (left.instantiate1 value) (right.instantiate1 value) :=
  related.openFixedParameters support within

private theorem overlappingFreshOpening (old source target param : FVarId)
    (fresh : source ≠ old) (shared : param ≠ source) (depth : Nat) :
    let body := Expr.app (.fvar old) (.app (.bvar 0) (.fvar param))
    IndexLookupRenaming ([(old, source)] ++ [(source, target)])
      (body.instantiate1' (.fvar source) depth)
      ((indexRenameExpr [(old, source)] body).instantiate1' (.fvar target) depth) := by
  dsimp only
  apply IndexLookupRenaming.openFreshIndex' (show IndexLookupRenaming [(old, source)] _ _ from rfl)
  · simp [IndexAvoids, Ne.symm fresh, shared]
  · simpa using fresh

private def fixedValue (param : FVarId) : Expr :=
  .lam `replacement (.fvar param) (.app (.fvar param) (.bvar 2)) .implicit

private theorem looseFixedValueWithin (param : FVarId) : IndexFVarsWithin [param] (fixedValue param) := by
  simp [IndexFVarsWithin, fixedValue]

private theorem fixedLooseReplacement {pairs : List (FVarId × FVarId)} {left right : Expr} {param : FVarId}
    (related : IndexLookupRenaming pairs left right) (support : IndexParameterSupport pairs [param]) (depth : Nat) :
    IndexLookupRenaming pairs (left.instantiate1' (fixedValue param) depth)
      (right.instantiate1' (fixedValue param) depth) :=
  related.openFixedParameters' support (looseFixedValueWithin param) depth

private theorem duplicateTargetRejected (first second target : FVarId) :
    ¬ IndexPairInjection ([(first, target)] ++ [(second, target)]) := by
  simp [IndexPairInjection]

private theorem sharedSourceExtensionRejected (param target : FVarId) :
    ¬ IndexParameterSupport ([] ++ [(param, target)]) [param] := by
  intro support
  exact (support param (by simp)) (by simp)

private theorem injectionExtendsFresh {pairs : List (FVarId × FVarId)} {source target : FVarId}
    (injection : IndexPairInjection pairs) (sourceFresh : source ∉ pairs.map Prod.fst)
    (targetFresh : target ∉ pairs.map Prod.snd) : IndexPairInjection (pairs ++ [(source, target)]) :=
  injection.appendFresh sourceFresh targetFresh

private theorem parametersExtendFresh {pairs : List (FVarId × FVarId)} {params : List FVarId}
    {source target : FVarId} (support : IndexParameterSupport pairs params) (outside : source ∉ params) :
    IndexParameterSupport (pairs ++ [(source, target)]) params := support.appendFresh outside

private theorem swappedPairsRemainInjective (first second : FVarId) (different : first ≠ second) :
    IndexPairInjection ([(first, second)] ++ [(second, first)]) :=
  (singletonInjection first second).appendFresh (by simpa using Ne.symm different) (by simpa using different)

private theorem actualParameterFreshness {ctx : Context} {bound : Nat} {values : List Expr}
    (support : BinderValuesBefore ctx bound values) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (⟨ctx.ngen.curr⟩ : FVarId) ∉ values.map Expr.fvarId! := support.currentFresh hwf hreserved

private theorem actualKeyFreshness {ctx : Context} {pairs : List (FVarId × FVarId)}
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (declared : ∀ id ∈ pairs.map Prod.fst, ∃ decl, ctx.lctx.find? id = some decl) :
    (⟨ctx.ngen.curr⟩ : FVarId) ∉ pairs.map Prod.fst := indexSourceFresh_of_declared hwf hreserved declared

private theorem actualCurrentOpening {ctx : Context} {pairs : List (FVarId × FVarId)}
    {left right : Expr} {target : FVarId} (related : IndexLookupRenaming pairs left right)
    (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen)
    (declared : ∀ id ∈ pairs.map Prod.fst, ∃ decl, ctx.lctx.find? id = some decl)
    (sourceReserved : SourceReserved left ctx.ngen) :
    IndexLookupRenaming (pairs ++ [(⟨ctx.ngen.curr⟩, target)])
      (left.instantiate1 (.fvar ⟨ctx.ngen.curr⟩)) (right.instantiate1 (.fvar target)) :=
  related.openCurrentIndex hwf hreserved declared sourceReserved

private theorem actualParentOpening {stats : InductiveStats} {types : Array InductiveType}
    {parent : Nat} {checked generated : Context} {info : RecInfo}
    (alignment : ParentBinderSupportAlignment stats types parent checked generated info) :
    ∃ (checkedIds : List FVarId) (pairs : List (FVarId × FVarId)), checkedIds.length = stats.nindices[parent]! ∧
      pairs = checkedIds.zip (info.indices.toList.map Expr.fvarId!) ∧
      IndexOpeningLookup pairs (stats.params.toList.map Expr.fvarId!) := by
  obtain ⟨checkedIds, pairs, hcount, hzip, _, _, _, _, _, hopen⟩ := alignment.openingLookup
  exact ⟨checkedIds, pairs, hcount, hzip, hopen⟩

private theorem provedRegisteredOpening (data : MData) (ctx : Context) (hwf : ctx.lctx.WF)
    (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    (checkInductiveTypes 1 (provedTypes data) (fun stats => do
      withEnv (← declareInductiveTypes stats 1 (provedTypes data) 0 false) do
        checkConstructors (provedTypes data) stats false
        withEnv (← declareConstructors stats (provedTypes data) false) do
          let result ← mkRecInfos.scopeRegistration stats (provedTypes data) (.succ .zero) [] false false
          return (stats, result)) ctx).WF fun result =>
      RecursorIndexCounts result.1 (provedTypes data) result.2.2.1 ∧ ∃ checkedRoot,
        CheckedHeaderSources 1 (provedTypes data) ctx result.1 checkedRoot ∧
        ∀ parent, parent < (provedTypes data).size → ∃ (checkedIds : List FVarId) (pairs : List (FVarId × FVarId)),
          checkedIds.length = result.1.nindices[parent]! ∧
          pairs = checkedIds.zip (result.2.2.1[parent]!.indices.toList.map Expr.fvarId!) ∧
          IndexOpeningLookup pairs (result.1.params.toList.map Expr.fvarId!) :=
  (checkInductiveTypes.safeRegisteredWrappedBinderSupport 1 (provedTypes data) 0 (.succ .zero) [] false ctx
    (provedHeaders data) hwf hreserved).mono fun _ ⟨hcounts, checkedRoot, hheaders, alignment⟩ =>
      ⟨hcounts, checkedRoot, hheaders, fun parent hparent => actualParentOpening (alignment.2 parent hparent)⟩

private def constructors (source param : FVarId) : Array Expr := #[
  .bvar 2, .fvar source, .mvar ⟨`LookupOpeningMeta⟩, .sort (.succ (.param `u)),
  .const `LookupOpeningConstant [.param `u], .lit (.natVal 7),
  .app (.fvar source) (.bvar 2),
  .lam `local (.app (.fvar param) (.bvar 0)) (.app (.fvar source) (.bvar 2)) .instImplicit,
  .forallE `index (.app (.fvar param) (.bvar 0)) (.app (.fvar source) (.bvar 3)) .strictImplicit,
  .letE `hidden (.app (.fvar param) (.bvar 0)) (.app (.fvar source) (.bvar 2))
    (.app (.fvar source) (.bvar 3)) false,
  .mdata tagged (.app (.fvar source) (.bvar 2)),
  .proj `LookupOpeningStructure 2 (.app (.fvar source) (.bvar 2))]

private def checkSubstitution (pairs : List (FVarId × FVarId)) (body replacement : Expr) (depth : Nat) :
    MetaM Unit := do
  unless indexRenameExpr pairs (body.instantiate1' replacement depth) ==
      (indexRenameExpr pairs body).instantiate1' (indexRenameExpr pairs replacement) depth do
    throwError "lookup-opening raw instantiate1' compatibility failed at depth {depth}"

private def checkLift (pairs : List (FVarId × FVarId)) (body : Expr) (start amount : Nat) : MetaM Unit := do
  unless indexRenameExpr pairs (body.liftLooseBVars' start amount) ==
      (indexRenameExpr pairs body).liftLooseBVars' start amount do
    throwError "lookup-opening raw liftLooseBVars' compatibility failed at start {start}/amount {amount}"

private def substitutionMatrix : MetaM Unit := do
  let source : FVarId := ⟨`LookupOpeningSource⟩
  let target : FVarId := ⟨`LookupOpeningTarget⟩
  let other : FVarId := ⟨`LookupOpeningOther⟩
  let param : FVarId := ⟨`LookupOpeningParam⟩
  let plans := [[], [(source, target)], [(source, source)], [(source, target), (target, source)],
    [(source, target), (source, other)], [(source, target), (other, target)]]
  let replacements := [Expr.fvar source, .bvar 0, .bvar 3, .app (.fvar source) (.bvar 1),
    .lam `replacement (.fvar param) (.app (.fvar source) (.bvar 2)) .implicit]
  for pairs in plans do
    for body in constructors source param do
      for replacement in replacements do
        for depth in [0, 1, 2, 4] do
          checkSubstitution pairs body replacement depth
      for start in [0, 1, 3] do
        for amount in [0, 1, 2, 5] do
          checkLift pairs body start amount
  logInfo "1440 raw substitution checks and 864 raw loose-bvar lift checks cover all 12 Expr constructors, six pair lists, four depths, and loose replacements"

private def extensionControls : MetaM Unit := do
  let source : FVarId := ⟨`LookupOpeningOldSource⟩
  let intermediate : FVarId := ⟨`LookupOpeningFreshSource⟩
  let target : FVarId := ⟨`LookupOpeningFreshTarget⟩
  let param : FVarId := ⟨`LookupOpeningShared⟩
  let pairs := [(source, intermediate)]
  let extended := pairs ++ [(intermediate, target)]
  let body := Expr.app (.fvar source) (.app (.bvar 0) (.fvar param))
  unless !(body.containsFVar intermediate) && indexLookup pairs intermediate == intermediate &&
      indexLookup extended intermediate == target && indexLookup extended source == intermediate do
    throwError "lookup-opening overlapping target/new-source support setup failed"
  unless indexRenameExpr extended (body.instantiate1' (.fvar intermediate) 0) ==
      (indexRenameExpr pairs body).instantiate1' (.fvar target) 0 do
    throwError "lookup-opening matched fresh pair incorrectly required global source/target disjointness"
  unless indexLookup extended param == param do
    throwError "lookup-opening extension changed a supported shared parameter"
  let duplicate := pairs ++ [(source, target)]
  unless indexLookup duplicate source == intermediate && indexLookup duplicate source != target do
    throwError "lookup-opening missing key freshness was incorrectly accepted"
  unless indexRenameExpr [(intermediate, target)] (.fvar intermediate) !=
      indexRenameExpr [] (.fvar intermediate) do
    throwError "lookup-opening missing body support was incorrectly accepted"
  unless indexRenameExpr [(intermediate, intermediate)] (.fvar intermediate) ==
      indexRenameExpr [] (.fvar intermediate) do
    throwError "lookup-opening identity extension control failed"
  let reusedTarget := pairs ++ [(intermediate, intermediate)]
  unless (reusedTarget.map Prod.snd).eraseDups.length != reusedTarget.length &&
      indexRenameExpr reusedTarget ((Expr.bvar 0).instantiate1' (.fvar intermediate) 0) == .fvar intermediate do
    throwError "lookup-opening reused target incorrectly retained pair injection or lost deterministic opening"
  unless indexLookup [(param, target)] param != param do
    throwError "lookup-opening source/shared-parameter collision incorrectly retained fixed parameter support"
  logInfo "eight fresh-extension/fixed-parameter/overlap/duplicate/missing-support/identity/target-reuse/shared-source control groups retain explicit boundaries"

private def stage (nparams : Nat) (types : Array InductiveType) :
    M (InductiveStats × Context × Context × Kernel.Environment × Array RecInfo × Context) :=
  checkInductiveTypes nparams types fun stats => do
    let checked ← readThe Context
    withEnv (← declareInductiveTypes stats nparams types 0 false) do
      checkConstructors types stats false
      withEnv (← declareConstructors stats types false) do
        let generatorRoot ← readThe Context
        let result ← mkRecInfos.scopeRegistration stats types (.succ .zero)
          generatorRoot.lparams false false
        return (stats, checked, generatorRoot, result)

private def valuesAt (ctx : Context) (start count : Nat) : MetaM (Array Expr) := do
  let mut values := #[]
  for offset in [:count] do
    let some decl := ctx.lctx.getAt? (start + offset)
      | throwError "lookup-opening checked source allocation points at a hole"
    let some byId := ctx.lctx.find? decl.fvarId
      | throwError "lookup-opening checked source allocation is absent from native find?"
    unless byId.index == decl.index && byId.toExpr == decl.toExpr && decl.index == start + offset do
      throwError "lookup-opening actual source find?/getAt? receipts disagree"
    values := values.push decl.toExpr
  return values

private def checkOpeningStep (pairs : List (FVarId × FVarId)) (parameter : Bool)
    (leftBody rightBody leftValue rightValue : Expr) : MetaM (List (FVarId × FVarId)) := do
  if parameter then
    unless leftValue == rightValue && indexRenameExpr pairs leftValue == rightValue do
      throwError "lookup-opening actual parameter replacement is not fixed"
    unless indexRenameExpr pairs (leftBody.instantiate1 leftValue) == rightBody.instantiate1 rightValue do
      throwError "lookup-opening actual shared-parameter substitution lost deterministic correspondence"
    return pairs
  else
    let source := leftValue.fvarId!
    unless !(pairs.any (·.1 == source)) && !(leftBody.containsFVar source) do
      throwError "lookup-opening actual checked index lacks fresh-key/body-support receipts"
    let extended := pairs ++ [(source, rightValue.fvarId!)]
    unless indexRenameExpr extended leftBody == rightBody &&
        indexRenameExpr extended (leftBody.instantiate1 leftValue) == rightBody.instantiate1 rightValue do
      throwError "lookup-opening actual fresh index substitution lost deterministic correspondence"
    return extended

private def checkOpening (nparams : Nat) (type : Expr) (params checked generated : Array Expr) : MetaM Unit := do
  let mut left := type
  let mut right := type
  let mut pairs : List (FVarId × FVarId) := []
  let leftValues := params ++ checked
  let rightValues := params ++ generated
  for position in [:leftValues.size] do
    let .forallE leftName leftDomain leftBody leftBi := left
      | throwError "lookup-opening checked plan ended before its actual substitutions"
    let .forallE rightName rightDomain rightBody rightBi := right
      | throwError "lookup-opening generated plan ended before its actual substitutions"
    unless leftName == rightName && leftBi == rightBi && indexRenameExpr pairs leftDomain == rightDomain &&
        indexRenameExpr pairs leftBody == rightBody do
      throwError "lookup-opening raw deterministic binder correspondence failed"
    pairs ← checkOpeningStep pairs (position < nparams) leftBody rightBody leftValues[position]! rightValues[position]!
    left := leftBody.instantiate1 leftValues[position]!
    right := rightBody.instantiate1 rightValues[position]!
  unless left == sortType && right == sortType && pairs.length == checked.size do
    throwError "lookup-opening actual paired telescope terminals or finite mapping count changed"

private def checkFixture (ctx : Context) (nparams : Nat) (types : Array InductiveType)
    (expected : Array Nat) : MetaM Unit := do
  let .ok (stats, checked, _, env, infos, _) := stage nparams types ctx
    | throwError "lookup-opening successful registration fixture failed: {types.map (·.name)}"
  unless stats.params.size == nparams && stats.nindices == expected && infos.size == types.size do
    throwError "lookup-opening actual registered counts changed"
  for parent in [:types.size] do
    let checkedStart := ctx.lctx.numIndices + nparams + (expected.toList.take parent).sum
    let checkedValues ← valuesAt checked checkedStart expected[parent]!
    let .ok normalized := ((monadLift (TypeChecker.whnf types[parent]!.type) : M Expr) checked)
      | throwError "lookup-opening source normalization failed"
    checkOpening nparams normalized stats.params checkedValues infos[parent]!.indices
    let some (.recInfo recursor) := env.find? (mkRecName types[parent]!.name)
      | throwError "lookup-opening successful fixture lost registered recursor"
    unless recursor.numParams == nparams && recursor.numIndices == expected[parent]! do
      throwError "lookup-opening actual registered metadata changed"

private def multipleParams : Expr := .forallE `carrier sortType
  (.forallE `pivot (.bvar 0)
    (.forallE `element (.bvar 1)
      (.forallE `witness (equalityDomain (.bvar 2) (.bvar 0) (.bvar 1))
        (.forallE `again
          (proofEquality (equalityDomain (.bvar 3) (.bvar 1) (.bvar 2)) (.bvar 0) (.bvar 0))
          sortType .default) .instImplicit) .strictImplicit) .default) .implicit

private def fixtures (ctx : Context) : MetaM Unit := do
  checkFixture ctx 0 #[header `LookupOpeningEmpty sortType] #[0]
  for nparams in [0, 1, 2, 3, 4] do
    checkFixture ctx nparams #[header (Name.mkNum `LookupOpeningDependent nparams) dependent] #[4 - nparams]
  checkFixture ctx 1 #[header `LookupOpeningWrappedDependent (wrapped tagged)] #[3]
  checkFixture ctx 1 #[header `LookupOpeningMutualFirst dependent,
    header `LookupOpeningMutualSecond (.mdata tagged dependent)] #[3, 3]
  checkFixture ctx 2 #[header `LookupOpeningMultiple multipleParams] #[3]
  checkFixture ctx 0 #[header `LookupOpeningIndependentNat
    (.forallE `first (.const ``Nat []) (.forallE `second (.const ``Nat []) sortType .default) .default)] #[2]

private def audit (theoremName : Name) (interfaces : List Name := []) : MetaM Unit := do
  let axioms ← collectAxioms theoremName
  logInfo m!"{theoremName}: axioms = {repr axioms}"
  for axiomName in axioms do
    unless ([``propext, ``Classical.choice, ``Quot.sound] ++ interfaces).contains axiomName do
      throwError "unexpected axiom {axiomName} in {theoremName}"

run_meta
  let binding := [``Expr.instantiate1_eq]
  let scope := [``PersistentArray.toList'_push, ``PersistentHashMap.WF.find?_eq,
    ``PersistentHashMap.WF.toList'_insert]
  let normalized := binding ++ [``Expr.instantiateRange_eq, ``Expr.instantiate_eq]
  audit ``dependentShape
  audit ``wrappedTrace binding
  audit ``provedHeaders binding
  audit ``singletonInjection
  audit ``singletonLookup
  audit ``depthTwoLooseReplacement
  audit ``depthTwoBelowUnchanged
  audit ``depthTwoAboveDecrements
  audit ``nestedLooseReplacement
  audit ``duplicateFirstMatch
  audit ``missingFreshnessChangesReplacement
  audit ``missingBodySupportChangesExistingFVar
  audit ``identityExtensionCanIgnoreBodySupport
  audit ``rawLiftCommutes
  audit ``rawSubstitutionDepthCommutes
  audit ``rawSubstitutionCommutes binding
  audit ``rawSignaturePreserved
  audit ``relatedLift
  audit ``relatedSubstitutionDepth
  audit ``relatedSubstitution binding
  audit ``relatedSignature
  audit ``freshKeyMaps
  audit ``otherLookupPreserved
  audit ``avoidingBodyPreserved
  audit ``finiteSupportAvoids
  audit ``fixedExpression
  audit ``freshOpeningDepth
  audit ``freshOpening binding
  audit ``mappedOpeningDepth
  audit ``mappedOpening binding
  audit ``fixedOpeningDepth
  audit ``fixedOpening binding
  audit ``overlappingFreshOpening
  audit ``looseFixedValueWithin
  audit ``fixedLooseReplacement
  audit ``duplicateTargetRejected
  audit ``sharedSourceExtensionRejected
  audit ``injectionExtendsFresh
  audit ``parametersExtendFresh
  audit ``swappedPairsRemainInjective
  audit ``actualParameterFreshness scope
  audit ``actualKeyFreshness scope
  audit ``actualCurrentOpening (binding ++ scope)
  audit ``actualParentOpening
  audit ``provedRegisteredOpening (normalized ++ scope)
  audit ``indexRenameExpr_liftLooseBVars'
  audit ``indexRenameExpr_instantiate1'
  audit ``indexRenameExpr_instantiate1 binding
  audit ``indexRenameExpr_binderSignature
  audit ``IndexLookupRenaming.liftLooseBVars'
  audit ``IndexLookupRenaming.instantiate1'
  audit ``IndexLookupRenaming.instantiate1 binding
  audit ``IndexLookupRenaming.binderSignature
  audit ``IndexAvoids.iff_not_mem
  audit ``IndexAvoids.of_not_mem
  audit ``IndexFVarsWithin.iff_subset
  audit ``IndexFVarsWithin.of_subset
  audit ``IndexFVarsWithin.avoids
  audit ``indexLookup_append_fresh
  audit ``indexLookup_append_of_ne
  audit ``indexRenameExpr_append_of_avoids
  audit ``indexRenameExpr_fixedParameters
  audit ``IndexLookupRenaming.openFreshIndex'
  audit ``IndexLookupRenaming.openFreshIndex binding
  audit ``IndexLookupRenaming.openMappedIndex'
  audit ``IndexLookupRenaming.openMappedIndex binding
  audit ``IndexLookupRenaming.openFixedParameters'
  audit ``IndexLookupRenaming.openFixedParameters binding
  audit ``indexSourceFresh_of_declared scope
  audit ``IndexPairInjection.appendFresh
  audit ``IndexParameterSupport.appendFresh
  audit ``BinderValuesBefore.currentFresh scope
  audit ``IndexLookupRenaming.openCurrentIndex (binding ++ scope)
  audit ``IndexOpeningLookup.ofInjectionSupport
  audit ``ParentBinderSupportAlignment.openingLookup
  substitutionMatrix
  extensionControls
  let ctx : Context := {
    env := (← Lean.getEnv).toKernelEnv, lparams := [], safety := .safe, allowPrimitive := false }
  let seeded := { ctx with
    ngen := { namePrefix := `LookupOpeningSeed, idx := 42 }
    lctx := ctx.lctx.mkLocalDecl ⟨.num `LookupOpeningSeed 40⟩ `oldNat (.const ``Nat []) .implicit
      |>.mkLetDecl ⟨.num `LookupOpeningSeed 41⟩ `oldLet (.const ``Nat []) (.lit (.natVal 7)) false }
  for reader in [ctx, seeded, { ctx with ngen := { namePrefix := `OtherLookupOpeningSeed, idx := 71 } },
      { ctx with lparams := [`u] }] do
    fixtures reader
  logInfo "40 dense-reader full registrations preserve deterministic raw paired openings across 44 parent pairs/156 binder steps/four readers"

end InductiveIndexLookupOpeningTest
