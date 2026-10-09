import Lean4Lean.Verify.InductiveBinderDomains

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception
open ElimNestedInductive (ContextReserved)

def BinderPositionedAt (ctx : Context) (value : Expr) (name : Name) (domain : Expr)
    (bi : BinderInfo) (position : Nat) : Prop :=
  ∃ decl, ctx.lctx.find? value.fvarId! = some decl ∧ decl.toExpr = value ∧
    decl.type = domain ∧ decl.userName = name ∧ decl.binderInfo = bi ∧ decl.index = position

theorem BinderPositionedAt.declared {ctx : Context} {value domain : Expr} {name : Name}
    {bi : BinderInfo} {position : Nat}
    (positioned : BinderPositionedAt ctx value name domain bi position) :
    BinderDeclaredAt ctx value name domain bi := by
  obtain ⟨decl, hlookup, hexpr, htype, hname, hbi, _⟩ := positioned
  exact ⟨decl, hlookup, hexpr, htype, hname, hbi⟩

theorem BinderPositionedAt.mono {original current : Context} {value domain : Expr}
    {name : Name} {bi : BinderInfo} {position : Nat}
    (positioned : BinderPositionedAt original value name domain bi position)
    (hwf : original.lctx.WF) (hframe : original.RecursorScopeFrame current) :
    BinderPositionedAt current value name domain bi position := by
  obtain ⟨decl, hlookup, hexpr, htype, hname, hbi, hindex⟩ := positioned
  exact ⟨decl, hframe.oldLookup hwf hlookup, hexpr, htype, hname, hbi, hindex⟩

theorem BinderPositionedAt.index_eq_of_id_eq {ctx : Context} {left right leftDomain rightDomain : Expr}
    {leftName rightName : Name} {leftBi rightBi : BinderInfo} {leftPosition rightPosition : Nat}
    (leftReceipt : BinderPositionedAt ctx left leftName leftDomain leftBi leftPosition)
    (rightReceipt : BinderPositionedAt ctx right rightName rightDomain rightBi rightPosition)
    (hids : left.fvarId! = right.fvarId!) : leftPosition = rightPosition := by
  obtain ⟨leftDecl, hleft, _, _, _, _, hleftPosition⟩ := leftReceipt
  obtain ⟨rightDecl, hright, _, _, _, _, hrightPosition⟩ := rightReceipt
  rw [hids, hright] at hleft
  obtain rfl := Option.some.inj hleft
  exact hleftPosition.symm.trans hrightPosition

theorem newlyAllocatedBinderPositioned (ctx : Context) (name : Name) (domain : Expr)
    (bi : BinderInfo) (hwf : ctx.lctx.WF) (hreserved : ContextReserved ctx.lctx ctx.ngen) :
    BinderPositionedAt (recursorIndexContext ctx name bi (peelTypeAnnotations domain))
      (.fvar ⟨ctx.ngen.curr⟩) name (peelTypeAnnotations domain) bi ctx.lctx.decls.size := by
  have hframe := Context.RecursorScopeFrame.push ctx hwf hreserved name bi (peelTypeAnnotations domain)
  let decl := LocalDecl.cdecl ctx.lctx.decls.size ⟨ctx.ngen.curr⟩ name
    (peelTypeAnnotations domain) bi .default
  have hmem : decl ∈ (recursorIndexContext ctx name bi (peelTypeAnnotations domain)).lctx.toList := by
    simp only [recursorIndexContext, LocalContext.mkLocalDecl_toList, List.mem_cons]
    exact .inl rfl
  exact ⟨decl, hframe.wf.find?_of_mem hmem, rfl, rfl, rfl, rfl, rfl⟩

def BinderIndexAllocations (ctx : Context) (start : Nat) : List BinderStep → Prop
  | [] => True
  | step :: steps =>
      match step.role with
      | .parameter => BinderIndexAllocations ctx start steps
      | .index => BinderPositionedAt ctx step.value step.name step.localDomain step.bi start ∧
          BinderIndexAllocations ctx (start + 1) steps

theorem BinderIndexAllocations.mono {original current : Context} {start : Nat} {steps : List BinderStep}
    (allocated : BinderIndexAllocations original start steps) (hwf : original.lctx.WF)
    (hframe : original.RecursorScopeFrame current) : BinderIndexAllocations current start steps := by
  induction steps generalizing start with
  | nil => trivial
  | cons step steps ih =>
    cases hrole : step.role with
    | parameter =>
      simp only [BinderIndexAllocations, hrole] at allocated ⊢
      exact ih allocated
    | index =>
      simp only [BinderIndexAllocations, hrole] at allocated ⊢
      exact ⟨allocated.1.mono hwf hframe, ih allocated.2⟩

theorem BinderIndexAllocations.declared {ctx : Context} {start : Nat} {steps : List BinderStep}
    (allocated : BinderIndexAllocations ctx start steps) : BinderStepsIndexDeclared ctx steps := by
  induction steps generalizing start with
  | nil => intro step hstep; cases hstep
  | cons step steps ih =>
    intro next hnext hnextRole
    cases hrole : step.role with
    | parameter =>
      simp only [BinderIndexAllocations, hrole] at allocated
      obtain rfl | hnext := List.mem_cons.mp hnext
      · rw [hrole] at hnextRole
        cases hnextRole
      · exact ih allocated next hnext hnextRole
    | index =>
      simp only [BinderIndexAllocations, hrole] at allocated
      obtain rfl | hnext := List.mem_cons.mp hnext
      · exact allocated.1.declared
      · exact ih allocated.2 next hnext hnextRole

theorem BinderIndexAllocations.positioned {ctx : Context} {start ordinal : Nat}
    {steps : List BinderStep} {value : Expr} (allocated : BinderIndexAllocations ctx start steps)
    (hvalue : (BinderStep.indexValues steps)[ordinal]? = some value) :
    ∃ step ∈ steps, step.role = .index ∧ step.value = value ∧
      BinderPositionedAt ctx step.value step.name step.localDomain step.bi (start + ordinal) := by
  induction steps generalizing start ordinal with
  | nil => cases hvalue
  | cons step steps ih =>
    cases hrole : step.role with
    | parameter =>
      simp only [BinderIndexAllocations, hrole] at allocated
      simp only [BinderStep.indexValues, hrole] at hvalue
      obtain ⟨next, hnext, hnextRole, hnextValue, positioned⟩ := ih allocated hvalue
      exact ⟨next, List.mem_cons_of_mem step hnext, hnextRole, hnextValue, positioned⟩
    | index =>
      simp only [BinderIndexAllocations, hrole] at allocated
      simp only [BinderStep.indexValues, hrole, ↓reduceIte] at hvalue
      cases ordinal with
      | zero =>
        have hhead := Option.some.inj hvalue
        exact ⟨step, List.mem_cons_self, hrole, hhead, allocated.1⟩
      | succ ordinal =>
        simp only [List.getElem?_cons_succ] at hvalue
        obtain ⟨next, hnext, hnextRole, hnextValue, positioned⟩ := ih allocated.2 hvalue
        refine ⟨next, List.mem_cons_of_mem step hnext, hnextRole, hnextValue, ?_⟩
        simpa only [Nat.add_assoc, Nat.add_comm 1 ordinal] using positioned

theorem BinderIndexAllocations.indexIdsNodup {ctx : Context} {start : Nat} {steps : List BinderStep}
    (allocated : BinderIndexAllocations ctx start steps) :
    ((BinderStep.indexValues steps).map Expr.fvarId!).Nodup := by
  induction steps generalizing start with
  | nil => exact List.nodup_nil
  | cons step steps ih =>
    cases hrole : step.role with
    | parameter =>
      simp only [BinderIndexAllocations, hrole] at allocated
      simpa only [BinderStep.indexValues, hrole, BinderRole.noConfusion, ↓reduceIte] using ih allocated
    | index =>
      simp only [BinderIndexAllocations, hrole] at allocated
      simp only [BinderStep.indexValues, hrole, ↓reduceIte, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih allocated.2⟩
      intro hmem
      obtain ⟨value, hvalue, hids⟩ := List.mem_map.mp hmem
      obtain ⟨ordinal, hordinal⟩ := List.mem_iff_getElem?.mp hvalue
      obtain ⟨next, _, _, hnextValue, positioned⟩ := allocated.2.positioned hordinal
      have hsame := allocated.1.index_eq_of_id_eq positioned (by rw [hnextValue, hids])
      omega

def IndexPairInjection (pairs : List (FVarId × FVarId)) : Prop :=
  (pairs.map Prod.fst).Nodup ∧ (pairs.map Prod.snd).Nodup

theorem indexZipProjections (left right : List FVarId) :
    (left.zip right).map Prod.fst = left.take right.length ∧
    (left.zip right).map Prod.snd = right.take left.length := by
  induction left generalizing right with
  | nil => simp
  | cons leftId left ih =>
    cases right with
    | nil => simp
    | cons rightId right =>
      obtain ⟨hleft, hright⟩ := ih right
      simp only [List.zip_cons_cons, List.map_cons, List.length_cons,
        List.take_succ_cons, hleft, hright]
      trivial

theorem indexZipExactProjections {left right : List FVarId} (hlength : left.length = right.length) :
    (left.zip right).map Prod.fst = left ∧ (left.zip right).map Prod.snd = right := by
  obtain ⟨hleft, hright⟩ := indexZipProjections left right
  constructor
  · simpa only [← hlength, List.take_length] using hleft
  · simpa only [hlength, List.take_length] using hright

theorem IndexPairInjection.of_zip {left right : List FVarId}
    (hleft : left.Nodup) (hright : right.Nodup) : IndexPairInjection (left.zip right) := by
  obtain ⟨hfst, hsnd⟩ := indexZipProjections left right
  exact ⟨hfst ▸ List.Nodup.sublist (List.take_sublist right.length left) hleft,
    hsnd ▸ List.Nodup.sublist (List.take_sublist left.length right) hright⟩

private theorem projectionUnique {pairs : List (FVarId × FVarId)}
    {left right : FVarId × FVarId} (projection : FVarId × FVarId → FVarId)
    (hnodup : (pairs.map projection).Nodup) (hleft : left ∈ pairs) (hright : right ∈ pairs)
    (hsame : projection left = projection right) : left = right := by
  induction pairs with
  | nil => cases hleft
  | cons pair pairs ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnodup
    obtain hleftEq | hleftTail := List.mem_cons.mp hleft
    · subst left
      obtain hrightEq | hrightTail := List.mem_cons.mp hright
      · exact hrightEq.symm
      · exact False.elim (hnot (List.mem_map.mpr ⟨right, hrightTail, hsame.symm⟩))
    · obtain hrightEq | hrightTail := List.mem_cons.mp hright
      · subst right
        exact False.elim (hnot (List.mem_map.mpr ⟨left, hleftTail, hsame⟩))
      · exact ih htail hleftTail hrightTail

theorem IndexPairInjection.functional {pairs : List (FVarId × FVarId)}
    {left right₁ right₂ : FVarId} (injection : IndexPairInjection pairs)
    (hfirst : (left, right₁) ∈ pairs) (hsecond : (left, right₂) ∈ pairs) : right₁ = right₂ :=
  congrArg Prod.snd (projectionUnique Prod.fst injection.1 hfirst hsecond rfl)

theorem IndexPairInjection.injective {pairs : List (FVarId × FVarId)}
    {left₁ left₂ right : FVarId} (injection : IndexPairInjection pairs)
    (hfirst : (left₁, right) ∈ pairs) (hsecond : (left₂, right) ∈ pairs) : left₁ = left₂ :=
  congrArg Prod.fst (projectionUnique Prod.snd injection.2 hfirst hsecond rfl)

end Lean4Lean.AddInductive
