import Lean4Lean.Verify.InductiveRestorationRules

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open private Lean.Kernel.Environment.add from Lean.Environment
open private Lean4Lean.AddInductive.addFresh from Lean4Lean.Verify.ConstructorMetadata
open private Lean4Lean.AddInductive.bindWF Lean4Lean.AddInductive.readWF
  from Lean4Lean.Verify.InductiveStats

private theorem registerHeaderNames (infos : List InductiveVal) (env : Environment)
    (allowPrimitive : Bool) (hmap : env.constants.WF) :
    (infos.foldlM (fun (current : Environment) (info : InductiveVal) => do
      current.checkName info.name allowPrimitive
      pure (current.add (.inductInfo info))) env).WF fun _ =>
      (infos.map (fun info : InductiveVal => info.name)).Nodup ∧
        ∀ info ∈ infos, env.find? info.name = none := by
  induction infos generalizing env with
  | nil => exact .pure ⟨by simp, by simp⟩
  | cons info infos ih =>
    simp only [List.foldlM_cons, bind_assoc, pure_bind]
    refine (Lean4Lean.checkName.WF env info.name allowPrimitive).bind ?_
    rintro _ ⟨hfresh, _⟩
    obtain ⟨hnext, hself, hpreserve⟩ := Lean4Lean.AddInductive.addFresh env (.inductInfo info) hmap hfresh
    refine (ih _ hnext).mono ?_
    rintro _ ⟨hnodup, habsent⟩
    refine ⟨List.nodup_cons.mpr ⟨?_, hnodup⟩, ?_⟩
    · intro hmem
      obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
      have hnone := habsent other hother
      rw [heq] at hnone
      have hcontra := hself.symm.trans hnone
      cases hcontra
    · intro other hother
      rcases List.mem_cons.mp hother with rfl | hother
      · simpa only [Kernel.Environment.find?, hmap.find?'_eq_find?] using hfresh
      · cases hlookup : env.find? other.name with
        | none => rfl
        | some constant =>
          have hnone := habsent other hother
          rw [hpreserve other.name constant hlookup] at hnone
          cases hnone

theorem declareInductiveTypes.namesNodup (stats : InductiveStats) (nparams : Nat)
    (types : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (ctx : Context) (hmap : ctx.env.constants.WF) (hsize : stats.nindices.size = types.size) :
    (declareInductiveTypes stats nparams types numNested isUnsafe ctx).WF fun _ =>
      (types.toList.map (·.name)).Nodup := by
  let infos := types.zipWith (bs := stats.nindices) fun type numIndices =>
    declareInductiveTypes.metadataVal stats nparams types numNested isUnsafe ctx.lparams type numIndices
  have hnames : infos.map (·.name) = types.map (·.name) := by
    apply Array.ext
    · simp only [infos, Array.size_map, Array.size_zipWith, hsize, Nat.min_self]
    · intro index hinfo htype
      simp only [infos, Array.getElem_map, Array.getElem_zipWith, declareInductiveTypes.metadataVal]
  have hlist := congrArg Array.toList hnames
  simp only [Array.toList_map] at hlist
  have haction : declareInductiveTypes stats nparams types numNested isUnsafe ctx =
      infos.toList.foldlM (fun (current : Environment) (info : InductiveVal) => do
        current.checkName info.name ctx.allowPrimitive
        pure (current.add (.inductInfo info))) ctx.env := by
    unfold declareInductiveTypes
    rw [← Array.foldlM_toList]
    rfl
  rw [haction]
  exact (registerHeaderNames infos.toList ctx.env ctx.allowPrimitive hmap).mono fun _ hnames => hlist ▸ hnames.1

theorem run.datatypeNamesNodup (nparams : Nat) (types : List InductiveType) (numNested : Nat)
    (ctx : Context) (hmap : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun _ => (types.map (·.name)).Nodup := by
  unfold run
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.readWF
  dsimp only
  apply Lean4Lean.AddInductive.bindWF
  intro _
  apply checkInductiveTypes.frameHeaderSizes
  intro stats current hsizes hframe
  have hcurrent : current.env.constants.WF := by simpa only [hframe.env] using hmap
  refine (declareInductiveTypes.namesNodup stats nparams types.toArray numNested _ current hcurrent hsizes.1).bind ?_
  intro headers hnames result hresult
  simpa only [List.toList_toArray] using hnames

end AddInductive

theorem InductiveNamePrefix.suffixNotMem {original rewritten : Array InductiveType}
    (hprefix : InductiveNamePrefix original rewritten) (hnodup : (rewritten.toList.map (·.name)).Nodup)
    (index : Nat) (hindex : index < original.size) :
    original[index]!.name ∉ (rewritten.toList.map (·.name)).drop original.size := by
  let names := rewritten.toList.map (·.name)
  have hrewritten := Nat.lt_of_lt_of_le hindex hprefix.size
  have hlookup : names[index]? = some original[index]!.name := by
    simpa only [names, List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hrewritten,
      Option.map_some, getElem!_pos, hrewritten] using congrArg some (hprefix.names index hindex)
  have htake : original[index]!.name ∈ names.take original.size :=
    List.mem_of_getElem? ((List.getElem?_take_of_lt hindex).trans hlookup)
  have happend : (names.take original.size ++ names.drop original.size).Nodup := by
    simpa only [List.take_append_drop] using hnodup
  intro hmem
  exact (List.nodup_append.mp happend).2.2 _ htake _ hmem rfl

private theorem auxRecMapFrame (names : List Name) (mainName : Name) (nextIndex : Nat)
    (oldNames : Array Name) (nameMap : NameMap Name) (key : Name)
    (hnot : key ∉ names.map mkRecName) :
    (forIn (m := Id) names (⟨nextIndex, oldNames, nameMap⟩ : MProd Nat (MProd (Array Name) (NameMap Name)))
      (fun name current =>
        pure (.yield ⟨current.fst + 1, current.snd.fst.push (mkRecName name),
          current.snd.snd.insert (mkRecName name) ((mkRecName mainName).appendIndexAfter current.fst)⟩))).run.snd.snd.find? key =
      nameMap.find? key := by
  induction names generalizing nextIndex oldNames nameMap with
  | nil => rfl
  | cons name names ih =>
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih (hnot := fun hmem => hnot (List.mem_cons_of_mem _ hmem))]
    have hne : mkRecName name ≠ key := by
      intro heq
      exact hnot (by simp only [List.map_cons, List.mem_cons]; exact Or.inl heq.symm)
    simp only [NameMap.find?, NameMap.insert, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert,
      Std.LawfulEqCmp.compare_eq_iff_eq, if_neg hne]

theorem mkAuxRecNameMap.find?_eq_none (env : Environment) (types : List InductiveType) (key : Name)
    (hnot : key ∉ (mkAuxRecNameMap env types).1) :
    (mkAuxRecNameMap env types).2.find? key = none := by
  cases types with
  | nil => exact Std.TreeMap.getElem?_emptyc
  | cons type types =>
    generalize hget : env.find? type.name = found
    cases found with
    | none => simpa only [mkAuxRecNameMap, hget] using (Std.TreeMap.getElem?_emptyc (a := key) (β := Name))
    | some constant =>
      cases constant with
      | inductInfo info =>
        have hnames := mkAuxRecNameMap.names env type types info hget
        unfold mkAuxRecNameMap
        simp only [hget]
        split
        · rename_i hlength
          have hnot' : key ∉ (info.all.drop (type :: types).length).map mkRecName := by
            simpa only [hnames, if_pos hlength] using hnot
          simpa only [pure_bind] using (auxRecMapFrame (info.all.drop (type :: types).length)
            type.name 1 #[] {} key hnot').trans (by
              change ({} : Std.TreeMap Name Name Name.quickCmp)[key]? = none
              exact Std.TreeMap.getElem?_emptyc)
        · exact Std.TreeMap.getElem?_emptyc
      | _ => simpa only [mkAuxRecNameMap, hget] using (Std.TreeMap.getElem?_emptyc (a := key) (β := Name))

theorem mkAuxRecNameMap.getD_eq_self (env : Environment) (types : List InductiveType) (key : Name)
    (hnot : key ∉ (mkAuxRecNameMap env types).1) :
    (mkAuxRecNameMap env types).2.getD key key = key := by
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  have hnone := mkAuxRecNameMap.find?_eq_none env types key hnot
  exact congrArg (fun found : Option Name => found.getD key) hnone

end Lean4Lean
