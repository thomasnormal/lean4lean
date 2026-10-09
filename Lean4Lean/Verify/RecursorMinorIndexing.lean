import Lean4Lean.Verify.RecursorRuleFields

namespace Lean4Lean.AddInductive
open Lean hiding Environment Exception

theorem RecursorInfoCounts.minorPrefix {types : Array InductiveType} {infos : Array RecInfo}
    (hcounts : RecursorInfoCounts types infos) (index : Nat) :
    ((infos.toList.take index).flatMap (fun info => info.minors.toList)).length =
      recursorMinorOffset types index := by
  have hmap : infos.map (fun info => info.minors.size) = types.map (fun type => type.ctors.length) := by
    apply Array.ext
    · simpa using hcounts.size
    · intro parent hinfo htype
      have hbound : parent < types.size := by simpa using htype
      simpa only [Array.getElem_map, getElem!_pos, hcounts.size, hbound] using hcounts.minors parent hbound
  have hlist := congrArg Array.toList hmap
  simp only [Array.toList_map] at hlist
  simp only [recursorMinorOffset, List.length_flatMap, Array.length_toList, List.map_take]
  rw [hlist]

private theorem flatMap_local {items : List α} (fields : α → List β)
    (parent : Nat) (hparent : parent < items.length) (index : Nat)
    (hindex : index < (fields items[parent]).length) :
    ((items.take parent).flatMap fields).length + index < (items.flatMap fields).length ∧
    (items.flatMap fields)[((items.take parent).flatMap fields).length + index]? =
      (fields items[parent])[index]? := by
  have hsplit : items = items.take parent ++ items[parent] :: items.drop (parent + 1) := by
    rw [List.getElem_cons_drop hparent, List.take_append_drop]
  have hflat : items.flatMap fields = (items.take parent).flatMap fields ++
      fields items[parent] ++ (items.drop (parent + 1)).flatMap fields := by
    calc
      items.flatMap fields = (items.take parent ++ items[parent] :: items.drop (parent + 1)).flatMap fields :=
        congrArg (List.flatMap fields) hsplit
      _ = _ := by simp only [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  rw [hflat]
  constructor
  · simp only [List.length_append]
    omega
  · rw [List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    exact List.getElem?_append_left hindex

def RecursorMinorIndexing (types : Array InductiveType) (infos : Array RecInfo) : Prop :=
  ∀ parent, parent < types.size → ∀ index, index < types[parent]!.ctors.length →
    index < infos[parent]!.minors.size ∧
    recursorMinorOffset types parent + index < (infos.flatMap (·.minors)).size ∧
    (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]? =
      infos[parent]!.minors[index]?

theorem RecursorInfoCounts.minorIndexing {types : Array InductiveType} {infos : Array RecInfo}
    (hcounts : RecursorInfoCounts types infos) : RecursorMinorIndexing types infos := by
  intro parent hparent index hindex
  have hinfo : parent < infos.size := by rw [hcounts.size]; exact hparent
  have hlocal : index < infos[parent]!.minors.size := by rw [hcounts.minors parent hparent]; exact hindex
  obtain ⟨hbound, hlookup⟩ := flatMap_local (fun info : RecInfo => info.minors.toList) parent
    (by simpa using hinfo) index (by simpa [getElem!_pos, hinfo] using hlocal)
  rw [hcounts.minorPrefix parent] at hbound hlookup
  refine ⟨hlocal, ?_, ?_⟩
  · simpa only [← Array.toList_flatMap, Array.length_toList] using hbound
  · simpa only [← Array.toList_flatMap, Array.getElem?_toList, Array.getElem_toList,
      getElem!_pos, hinfo] using hlookup

theorem RecursorMinorIndexing.at {types : Array InductiveType} {infos : Array RecInfo}
    (hindexing : RecursorMinorIndexing types infos) (parent : Nat) (hparent : parent < types.size)
    (index : Nat) (hindex : index < types[parent]!.ctors.length) :
    ∃ minor, infos[parent]!.minors[index]? = some minor ∧
      (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]? = some minor := by
  obtain ⟨hlocal, _, hlookup⟩ := hindexing parent hparent index hindex
  exact ⟨infos[parent]!.minors[index], Array.getElem?_eq_getElem hlocal,
    hlookup.trans (Array.getElem?_eq_getElem hlocal)⟩

theorem RecursorMinorIndexing.getElem! {types : Array InductiveType} {infos : Array RecInfo}
    (hindexing : RecursorMinorIndexing types infos) (parent : Nat) (hparent : parent < types.size)
    (index : Nat) (hindex : index < types[parent]!.ctors.length) :
    (infos.flatMap (·.minors))[recursorMinorOffset types parent + index]! =
      infos[parent]!.minors[index]! := by
  obtain ⟨hlocal, hbound, hlookup⟩ := hindexing parent hparent index hindex
  simpa only [Array.getElem?_eq_getElem hbound, Array.getElem?_eq_getElem hlocal,
    Option.some.injEq, getElem!_pos, hbound, hlocal] using hlookup

theorem InductiveStats.SafeRunMinorOffsets.indexedSourceRules {stats : InductiveStats}
    {nparams numNested : Nat} {types : Array InductiveType} {original root : Context}
    {constructors env : Kernel.Environment}
    (hoffsets : stats.SafeRunMinorOffsets nparams types numNested original root constructors env) :
    ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context),
      ({ root with env := constructors } : Context).HeaderFrame source ∧
      RecursorInfoCounts types infos ∧ RecursorMinorIndexing types infos ∧
      ∀ parent, parent < types.size → ∃ info : RecursorVal,
        env.find? (mkRecName types[parent]!.name) = some (.recInfo info) ∧
        mkRecRules types elimLevel stats parent (infos.map (·.motive)) (infos.flatMap (·.minors))
          (recursorMinorOffset types parent) source =
            .ok (info.rules, recursorMinorOffset types (parent + 1)) := by
  obtain ⟨elimLevel, infos, source, hframe, hcounts, hsource⟩ := hoffsets.sourceRules
  exact ⟨elimLevel, infos, source, hframe, hcounts, hcounts.minorIndexing, hsource⟩

theorem run.safeMinorIndexing (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (ctx : Context) (hsafety : ctx.safety = .safe)
    (hwf : ctx.env.constants.WF) :
    (run nparams types numNested ctx).WF fun env =>
      ∃ (stats : InductiveStats) (root : Context) (constructors : Kernel.Environment),
        stats.SafeRunMinorOffsets nparams types.toArray numNested ctx root constructors env ∧
        ∃ (elimLevel : Level) (infos : Array RecInfo) (source : Context),
          ({ root with env := constructors } : Context).HeaderFrame source ∧
          RecursorInfoCounts types.toArray infos ∧ RecursorMinorIndexing types.toArray infos ∧
          ∀ parent, parent < types.toArray.size → ∃ info : RecursorVal,
            env.find? (mkRecName types.toArray[parent]!.name) = some (.recInfo info) ∧
            mkRecRules types.toArray elimLevel stats parent (infos.map (·.motive)) (infos.flatMap (·.minors))
              (recursorMinorOffset types.toArray parent) source =
                .ok (info.rules, recursorMinorOffset types.toArray (parent + 1)) := by
  refine (run.safeMinorOffsets nparams types numNested ctx hsafety hwf).mono ?_
  rintro env ⟨stats, root, constructors, hoffsets⟩
  exact ⟨stats, root, constructors, hoffsets, hoffsets.indexedSourceRules⟩

end Lean4Lean.AddInductive
