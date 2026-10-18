module

public import SpectreClusters.StageDActualTileHierarchy

@[expose] public section


namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch
open StageA

theorem nativeBlocks_nested (C : NativeHierarchy.ParentOccurrenceTheorem)
    (n : Nat) (F : NativeHierarchy.LegalField) (x : Position) :
    ∃ y, ∀ p ∈ NativeHierarchy.blocks C n F x,
      p ∈ NativeHierarchy.blocks C (n+1) F y := by
  induction n generalizing F x with
  | zero =>
    obtain ⟨y,hy⟩ := NativeHierarchy.blocks_cover C 1 F x
    refine ⟨y,?_⟩
    intro p hp
    have he : p = x := List.mem_singleton.mp hp
    simpa only [he] using hy
  | succ n ih =>
    obtain ⟨y,hy⟩ := ih (NativeHierarchy.next C F) x
    refine ⟨y,?_⟩
    intro p hp
    obtain ⟨a,ha,hpa⟩ := (NativeHierarchy.mem_refine C F _ p).mp hp
    exact (NativeHierarchy.mem_refine C F _ p).mpr ⟨a,hy a ha,hpa⟩

theorem actualHierarchyBlock_nested (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hD : FinalClusterCaptures) {f : Cell → ClusterPlacement}
    (hf : ValidClusterGridField f) (base : Cell) (n : Nat) (x : Position) :
    ∃ y, ∀ p ∈ actualHierarchyBlock C hD hf base n x,
      p ∈ actualHierarchyBlock C hD hf base (n+1) y := by
  obtain ⟨y,hy⟩ := nativeBlocks_nested C n (actualLegalField hD hf base) x
  refine ⟨y,?_⟩
  intro p hp
  obtain ⟨v,hv,he⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨v,hy v hv,he⟩

theorem actualHierarchyTiles_nested (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : FinalCaptures) (hD : FinalClusterCaptures) (f : Cell → HTPlacement)
    (hf : ValidGridField f) (hs : SparseTurtles f) (base : Cell) (n : Nat) (x : Position) :
    ∃ y, ∀ p ∈ actualHierarchyTiles C hA hD f hf hs base n x,
      p ∈ actualHierarchyTiles C hA hD f hf hs base (n+1) y := by
  obtain ⟨y,hy⟩ := actualHierarchyBlock_nested C hD
    (extractedClusterField_valid hA f hf hs) base n x
  refine ⟨y,?_⟩
  intro p hp
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  exact List.mem_flatMap.mpr ⟨q,hy q hq,hp⟩

end SpectreClusters.StageD
