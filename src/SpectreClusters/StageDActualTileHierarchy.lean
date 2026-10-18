module

public import SpectreClusters.StageDActualHierarchyBoundary

@[expose] public section


/-! Source-correct finite tile blocks for every level of the actual hierarchy.
Every listed H/T tile is owned by the original field; every owned tile lies in
exactly one block at each level. No geometric tile is introduced by the chart. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership
open StageA

def clusterPlacementTiles (q : ClusterPlacement) : List HTPlacement :=
  (clusterPieces q.kind).map (movePlacement q.turn q.center)

theorem extracted_cluster_has_root (hA : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : SparseTurtles f)
    (q : ActualCluster (extractedClusterField hA f hf hs)) :
    ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ q.val = assignedClusterPlacement f r := by
  obtain ⟨c,hc⟩ := cluster_owned_represented _ q.val q.property
  have hr := assignedRoot_spec hA f hf hs c
  exact ⟨assignedRoot hA f hf hs c,hr.1,hr.2.1,hc.symm⟩

theorem extracted_cluster_tiles_owned (hA : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : SparseTurtles f)
    (q : ActualCluster (extractedClusterField hA f hf hs))
    (p : HTPlacement) (hp : p ∈ clusterPlacementTiles q.val) : RootOwned f p := by
  obtain ⟨r,hr,hk,he⟩ := extracted_cluster_has_root hA f hf hs q
  rw [he] at hp
  exact (sparse_assigned_cluster_owned hA f hf hs r hr hk).2 p hp

theorem extracted_cluster_tiles_cover (hA : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : SparseTurtles f)
    (p : HTPlacement) (hp : RootOwned f p) :
    ∃ q : ActualCluster (extractedClusterField hA f hf hs), p ∈ clusterPlacementTiles q.val := by
  obtain ⟨r,hr,hk,hp,_⟩ := sparse_owned_tile_unique_cluster hA f hf hs p hp
  exact ⟨⟨assignedClusterPlacement f r,extractedClusterField_owns hA f hf hs r hr hk⟩,hp⟩

theorem extracted_cluster_tiles_disjoint (hA : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : SparseTurtles f)
    (q r : ActualCluster (extractedClusterField hA f hf hs)) (p : HTPlacement)
    (hq : p ∈ clusterPlacementTiles q.val) (hr : p ∈ clusterPlacementTiles r.val) : q = r := by
  obtain ⟨a,ha,hka,heqa⟩ := extracted_cluster_has_root hA f hf hs q
  obtain ⟨b,hb,hkb,herb⟩ := extracted_cluster_has_root hA f hf hs r
  rw [heqa] at hq
  rw [herb] at hr
  have he := sparse_assigned_tile_unique hA f hf hs a b ha hka hb hkb p hq hr
  apply Subtype.ext
  rw [heqa,herb,he]

noncomputable def actualHierarchyTiles (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : FinalCaptures) (hD : FinalClusterCaptures) (f : Cell → HTPlacement)
    (hf : ValidGridField f) (hs : SparseTurtles f) (base : Cell) (n : Nat) (x : Position) :
    List HTPlacement :=
  (actualHierarchyBlock C hD (extractedClusterField_valid hA f hf hs) base n x).flatMap
    (fun q => clusterPlacementTiles q.val)

theorem actualHierarchyTiles_owned (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : FinalCaptures) (hD : FinalClusterCaptures) (f : Cell → HTPlacement)
    (hf : ValidGridField f) (hs : SparseTurtles f) (base : Cell) (n : Nat) (x : Position)
    (p : HTPlacement) (hp : p ∈ actualHierarchyTiles C hA hD f hf hs base n x) :
    RootOwned f p := by
  obtain ⟨q,_,hqp⟩ := List.mem_flatMap.mp hp
  exact extracted_cluster_tiles_owned hA f hf hs q p hqp

theorem actualHierarchyTiles_cover (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : FinalCaptures) (hD : FinalClusterCaptures) (hh : HaloOrderBinding)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hs : SparseTurtles f)
    (base : Cell) (n : Nat) (p : HTPlacement) (hp : RootOwned f p) :
    ∃ x, p ∈ actualHierarchyTiles C hA hD f hf hs base n x := by
  obtain ⟨q,hq⟩ := extracted_cluster_tiles_cover hA f hf hs p hp
  obtain ⟨x,hx⟩ := actualHierarchyBlock_cover C hD hh
    (extractedClusterField_valid hA f hf hs) base n q
  exact ⟨x,List.mem_flatMap.mpr ⟨q,hx,hq⟩⟩

theorem actualHierarchyTiles_disjoint (C : NativeHierarchy.ParentOccurrenceTheorem)
    (hA : FinalCaptures) (hD : FinalClusterCaptures) (f : Cell → HTPlacement)
    (hf : ValidGridField f) (hs : SparseTurtles f) (base : Cell) (n : Nat)
    (x y : Position) (p : HTPlacement)
    (hx : p ∈ actualHierarchyTiles C hA hD f hf hs base n x)
    (hy : p ∈ actualHierarchyTiles C hA hD f hf hs base n y) : x = y := by
  obtain ⟨q,hqx,hpq⟩ := List.mem_flatMap.mp hx
  obtain ⟨r,hry,hpr⟩ := List.mem_flatMap.mp hy
  have he := extracted_cluster_tiles_disjoint hA f hf hs q r p hpq hpr
  subst r
  exact actualHierarchyBlock_disjoint C hD (extractedClusterField_valid hA f hf hs)
    base n x y q hqx hry

end SpectreClusters.StageD
