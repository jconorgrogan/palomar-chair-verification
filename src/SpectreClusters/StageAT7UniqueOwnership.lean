module

public import SpectreClusters.StageAT7OverlapAssembly
public import SpectreClusters.ClusterOwnershipTransport

@[expose] public section


/-! Occurrence-preserving uniqueness of genuine T7H clusters. All relative
poses follow from a shared literal tile and all26 nonidentity candidates
are rejected by checked finite actual-row refutation trees. -/
namespace SpectreClusters.StageA

theorem t7_canonical_shared_tile_root_eq (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (other : HTPlacement)
    (hother : ClusterOwned f .t7h other) (hfirst : PatchOwned f (clusterPieces .t7h))
    (p : HTPlacement) (hp : p ∈ clusterPieces .t7h)
    (hpo : p ∈ clusterPiecesAt .t7h other) : other = canonicalRoot .turtle := by
  obtain ⟨b,hb,hbp⟩ := List.mem_map.mp hpo
  have hkind : p.kind = b.kind := (congrArg HTPlacement.kind hbp).symm
  have halign : alignTurtle p b = other := by
    rw [← hbp]
    exact alignTurtle_moved other b hother.1
  rcases t7SharedAlignment_complete p b hp hb hkind with he | hmem
  · exact halign.symm.trans he
  · rw [halign] at hmem
    exfalso
    apply t7_other_roots_refuted hcaptures f hf other hmem
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hfirst q hq
    · exact hother.2 q hq

/-- A shared tile occurrence determines the entire T7H cluster root. -/
theorem t7_shared_tile_root_unique (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (r s : HTPlacement)
    (hr : ClusterOwned f .t7h r) (hs : ClusterOwned f .t7h s)
    (p : HTPlacement) (hpr : p ∈ clusterPiecesAt .t7h r)
    (hps : p ∈ clusterPiecesAt .t7h s) : r = s := by
  let k := turnNeg r.turn
  let t := inverseTranslation r.turn r.center
  let g := moveField k t f
  have hv : ValidGridField g := moveField_valid k t f hf
  have hr' := clusterOwned_moved .t7h k t f r hr
  have hs' := clusterOwned_moved .t7h k t f s hs
  have hcanon : movePlacement k t r = canonicalRoot .turtle := by
    have h := normalize_root r
    simpa only [hr.1,originRoot,canonicalRoot] using h
  rw [hcanon] at hr'
  have hfirst : PatchOwned g (clusterPieces .t7h) := by
    simpa only [g,PatchOwned,clusterPiecesAt_canonical] using hr'.2
  have hpr' : movePlacement k t p ∈ clusterPiecesAt .t7h (movePlacement k t r) := by
    rw [clusterPiecesAt_moved]
    exact List.mem_map.mpr ⟨p,hpr,rfl⟩
  rw [hcanon,clusterPiecesAt_canonical] at hpr'
  have hps' : movePlacement k t p ∈ clusterPiecesAt .t7h (movePlacement k t s) := by
    rw [clusterPiecesAt_moved]
    exact List.mem_map.mpr ⟨p,hps,rfl⟩
  have he := t7_canonical_shared_tile_root_eq hcaptures g hv (movePlacement k t s)
    hs' hfirst (movePlacement k t p) hpr' hps'
  exact movePlacement_injective k t (hcanon.trans he.symm)

def clusterCellsAt (k : ClusterKind) (root : HTPlacement) : List Cell :=
  (clusterPiecesAt k root).flatMap placementCells

/-- Distinct genuine T7H roots have disjoint cell sets, not merely distinct
names or independently non-overlapping literal templates. -/
theorem t7_distinct_roots_disjoint (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (r s : HTPlacement)
    (hr : ClusterOwned f .t7h r) (hs : ClusterOwned f .t7h s) (hne : r ≠ s) :
    DisjointCells (clusterCellsAt .t7h r) (clusterCellsAt .t7h s) := by
  intro c hcr hcs
  obtain ⟨p,hpr,hcp⟩ := List.mem_flatMap.mp hcr
  obtain ⟨q,hqs,hcq⟩ := List.mem_flatMap.mp hcs
  have he : p = q := (hr.2 p hpr c hcp).symm.trans (hs.2 q hqs c hcq)
  subst q
  exact hne (t7_shared_tile_root_unique hcaptures f hf r s hr hs p hpr hqs)

end SpectreClusters.StageA
