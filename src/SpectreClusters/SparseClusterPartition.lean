module

public import SpectreClusters.SparseClusterOwnership
public import SpectreClusters.StageAT7UniqueOwnership

@[expose] public section


/-! Genuine whole-grid cluster partition in the sparse-turtle phase. Every
cell is covered, every assigned tile is an original field occurrence, and
distinct turtle roots own disjoint assigned clusters. -/
namespace SpectreClusters.StageA

theorem sparse_unique_core_ownership (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f) :
    UniqueCoreOwnership f := by
  intro r s hr hkr hs hks p hpr hps
  exact t7_shared_tile_root_unique hcaptures f hf r s
    (sparse_turtle_owns_t7h hcaptures f hf hsparse r hr hkr)
    (sparse_turtle_owns_t7h hcaptures f hf hsparse s hs hks) p hpr hps

theorem sparse_assigned_tile_unique (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (r s : HTPlacement) (hr : RootOwned f r) (hkr : r.kind = .turtle)
    (hs : RootOwned f s) (hks : s.kind = .turtle) (p : HTPlacement)
    (hpr : p ∈ assignedPieces f r) (hps : p ∈ assignedPieces f s) : r = s :=
  assigned_piece_unique_of_core_unique f (sparse_unique_core_ownership hcaptures f hf hsparse)
    r s hr hkr hs hks p hpr hps

theorem sparse_owned_tile_unique_cluster (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (p : HTPlacement) (hp : RootOwned f p) :
    ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ p ∈ assignedPieces f r ∧
      ∀ s, RootOwned f s → s.kind = .turtle → p ∈ assignedPieces f s → r = s := by
  obtain ⟨r,hr,hrk,hpr⟩ := sparse_owned_tile_assigned_cover hcaptures f hf hsparse p hp
  exact ⟨r,hr,hrk,hpr,fun s hs hsk hps =>
    sparse_assigned_tile_unique hcaptures f hf hsparse r s hr hrk hs hsk p hpr hps⟩

theorem sparse_assigned_cells_disjoint (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (r s : HTPlacement) (hr : RootOwned f r) (hkr : r.kind = .turtle)
    (hs : RootOwned f s) (hks : s.kind = .turtle) (hne : r ≠ s) :
    DisjointCells (assignedCells f r) (assignedCells f s) := by
  intro c hcr hcs
  obtain ⟨p,hpr,hcp⟩ := List.mem_flatMap.mp hcr
  obtain ⟨q,hqs,hcq⟩ := List.mem_flatMap.mp hcs
  have hor := sparse_assigned_cluster_owned hcaptures f hf hsparse r hr hkr
  have hos := sparse_assigned_cluster_owned hcaptures f hf hsparse s hs hks
  have he : p = q := (hor.2 p hpr c hcp).symm.trans (hos.2 q hqs c hcq)
  subst q
  exact hne (sparse_assigned_tile_unique hcaptures f hf hsparse r s hr hkr hs hks p hpr hqs)

def ValidAssignedClusterPartition (f : Cell → HTPlacement) : Prop :=
  (∀ c, ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ c ∈ assignedCells f r) ∧
  (∀ r, RootOwned f r → r.kind = .turtle → ClusterOwned f (assignedKind f r) r) ∧
  (∀ r s, RootOwned f r → r.kind = .turtle → RootOwned f s → s.kind = .turtle → r ≠ s →
    DisjointCells (assignedCells f r) (assignedCells f s))

theorem sparse_assigned_cluster_partition (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f) :
    ValidAssignedClusterPartition f := by
  exact ⟨sparse_all_cells_covered hcaptures f hf hsparse,
    sparse_assigned_cluster_owned hcaptures f hf hsparse,
    fun r s hr hkr hs hks hne => sparse_assigned_cells_disjoint hcaptures f hf hsparse
      r s hr hkr hs hks hne⟩

end SpectreClusters.StageA
