module

public import SpectreClusters.StageAPhasePropagation
public import SpectreClusters.StageAT8Forcing
public import SpectreClusters.ClusterAssignment

@[expose] public section


/-! Sparse-turtle fields have actual literal T7H cores and T8H footprints.
The canonical assignment covers every original tile and owns every assigned
tile. Disjointness is supplied separately by the T7H refutation packet. -/
namespace SpectreClusters.StageA

theorem sparse_turtle_word (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle) :
    rawWordAt .turtle 0 = wordOf (normalizeField f root) .turtle := by
  have hv := normalizeField_valid f hf root
  have hn := normalizeField_rootOwned f root hr
  obtain ⟨i,hi,hword⟩ := hcaptures (normalizeField f root) hv root.kind hn
  have hsp := (sparseTurtlesAt_normalized_iff f root).mpr (hsparse root hr)
  have hb := (row_sparseTurtles_iff (normalizeField f root) hv root.kind hn i hi hword).mp hsp
  rw [hk] at hb hword
  have hi0 : i = 0 := by simpa [sparseTurtlesRow] using hb
  subst i
  exact hword

theorem sparse_turtle_owns_t7h (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle) :
    ClusterOwned f .t7h root :=
  turtle_special_owns_t7h hcaptures f hf root hr hk (sparse_turtle_word hcaptures f hf hsparse root hr hk)

theorem sparse_turtle_owns_t8h_footprint (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle) :
    ClusterOwned f .t8h root :=
  turtle_special_owns_t8h_footprint hcaptures f hf root hr hk
    (sparse_turtle_word hcaptures f hf hsparse root hr hk)

theorem turtle_root_mem_t7h (root : HTPlacement) (hk : root.kind = .turtle) :
    root ∈ clusterPiecesAt .t7h root := by
  have h0 : canonicalRoot .turtle ∈ clusterPieces .t7h := by decide
  have he : movePlacement root.turn root.center (canonicalRoot .turtle) = root := by
    simpa only [hk,originRoot,canonicalRoot] using movePlacement_originRoot root
  exact List.mem_map.mpr ⟨canonicalRoot .turtle,h0,he⟩

/-- Every original tile lies in a footprint attached to an actually owned
sparse turtle. No finite-window coverage callback is left as a premise. -/
theorem sparse_owned_tile_footprint_cover (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (p : HTPlacement) (hp : RootOwned f p) :
    ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ p ∈ clusterPiecesAt .t8h r := by
  cases hk : p.kind with
  | turtle => exact ⟨p,hp,hk,t7_piece_mem_t8 p p (turtle_root_mem_t7h p hk)⟩
  | hat =>
    let g := normalizeField f p
    have hv : ValidGridField g := normalizeField_valid f hf p
    have hn : RootOwned g (canonicalRoot .hat) := by
      simpa only [hk,originRoot,canonicalRoot] using normalizeField_rootOwned f p hp
    obtain ⟨i,hi,hword⟩ := hcaptures g hv .hat hn
    have hsp : SparseTurtlesAt g (canonicalRoot .hat) := by
      simpa only [hk,originRoot,canonicalRoot] using
        (sparseTurtlesAt_normalized_iff f p).mpr (hsparse p hp)
    have hb := (row_sparseTurtles_iff g hv .hat hn i hi hword).mp hsp
    have hne : i ≠ 210 := by simpa [sparseTurtlesRow] using hb
    obtain ⟨r,hr,hrk,hcover⟩ := regular_hat_has_turtle_cover hcaptures g hv hn i hi hne hword
    refine ⟨movePlacement p.turn p.center r,owned_of_normalized_owned f p r hr,hrk,?_⟩
    have he : movePlacement p.turn p.center (canonicalRoot .hat) = p := by
      simpa only [hk,originRoot,canonicalRoot] using movePlacement_originRoot p
    rw [clusterPiecesAt_moved]
    exact List.mem_map.mpr ⟨canonicalRoot .hat,hcover,he⟩

/-- Every actual tile is assigned to an actual turtle-rooted T7H or T8H
cluster by the intrinsic extra-hat rule. Uniqueness is proved separately. -/
theorem sparse_owned_tile_assigned_cover (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (p : HTPlacement) (hp : RootOwned f p) :
    ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ p ∈ assignedPieces f r := by
  classical
  obtain ⟨r,hr,hrk,hcover⟩ := sparse_owned_tile_footprint_cover hcaptures f hf hsparse p hp
  rcases t8_piece_core_or_extra r p hcover with hcore | he
  · exact ⟨r,hr,hrk,core_piece_assigned f r p hcore⟩
  · by_cases hclaimed : ExtraCovered f r
    · obtain ⟨s,hs,hsk,hmem⟩ := hclaimed
      exact ⟨s,hs,hsk,core_piece_assigned f s p (he.symm ▸ hmem)⟩
    · refine ⟨r,hr,hrk,?_⟩
      simpa only [assignedPieces,assignedKind,if_neg hclaimed] using hcover

theorem sparse_assigned_cluster_owned (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle) :
    ClusterOwned f (assignedKind f root) root := by
  have ht := sparse_turtle_owns_t8h_footprint hcaptures f hf hsparse root hr hk
  refine ⟨hk,?_⟩
  intro p hp
  exact ht.2 p (assigned_piece_mem_t8 f root p hp)

noncomputable def assignedCells (f : Cell → HTPlacement) (root : HTPlacement) : List Cell :=
  (assignedPieces f root).flatMap placementCells

theorem sparse_all_cells_covered (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (hsparse : SparseTurtles f) (c : Cell) :
    ∃ r, RootOwned f r ∧ r.kind = .turtle ∧ c ∈ assignedCells f r := by
  obtain ⟨r,hr,hrk,hmem⟩ := sparse_owned_tile_assigned_cover hcaptures f hf hsparse
    (f c) (GridReduction.field_rootOwned f hf c)
  exact ⟨r,hr,hrk,List.mem_flatMap.mpr ⟨f c,hmem,(hf c).1⟩⟩

end SpectreClusters.StageA
