module

public import SpectreClusters.StageAFieldNeighbors
public import SpectreClusters.GridReductionWindowStages

@[expose] public section


/-! Genuine field support and literal cluster ownership. No finite row
membership is assumed implicitly: the final capture theorem is an explicit
parameter here, discharged by StageAComplete in the final assembly. -/
namespace SpectreClusters.StageA

abbrev FinalCaptures : Prop := GridReductionWindows.Captures rawWordAt (keptIds 2)
  GridReductionWindowBinding.encode

theorem actual_neighbor_support (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (kind : HTKind)
    (hr : RootOwned f (canonicalRoot kind)) (i n : Nat)
    (hword : rawWordAt kind i = wordOf f kind)
    (hn : n ∈ rawWordAt kind i) (ha : alignmentValidB kind n = true) :
    ∃ j ∈ keptIds 2 (candidateAt kind n).kind,
      rawWordAt (candidateAt kind n).kind j =
        wordOf (normalizeField f (candidateAt kind n)) (candidateAt kind n).kind ∧
      supportB kind (rawWordAt kind i) n
        (rawWordAt (candidateAt kind n).kind j) = true := by
  have he := GridReductionWindowBinding.encoding_sound field_mem_candidates
  have hp : RootOwned f (candidateAt kind n) := (he f hf kind hr).2 n (show n ∈ wordOf f kind from hword ▸ hn)
  have hvalid := normalizeField_valid f hf (candidateAt kind n)
  have hroot := normalizeField_rootOwned f (candidateAt kind n) hp
  obtain ⟨j,hj,hjword⟩ := hcaptures (normalizeField f (candidateAt kind n))
    hvalid (candidateAt kind n).kind hroot
  refine ⟨j,hj,hjword,?_⟩
  exact GridReductionWindows.supportB_of_encodes GridReductionWindowBinding.data
    f kind (rawWordAt kind i) n (rawWordAt (candidateAt kind n).kind j)
    (hword ▸ (he f hf kind hr).1)
    (hjword ▸ (he (normalizeField f (candidateAt kind n)) hvalid
      (candidateAt kind n).kind hroot).1)
    (GridReductionWindowBinding.alignment_sound kind n ha)

/-- Ownership survives denormalization to the original field. -/
theorem owned_of_normalized_owned (f : Cell → HTPlacement) (root p : HTPlacement)
    (hp : RootOwned (normalizeField f root) p) :
    RootOwned f (movePlacement root.turn root.center p) := by
  intro c hc
  rw [placementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have h := congrArg (movePlacement root.turn root.center) (hp d hd)
  rw [denormalizeField_apply] at h
  exact h

/-- The literal pieces of a directly moved cluster, preserving every tile pose. -/
def clusterPiecesAt (k : ClusterKind) (root : HTPlacement) : List HTPlacement :=
  (clusterPieces k).map (movePlacement root.turn root.center)

def ClusterOwned (f : Cell → HTPlacement) (k : ClusterKind) (root : HTPlacement) : Prop :=
  root.kind = .turtle ∧ ∀ p ∈ clusterPiecesAt k root, RootOwned f p

/-- A genuine exceptional turtle occurrence owns the literal T6H core.
This conclusion refers to every individual tile occurrence, not only its cells. -/
theorem turtle_special_owns_t6h (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) (hr : RootOwned f root) (hk : root.kind = .turtle)
    (hword : rawWordAt .turtle 0 = wordOf (normalizeField f root) .turtle) :
    ClusterOwned f .t6h root := by
  refine ⟨hk,?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  apply owned_of_normalized_owned f root q
  have hroot : RootOwned (normalizeField f root) (canonicalRoot .turtle) := by
    simpa only [hk,originRoot,canonicalRoot] using normalizeField_rootOwned f root hr
  rcases List.mem_cons.mp ((turtle_special_literal q).mpr hq) with hqroot | hqn
  · exact hqroot ▸ hroot
  · exact ((row_neighbors_iff_fieldNeighbor (normalizeField f root)
      (normalizeField_valid f hf root) .turtle hroot 0 hword q).mp hqn).1

end SpectreClusters.StageA
