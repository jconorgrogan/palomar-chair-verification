module

public import SpectreClusters.StageAPhaseChecks
public import SpectreClusters.StageAPhaseMeaning
public import SpectreClusters.StageAActualSupport
public import SpectreClusters.GridCellConnected

@[expose] public section


/-! Local checked phase consistency propagates through the entire kite
contact graph. The capture parameter is discharged by StageAComplete. -/
namespace SpectreClusters.StageA

theorem candidate_sparse_phase_iff (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (kind : HTKind)
    (hr : RootOwned f (canonicalRoot kind)) (i : Nat) (hi : i ∈ keptIds 2 kind)
    (hword : rawWordAt kind i = wordOf f kind) (n : Nat) (hn : n ∈ rawWordAt kind i) :
    SparseTurtlesAt f (canonicalRoot kind) ↔ SparseTurtlesAt f (candidateAt kind n) := by
  have hc := final_phase_checked kind i hi
  obtain ⟨j,hj,hjword,hs⟩ := actual_neighbor_support hcaptures f hf kind hr i n hword hn
    (phaseCompatible_alignment kind i n hc hn)
  have hp := GridReductionWindowBinding.represented_neighbor_owned f hf kind
    (field_mem_candidates f hf kind hr) n (show n ∈ wordOf f kind from hword ▸ hn)
  have hv := normalizeField_valid f hf (candidateAt kind n)
  have hroot := normalizeField_rootOwned f (candidateAt kind n) hp
  have he := phaseCompatible_sound kind i n j hc hn hj hs
  have hb : (sparseTurtlesRow kind i = true) ↔
      (sparseTurtlesRow (candidateAt kind n).kind j = true) := by rw [he]
  exact (row_sparseTurtles_iff f hf kind hr i hi hword).trans
    (hb.trans ((row_sparseTurtles_iff (normalizeField f (candidateAt kind n))
      hv (candidateAt kind n).kind hroot j hj hjword).symm.trans
        (sparseTurtlesAt_normalized_iff f (candidateAt kind n))))

theorem neighbor_sparse_phase_iff (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (root p : HTPlacement)
    (hr : RootOwned f root) (hp : FieldNeighbor f root p) :
    SparseTurtlesAt f root ↔ SparseTurtlesAt f p := by
  let g := normalizeField f root
  let q := movePlacement (turnNeg root.turn) (inverseTranslation root.turn root.center) p
  have hv : ValidGridField g := normalizeField_valid f hf root
  have hroot : RootOwned g (canonicalRoot root.kind) := normalizeField_rootOwned f root hr
  have hnq : FieldNeighbor g (canonicalRoot root.kind) q := by
    have hm := fieldNeighbor_moved (turnNeg root.turn) (inverseTranslation root.turn root.center)
      f root p hp
    rw [normalize_root] at hm
    exact hm
  obtain ⟨i,hi,hword⟩ := hcaptures g hv root.kind hroot
  have hmem := (row_neighbors_iff_fieldNeighbor g hv root.kind hroot i hword q).mpr hnq
  obtain ⟨n,hn,hnqeq⟩ := List.mem_map.mp hmem
  have hphase := candidate_sparse_phase_iff hcaptures g hv root.kind hroot i hi hword
    n (List.mem_eraseDups.mp hn)
  rw [hnqeq] at hphase
  exact (sparseTurtlesAt_normalized_iff f root).symm.trans
    (hphase.trans (sparseTurtlesAt_moved_iff (turnNeg root.turn)
      (inverseTranslation root.turn root.center) f p))

theorem contacting_cells_sparse_phase_iff (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (a b : Cell) (hc : CellContact a b) :
    SparseTurtlesAt f (f a) ↔ SparseTurtlesAt f (f b) := by
  by_cases he : f a = f b
  · rw [he]
  · apply neighbor_sparse_phase_iff hcaptures f hf (f a) (f b)
      (GridReduction.field_rootOwned f hf a)
    refine ⟨GridReduction.field_rootOwned f hf b,?_,a,(hf a).1,b,(hf b).1,hc⟩
    intro h
    exact he h.symm

theorem all_cells_sparse_phase_iff (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (a b : Cell) :
    SparseTurtlesAt f (f a) ↔ SparseTurtlesAt f (f b) := by
  have he := contact_invariant_constant (fun c => SparseTurtlesAt f (f c))
    (fun c d hcd => propext (contacting_cells_sparse_phase_iff hcaptures f hf c d hcd)) a b
  exact Iff.of_eq he

theorem ht_origin_cell_mem (kind : HTKind) : (⟨(0,0),0⟩ : Cell) ∈ htCells kind := by
  cases kind <;> decide

theorem owned_represented (f : Cell → HTPlacement) (root : HTPlacement)
    (hr : RootOwned f root) : ∃ c, f c = root := by
  refine ⟨moveCell root.turn root.center ⟨(0,0),0⟩,hr _ ?_⟩
  exact List.mem_map.mpr ⟨⟨(0,0),0⟩,ht_origin_cell_mem root.kind,rfl⟩

/-- The phase is globally constant on all actual tile occurrences. -/
theorem all_owned_sparse_phase_iff (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) (p q : HTPlacement)
    (hp : RootOwned f p) (hq : RootOwned f q) :
    SparseTurtlesAt f p ↔ SparseTurtlesAt f q := by
  obtain ⟨a,rfl⟩ := owned_represented f p hp
  obtain ⟨b,rfl⟩ := owned_represented f q hq
  exact all_cells_sparse_phase_iff hcaptures f hf a b

def SparseTurtles (f : Cell → HTPlacement) : Prop :=
  ∀ root, RootOwned f root → SparseTurtlesAt f root

def SparseHats (f : Cell → HTPlacement) : Prop :=
  ∀ root, RootOwned f root → ¬SparseTurtlesAt f root

theorem global_sparse_dichotomy (hcaptures : FinalCaptures)
    (f : Cell → HTPlacement) (hf : ValidGridField f) : SparseTurtles f ∨ SparseHats f := by
  classical
  let c : Cell := ⟨(0,0),0⟩
  have hc := GridReduction.field_rootOwned f hf c
  by_cases hs : SparseTurtlesAt f (f c)
  · left
    intro root hr
    exact (all_owned_sparse_phase_iff hcaptures f hf (f c) root hc hr).mp hs
  · right
    intro root hr hroot
    exact hs ((all_owned_sparse_phase_iff hcaptures f hf root (f c) hr hc).mp hroot)

end SpectreClusters.StageA
