module

public import SpectreClusters.StageDActualSystem

@[expose] public section


/-! Every actual cell contact is an intrinsic six-port adjacency. The literal
halo-order membership binding is kept explicit until the raw replay supplies it. -/
namespace SpectreClusters.StageD
open SpectreFinite SpectreFinite.HexSearch

def HaloOrderBinding : Prop := ∀ k : ClusterKind, LegalClusterKind k →
  ∀ c : Cell, c ∈ halo (clusterCells k) ↔ c ∈ haloOrder k

theorem row_neighbor_is_port (checks : FinalRowChecks) (i : Row) (p : ClusterPlacement) (hp : p ∈ rowNeighbors i) :
    ∃ d : Fin 6, rowPort i d = p := by
  have hl := List.idxOf_lt_length_of_mem hp
  have hd : (rowNeighbors i).idxOf p < 6 := by simpa only [row_neighbors_length checks] using hl
  refine ⟨⟨(rowNeighbors i).idxOf p,hd⟩,?_⟩
  simp [rowPort,List.getD_eq_getElem?_getD,hl]

theorem row_halo_covered (checks : FinalRowChecks) (hh : HaloOrderBinding) (i : Row) (c : Cell)
    (hc : c ∈ halo (clusterCells (rowKind i))) :
    ∃ d : Fin 6, c ∈ clusterPlacementCells (rowPort i d) := by
  have h := checks.basics i
  simp only [rowBasicsB,Bool.and_eq_true,decide_eq_true_eq] at h
  have hm := (hh (rowKind i) h.1.1.1 c).mp hc
  have hcover := (List.all_eq_true.mp h.2) c hm
  obtain ⟨p,hp,hpc⟩ := List.any_eq_true.mp hcover
  obtain ⟨v,hv,he⟩ := List.any_eq_true.mp hpc
  obtain ⟨d,rfl⟩ := row_neighbor_is_port checks i p hp
  exact ⟨d,(cellEqB_iff _ _).mp he ▸ hv⟩

theorem inverse_cell_mem_cluster (p : ClusterPlacement) (c : Cell)
    (hc : c ∈ clusterPlacementCells p) :
    moveCell (turnNeg p.turn) (inverseTranslation p.turn p.center) c ∈ clusterCells p.kind := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hc
  simpa only [moveCell_inverse] using hb

def clusterCellOwner {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f)
    (c : Cell) : ActualCluster f := ⟨f c,(hf c).2.2⟩

theorem actual_contact_steps (checks : FinalRowChecks) (hc : FinalClusterCaptures) (hh : HaloOrderBinding)
    {f : Cell → ClusterPlacement} (hf : ValidClusterGridField f) :
    ClusterOrbit.ContactSteps (actualHexSystem checks hc hf) (clusterCellOwner hf) := by
  intro a b hab
  by_cases he : f b = f a
  · exact Or.inl (Subtype.ext he)
  · let p : ActualCluster f := clusterCellOwner hf a
    let i := chosenRow hc hf p
    let a0 := moveCell (turnNeg p.val.turn) (inverseTranslation p.val.turn p.val.center) a
    let b0 := moveCell (turnNeg p.val.turn) (inverseTranslation p.val.turn p.val.center) b
    have ha0 : a0 ∈ clusterCells p.val.kind := inverse_cell_mem_cluster p.val a (hf a).2.1
    have hb0 : b0 ∉ clusterCells p.val.kind := by
      intro hb
      have hbin : b ∈ clusterPlacementCells p.val :=
        List.mem_map.mpr ⟨b0,hb,moveCell_right_inverse p.val.turn p.val.center b⟩
      exact he (p.property b hbin)
    have hcontact : CellContact a0 b0 :=
      cellContact_moved (turnNeg p.val.turn) (inverseTranslation p.val.turn p.val.center) a b hab
    have hhalo : b0 ∈ halo (clusterCells (rowKind i)) := by
      rw [(chosenRow_spec hc hf p).1]
      exact (mem_halo_iff _ _).mpr ⟨hb0,a0,ha0,hcontact⟩
    obtain ⟨e,heport⟩ := row_halo_covered checks hh i b0 hhalo
    let d := turnAdd p.val.turn e
    have hbin : b ∈ clusterPlacementCells (neighborPlacement i p.val d) := by
      unfold neighborPlacement
      rw [turnDiff_turnAdd,clusterPlacementCells_moved]
      exact List.mem_map.mpr ⟨b0,heport,moveCell_right_inverse p.val.turn p.val.center b⟩
    refine Or.inr ⟨d,?_⟩
    apply Subtype.ext
    exact neighborPlacement_owned checks hc hf p d b hbin

end SpectreClusters.StageD
