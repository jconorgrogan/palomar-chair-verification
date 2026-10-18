module

public import SpectreClusters.ClusterGridModel
public import SpectreClusters.GridNeighborTransport

@[expose] public section


namespace SpectreClusters

theorem moveClusterPlacement_zero (p : ClusterPlacement) :
    moveClusterPlacement 0 (0,0) p = p := by
  cases p
  simp [moveClusterPlacement,turnAdd_zero,rotate,add]

theorem moveClusterPlacement_compose (k l : Turn) (t u : Point) (p : ClusterPlacement) :
    moveClusterPlacement k t (moveClusterPlacement l u p) =
      moveClusterPlacement (turnAdd k l) (add t (rotate k u)) p := by
  cases p
  simp only [moveClusterPlacement,turnAdd_assoc,rotate_add,rotate_compose,add_assoc]

theorem moveClusterPlacement_inverse (k : Turn) (t : Point) (p : ClusterPlacement) :
    moveClusterPlacement (turnNeg k) (inverseTranslation k t) (moveClusterPlacement k t p) = p := by
  rw [moveClusterPlacement_compose,turnAdd_neg,inverse_offset,moveClusterPlacement_zero]

theorem moveClusterPlacement_right_inverse (k : Turn) (t : Point) (p : ClusterPlacement) :
    moveClusterPlacement k t (moveClusterPlacement (turnNeg k) (inverseTranslation k t) p) = p := by
  have h := movePlacement_right_inverse k t (⟨.turtle,p.turn,p.center⟩ : HTPlacement)
  cases p with
  | mk kind turn center =>
    have ht := congrArg HTPlacement.turn h
    have hc := congrArg HTPlacement.center h
    unfold moveClusterPlacement
    congr 1

theorem clusterPlacementCells_moved (k : Turn) (t : Point) (p : ClusterPlacement) :
    clusterPlacementCells (moveClusterPlacement k t p) =
      (clusterPlacementCells p).map (moveCell k t) := by
  simp only [clusterPlacementCells,moveClusterPlacement,List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (moveCell_compose k p.turn t p.center c).symm

def moveClusterField (k : Turn) (t : Point) (f : Cell → ClusterPlacement) (c : Cell) : ClusterPlacement :=
  moveClusterPlacement k t (f (moveCell (turnNeg k) (inverseTranslation k t) c))

theorem moveClusterField_apply_moved (k : Turn) (t : Point)
    (f : Cell → ClusterPlacement) (c : Cell) :
    moveClusterField k t f (moveCell k t c) = moveClusterPlacement k t (f c) := by
  simp only [moveClusterField,moveCell_inverse]

theorem moveClusterField_valid (k : Turn) (t : Point)
    (f : Cell → ClusterPlacement) (hf : ValidClusterGridField f) :
    ValidClusterGridField (moveClusterField k t f) := by
  intro c
  let d := moveCell (turnNeg k) (inverseTranslation k t) c
  have hd := hf d
  refine ⟨hd.1,?_,?_⟩
  · change c ∈ clusterPlacementCells (moveClusterPlacement k t (f d))
    rw [clusterPlacementCells_moved]
    exact List.mem_map.mpr ⟨d,hd.2.1,moveCell_right_inverse k t c⟩
  · intro e he
    change e ∈ clusterPlacementCells (moveClusterPlacement k t (f d)) at he
    rw [clusterPlacementCells_moved] at he
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    rw [moveClusterField_apply_moved,hd.2.2 a ha]
    rfl

theorem moveClusterField_rootOwned (k : Turn) (t : Point)
    (f : Cell → ClusterPlacement) (p : ClusterPlacement) (hp : ClusterRootOwned f p) :
    ClusterRootOwned (moveClusterField k t f) (moveClusterPlacement k t p) := by
  intro c hc
  rw [clusterPlacementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rw [moveClusterField_apply_moved,hp d hd]

end SpectreClusters
