module

public import SpectreClusters.StageAFieldNeighbors
public import SpectreClusters.GridReductionTransport

@[expose] public section


/-! Exact vertex-contact and actual-neighbor covariance under direct grid
motions. All statements remain on the literal kite grid. -/
namespace SpectreClusters

def moveVertex (k : Turn) (t : Point) (v : Point) : Point :=
  add (lattice t) (rotate k v)

theorem cellVertices_moved (k : Turn) (t : Point) (c : Cell) :
    cellVertices (moveCell k t c) = (cellVertices c).map (moveVertex k t) := by
  simp only [cellVertices,moveCell,translateCell,rotateCell,localVertices,List.map_map]
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_def,moveVertex,lattice_add,lattice_rotate,rotate_add,rotate_compose,add_assoc]

theorem cellContact_moved (k : Turn) (t : Point) (a b : Cell)
    (h : CellContact a b) : CellContact (moveCell k t a) (moveCell k t b) := by
  obtain ⟨v,hva,hvb⟩ := h
  refine ⟨moveVertex k t v,?_,?_⟩ <;> rw [cellVertices_moved]
  · exact List.mem_map.mpr ⟨v,hva,rfl⟩
  · exact List.mem_map.mpr ⟨v,hvb,rfl⟩

theorem cellContact_moved_iff (k : Turn) (t : Point) (a b : Cell) :
    CellContact (moveCell k t a) (moveCell k t b) ↔ CellContact a b := by
  constructor
  · intro h
    have hi := cellContact_moved (turnNeg k) (inverseTranslation k t) _ _ h
    simpa only [moveCell_inverse] using hi
  · exact cellContact_moved k t a b

theorem shapeContact_moved (k : Turn) (t : Point) (a b : HTPlacement)
    (h : ShapeContact (placementCells a) (placementCells b)) :
    ShapeContact (placementCells (movePlacement k t a))
      (placementCells (movePlacement k t b)) := by
  obtain ⟨c,hc,d,hd,hcontact⟩ := h
  refine ⟨moveCell k t c,?_,moveCell k t d,?_,cellContact_moved k t c d hcontact⟩
  · exact (mem_placementCells_moved k t a c).mpr hc
  · exact (mem_placementCells_moved k t b d).mpr hd

theorem shapeContact_moved_iff (k : Turn) (t : Point) (a b : HTPlacement) :
    ShapeContact (placementCells (movePlacement k t a))
      (placementCells (movePlacement k t b)) ↔
    ShapeContact (placementCells a) (placementCells b) := by
  constructor
  · intro h
    have hi := shapeContact_moved (turnNeg k) (inverseTranslation k t) _ _ h
    simpa only [movePlacement_inverse] using hi
  · exact shapeContact_moved k t a b

theorem fieldNeighbor_moved (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root p : HTPlacement) (h : StageA.FieldNeighbor f root p) :
    StageA.FieldNeighbor (moveField k t f) (movePlacement k t root) (movePlacement k t p) := by
  refine ⟨moveField_rootOwned k t f p h.1,?_,shapeContact_moved k t root p h.2.2⟩
  intro he
  exact h.2.1 (movePlacement_injective k t he)

end SpectreClusters
