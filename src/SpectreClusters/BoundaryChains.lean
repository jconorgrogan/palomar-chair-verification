module

public import SpectreClusters.LiteralData

@[expose] public section


/-! Finite oriented-cell-boundary checks, not a physical realization theorem. -/
namespace SpectreClusters

abbrev Edge := Point × Point

def cycleEdges (vs : List Point) : List Edge :=
  match vs with
  | [] => []
  | v :: tail => vs.zip (tail ++ [v])

def shapeEdges (cells : List Cell) : List Edge :=
  cells.flatMap (fun c => cycleEdges (cellVertices c))

def reverseEdge (e : Edge) : Edge := (e.2,e.1)

def exteriorEdges (cells : List Cell) : List Edge :=
  let es := shapeEdges cells
  es.filter (fun e => !(es.contains (reverseEdge e)))

/-- Equality of the literal exterior directed edge sets, with multiplicity
one on both sides. This does not by itself establish the real-body equality. -/
def BoundaryAgreement (cells : List Cell) (polygon : List Point) : Prop :=
  let ex := exteriorEdges cells
  let pe := cycleEdges polygon
  ex.Nodup ∧ pe.Nodup ∧ (∀ e ∈ ex, e ∈ pe) ∧ (∀ e ∈ pe, e ∈ ex)
instance (cells : List Cell) (polygon : List Point) :
    Decidable (BoundaryAgreement cells polygon) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem hat_cell_count : (htCells .hat).length = 8 := rfl
theorem turtle_cell_count : (htCells .turtle).length = 10 := rfl
theorem hat_cells_distinct : (htCells .hat).Nodup := by decide
theorem turtle_cells_distinct : (htCells .turtle).Nodup := by decide

set_option maxRecDepth 100000 in
theorem hat_boundary_agreement : BoundaryAgreement (htCells .hat) (htRefinedPolygon .hat) := by
  decide

set_option maxRecDepth 100000 in
theorem turtle_boundary_agreement :
    BoundaryAgreement (htCells .turtle) (htRefinedPolygon .turtle) := by decide

end SpectreClusters
