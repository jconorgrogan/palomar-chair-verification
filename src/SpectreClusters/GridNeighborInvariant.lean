module

public import SpectreClusters.GridNeighborTransport

@[expose] public section


namespace SpectreClusters

theorem moveField_inverse (k : Turn) (t : Point) (f : Cell → HTPlacement) :
    moveField (turnNeg k) (inverseTranslation k t) (moveField k t f) = f := by
  funext c
  have h := moveField_apply_moved (turnNeg k) (inverseTranslation k t)
    (moveField k t f) (moveCell k t c)
  rw [moveCell_inverse,moveField_apply_moved,movePlacement_inverse] at h
  exact h

theorem fieldNeighbor_moved_iff (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root p : HTPlacement) :
    StageA.FieldNeighbor (moveField k t f) (movePlacement k t root) (movePlacement k t p) ↔
      StageA.FieldNeighbor f root p := by
  constructor
  · intro h
    have hi := fieldNeighbor_moved (turnNeg k) (inverseTranslation k t)
      (moveField k t f) _ _ h
    simpa only [moveField_inverse,movePlacement_inverse] using hi
  · exact fieldNeighbor_moved k t f root p

def AllOppositeNeighbors (f : Cell → HTPlacement) (root : HTPlacement) : Prop :=
  ∀ p, StageA.FieldNeighbor f root p → p.kind ≠ root.kind

theorem allOppositeNeighbors_moved (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root : HTPlacement) (h : AllOppositeNeighbors f root) :
    AllOppositeNeighbors (moveField k t f) (movePlacement k t root) := by
  intro p hp
  have hn : StageA.FieldNeighbor (moveField k t f) (movePlacement k t root)
      (movePlacement k t (movePlacement (turnNeg k) (inverseTranslation k t) p)) := by
    simpa only [movePlacement_right_inverse] using hp
  have horiginal := (fieldNeighbor_moved_iff k t f root _).mp hn
  exact h (movePlacement (turnNeg k) (inverseTranslation k t) p) horiginal

theorem allOppositeNeighbors_moved_iff (k : Turn) (t : Point)
    (f : Cell → HTPlacement) (root : HTPlacement) :
    AllOppositeNeighbors (moveField k t f) (movePlacement k t root) ↔
      AllOppositeNeighbors f root := by
  constructor
  · intro h
    have hi := allOppositeNeighbors_moved (turnNeg k) (inverseTranslation k t)
      (moveField k t f) (movePlacement k t root) h
    simpa only [moveField_inverse,movePlacement_inverse] using hi
  · exact allOppositeNeighbors_moved k t f root

/-- Intrinsic phase of an actual occurrence. Sparse turtles are precisely
all-opposite turtle occurrences and non-all-opposite hat occurrences. -/
def SparseTurtlesAt (f : Cell → HTPlacement) (root : HTPlacement) : Prop :=
  root.kind = .turtle ↔ AllOppositeNeighbors f root

theorem sparseTurtlesAt_moved_iff (k : Turn) (t : Point)
    (f : Cell → HTPlacement) (root : HTPlacement) :
    SparseTurtlesAt (moveField k t f) (movePlacement k t root) ↔ SparseTurtlesAt f root := by
  unfold SparseTurtlesAt
  rw [allOppositeNeighbors_moved_iff]
  rfl

theorem sparseTurtlesAt_normalized_iff (f : Cell → HTPlacement) (root : HTPlacement) :
    SparseTurtlesAt (normalizeField f root) (originRoot root.kind) ↔ SparseTurtlesAt f root := by
  have h := sparseTurtlesAt_moved_iff (turnNeg root.turn)
    (inverseTranslation root.turn root.center) f root
  rw [normalize_root] at h
  exact h

end SpectreClusters
