module

public import SpectreClusters.GridMotions
public import SpectreClusters.GridReduction

@[expose] public section


/-! Direct-motion transport of the discrete tiling partition and its
occurrences. This makes normalization to the literal origin root sound.
The hypotheses remain about cells, not physical plane tilings. -/
namespace SpectreClusters

theorem moveCell_injective (k : Turn) (t : Point) :
    Function.Injective (moveCell k t) := by
  intro a b h
  have := congrArg (moveCell (turnNeg k) (inverseTranslation k t)) h
  simpa only [moveCell_inverse] using this

theorem moveCell_right_inverse (k : Turn) (t : Point) (c : Cell) :
    moveCell k t (moveCell (turnNeg k) (inverseTranslation k t) c) = c := by
  apply moveCell_injective (turnNeg k) (inverseTranslation k t)
  exact moveCell_inverse k t (moveCell (turnNeg k) (inverseTranslation k t) c)

theorem movePlacement_compose (k l : Turn) (t u : Point) (p : HTPlacement) :
    movePlacement k t (movePlacement l u p) =
      movePlacement (turnAdd k l) (add t (rotate k u)) p := by
  unfold movePlacement
  congr 1
  · exact turnAdd_assoc k l p.turn
  · rw [rotate_add,rotate_compose,add_assoc]

theorem movePlacement_zero (p : HTPlacement) : movePlacement 0 (0,0) p = p := by
  cases p
  simp [movePlacement,rotate,turnAdd_zero,add]

theorem movePlacement_inverse (k : Turn) (t : Point) (p : HTPlacement) :
    movePlacement (turnNeg k) (inverseTranslation k t) (movePlacement k t p) = p := by
  rw [movePlacement_compose,turnAdd_neg,inverse_offset,movePlacement_zero]

theorem movePlacement_injective (k : Turn) (t : Point) :
    Function.Injective (movePlacement k t) := by
  intro a b h
  have := congrArg (movePlacement (turnNeg k) (inverseTranslation k t)) h
  simpa only [movePlacement_inverse] using this

theorem movePlacement_right_inverse (k : Turn) (t : Point) (p : HTPlacement) :
    movePlacement k t (movePlacement (turnNeg k) (inverseTranslation k t) p) = p := by
  apply movePlacement_injective (turnNeg k) (inverseTranslation k t)
  exact movePlacement_inverse k t (movePlacement (turnNeg k) (inverseTranslation k t) p)

theorem mem_placementCells_moved (k : Turn) (t : Point) (p : HTPlacement) (c : Cell) :
    moveCell k t c ∈ placementCells (movePlacement k t p) ↔ c ∈ placementCells p := by
  rw [placementCells_moved]
  constructor
  · intro h
    obtain ⟨d,hd,he⟩ := List.mem_map.mp h
    exact (moveCell_injective k t he) ▸ hd
  · intro h
    exact List.mem_map.mpr ⟨c,h,rfl⟩

/-- Conjugate the entire cell-owner field by a direct grid motion. -/
def moveField (k : Turn) (t : Point) (f : Cell → HTPlacement) : Cell → HTPlacement :=
  fun c => movePlacement k t (f (moveCell (turnNeg k) (inverseTranslation k t) c))

theorem moveField_apply_moved (k : Turn) (t : Point) (f : Cell → HTPlacement) (c : Cell) :
    moveField k t f (moveCell k t c) = movePlacement k t (f c) := by
  simp only [moveField,moveCell_inverse]

theorem moveField_valid (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (hf : ValidGridField f) : ValidGridField (moveField k t f) := by
  intro c
  let d := moveCell (turnNeg k) (inverseTranslation k t) c
  have hcd : moveCell k t d = c := moveCell_right_inverse k t c
  rw [← hcd,moveField_apply_moved]
  refine ⟨(mem_placementCells_moved k t (f d) d).mpr (hf d).1,?_⟩
  intro e he
  rw [placementCells_moved] at he
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
  rw [moveField_apply_moved,(hf d).2 a ha]

theorem moveField_rootOwned (k : Turn) (t : Point) (f : Cell → HTPlacement)
    (root : HTPlacement) (hr : RootOwned f root) :
    RootOwned (moveField k t f) (movePlacement k t root) := by
  intro c hc
  rw [placementCells_moved] at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  rw [moveField_apply_moved,hr d hd]

def originRoot (kind : HTKind) : HTPlacement := ⟨kind,0,(0,0)⟩

theorem movePlacement_originRoot (p : HTPlacement) :
    movePlacement p.turn p.center (originRoot p.kind) = p := by
  have hz : ∀ k : Turn, turnAdd k 0 = k := by decide
  cases p
  simp [movePlacement,originRoot,hz,rotate_zero_point,add]

theorem normalize_root (p : HTPlacement) :
    movePlacement (turnNeg p.turn) (inverseTranslation p.turn p.center) p = originRoot p.kind := by
  have h := movePlacement_inverse p.turn p.center (originRoot p.kind)
  rw [movePlacement_originRoot] at h
  exact h

def normalizeField (f : Cell → HTPlacement) (root : HTPlacement) : Cell → HTPlacement :=
  moveField (turnNeg root.turn) (inverseTranslation root.turn root.center) f

theorem normalizeField_apply (f : Cell → HTPlacement) (root : HTPlacement) (c : Cell) :
    normalizeField f root c = movePlacement (turnNeg root.turn)
      (inverseTranslation root.turn root.center) (f (moveCell root.turn root.center c)) := by
  have h := moveField_apply_moved (turnNeg root.turn)
    (inverseTranslation root.turn root.center) f (moveCell root.turn root.center c)
  rw [moveCell_inverse] at h
  exact h

theorem denormalizeField_apply (f : Cell → HTPlacement) (root : HTPlacement) (c : Cell) :
    movePlacement root.turn root.center (normalizeField f root c) =
      f (moveCell root.turn root.center c) := by
  rw [normalizeField_apply,movePlacement_right_inverse]

theorem normalizeField_valid (f : Cell → HTPlacement) (hf : ValidGridField f)
    (root : HTPlacement) : ValidGridField (normalizeField f root) :=
  moveField_valid _ _ f hf

theorem normalizeField_rootOwned (f : Cell → HTPlacement) (root : HTPlacement)
    (hr : RootOwned f root) : RootOwned (normalizeField f root) (originRoot root.kind) := by
  have h := moveField_rootOwned (turnNeg root.turn)
    (inverseTranslation root.turn root.center) f root hr
  rw [normalize_root] at h
  exact h

/-- Every physical occurrence that has already been transferred to a genuine
grid partition admits a normalized corona in every generic reduction round. -/
theorem normalized_restriction_mem_allRounds (f : Cell → HTPlacement)
    (hf : ValidGridField f) (root : HTPlacement) (hr : RootOwned f root) (n : Nat) :
    GridReduction.restriction (normalizeField f root) (originRoot root.kind) ∈
      GridReduction.allRounds n (originRoot root.kind) :=
  GridReduction.restriction_mem_allRounds (normalizeField f root)
    (normalizeField_valid f hf root) n (originRoot root.kind) (normalizeField_rootOwned f root hr)

end SpectreClusters
