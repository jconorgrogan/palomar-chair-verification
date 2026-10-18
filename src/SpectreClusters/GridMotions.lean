module

public import SpectreClusters.LiteralData

@[expose] public section


/-! The six direct grid rotations and lattice translations, with explicit
inverse and cell/placement action laws. No reflections are smuggled into
this homochiral model. -/
namespace SpectreClusters

def turnNeg (k : Turn) : Turn := ⟨(6-k.val)%6,Nat.mod_lt _ (by decide)⟩

theorem turnAdd_assoc : ∀ a b c : Turn,
    turnAdd a (turnAdd b c) = turnAdd (turnAdd a b) c := by decide
theorem turnAdd_neg : ∀ k : Turn, turnAdd (turnNeg k) k = 0 := by decide
theorem turnAdd_zero : ∀ k : Turn, turnAdd 0 k = k := by decide

theorem rotate_compose (a b : Turn) (p : Point) :
    rotate a (rotate b p) = rotate (turnAdd a b) p := by
  have h3 : (3 : Turn).val = 3 := rfl
  have h4 : (4 : Turn).val = 4 := rfl
  have h5 : (5 : Turn).val = 5 := rfl
  have ha := a.isLt; have hb := b.isLt
  have asplit : a.val=0 ∨ a.val=1 ∨ a.val=2 ∨ a.val=3 ∨ a.val=4 ∨ a.val=5 := by omega
  have bsplit : b.val=0 ∨ b.val=1 ∨ b.val=2 ∨ b.val=3 ∨ b.val=4 ∨ b.val=5 := by omega
  rcases asplit with ha|ha|ha|ha|ha|ha <;>
    rcases bsplit with hb|hb|hb|hb|hb|hb <;>
      apply Prod.ext <;> simp [rotate,turnAdd,ha,hb,h3,h4,h5] <;> omega

theorem rotate_inverse (k : Turn) (p : Point) : rotate (turnNeg k) (rotate k p) = p := by
  rw [rotate_compose,turnAdd_neg]
  rfl

theorem rotate_zero_point (k : Turn) : rotate k (0,0) = (0,0) := by
  have hk := k.isLt
  have hs : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 := by omega
  rcases hs with h|h|h|h|h|h <;> simp [rotate,h]

theorem rotate_sub (k : Turn) (a b : Point) :
    rotate k (sub a b) = sub (rotate k a) (rotate k b) := by
  have hk := k.isLt
  have hs : k.val=0 ∨ k.val=1 ∨ k.val=2 ∨ k.val=3 ∨ k.val=4 ∨ k.val=5 := by omega
  rcases hs with h|h|h|h|h|h <;>
    apply Prod.ext <;> simp [rotate,sub,h] <;> omega

def movePlacement (k : Turn) (t : Point) (p : HTPlacement) : HTPlacement :=
  ⟨p.kind,turnAdd k p.turn,add t (rotate k p.center)⟩

def inverseTranslation (k : Turn) (t : Point) : Point := rotate (turnNeg k) (sub (0,0) t)

theorem moveCell_compose (k l : Turn) (t u : Point) (c : Cell) :
    moveCell k t (moveCell l u c) =
      moveCell (turnAdd k l) (add t (rotate k u)) c := by
  unfold moveCell translateCell rotateCell
  congr 1
  · rw [rotate_add,rotate_compose,add_assoc]
  · exact turnAdd_assoc k l c.sector

theorem moveCell_zero (c : Cell) : moveCell 0 (0,0) c = c := by
  cases c
  simp [moveCell,translateCell,rotateCell,rotate,turnAdd_zero,add]

theorem inverse_offset (k : Turn) (t : Point) :
    add (inverseTranslation k t) (rotate (turnNeg k) t) = (0,0) := by
  rw [inverseTranslation,rotate_sub,rotate_zero_point]
  apply Prod.ext <;> simp [sub,add] <;> omega

theorem moveCell_inverse (k : Turn) (t : Point) (c : Cell) :
    moveCell (turnNeg k) (inverseTranslation k t) (moveCell k t c) = c := by
  rw [moveCell_compose,turnAdd_neg,inverse_offset,moveCell_zero]

theorem placementCells_moved (k : Turn) (t : Point) (p : HTPlacement) :
    placementCells (movePlacement k t p) = (placementCells p).map (moveCell k t) := by
  simp only [placementCells,movePlacement,List.map_map]
  apply List.map_congr_left
  intro c hc
  exact (moveCell_compose k p.turn t p.center c).symm

end SpectreClusters
