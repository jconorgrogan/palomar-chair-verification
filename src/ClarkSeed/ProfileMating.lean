module

public import ProductClosure.ProductGraphContactWalks
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

/-! Literal finite vertex profiles with the original sparse-key mating action.
Spatial transport preserves the material bit; each mating step flips it.
Consequently this action is not silently treated as a group action. -/
namespace ClarkSeed.ProfileMating
noncomputable section
open Function
variable {X : Type*}

abbrev Key (X : Type*) := Finset X × Bool
abbrev Profile (X : Type*) := Finset (Key X)

def moveKey (g : X ≃ X) (k : Key X) : Key X := by
  classical
  exact (k.1.image g, k.2)

def flipKey (k : Key X) : Key X := (k.1, !k.2)

def move (g : X ≃ X) (P : Profile X) : Profile X := by
  classical
  exact P.image (moveKey g)

def flip (P : Profile X) : Profile X := by
  classical
  exact P.image flipKey

def mate (g : X ≃ X) (P : Profile X) : Profile X := move g (flip P)

@[simp] theorem flipKey_flipKey (k : Key X) : flipKey (flipKey k) = k := by
  rcases k with ⟨V,b⟩
  cases b <;> rfl

@[simp] theorem moveKey_refl (k : Key X) : moveKey (Equiv.refl X) k = k := by
  classical
  simp [moveKey]

@[simp] theorem moveKey_trans (g h : X ≃ X) (k : Key X) :
    moveKey h (moveKey g k) = moveKey (g.trans h) k := by
  classical
  simp [moveKey, Finset.image_image, Function.comp_def]

@[simp] theorem flipKey_moveKey (g : X ≃ X) (k : Key X) :
    flipKey (moveKey g k) = moveKey g (flipKey k) := rfl

@[simp] theorem flip_flip (P : Profile X) : flip (flip P) = P := by
  classical
  simp [flip, Finset.image_image, Function.comp_def]

theorem flip_involutive : Involutive (flip (X := X)) := flip_flip

@[simp] theorem move_refl (P : Profile X) : move (Equiv.refl X) P = P := by
  classical
  have h : moveKey (Equiv.refl X) = id := funext moveKey_refl
  simp [move, h]

theorem move_trans (g h : X ≃ X) (P : Profile X) :
    move h (move g P) = move (g.trans h) P := by
  classical
  simp only [move, Finset.image_image]
  congr 1
  funext k
  exact moveKey_trans g h k

@[simp] theorem flip_move (g : X ≃ X) (P : Profile X) :
    flip (move g P) = move g (flip P) := by
  classical
  simp only [flip, move, Finset.image_image]
  rfl

@[simp] theorem move_inverse (g : X ≃ X) (P : Profile X) :
    move g.symm (move g P) = P := by
  rw [move_trans]
  simp

@[simp] theorem mate_inverse (g : X ≃ X) (P : Profile X) :
    mate g.symm (mate g P) = P := by
  simp only [mate, flip_move, flip_flip, move_inverse]

theorem mate_eq_inverse_iff (g : X ≃ X) (P Q : Profile X) :
    P = mate g Q ↔ Q = mate g.symm P := by
  constructor
  · rintro rfl
    exact (mate_inverse g Q).symm
  · intro h
    rw [h]
    simpa using (mate_inverse g.symm P).symm

/-- Exactly one flip remains on an odd path. -/
theorem flip_iterate_odd (n : ℕ) (hn : Odd n) (P : Profile X) :
    flip^[n] P = flip P := by
  rw [flip_involutive.iterate_odd hn]

/-- Even paths preserve the material bit. -/
theorem flip_iterate_even (n : ℕ) (hn : Even n) (P : Profile X) :
    flip^[n] P = P := by
  rw [flip_involutive.iterate_even hn]
  rfl

#print axioms mate_inverse
#print axioms flip_iterate_odd
#print axioms move_trans
end
end ClarkSeed.ProfileMating
