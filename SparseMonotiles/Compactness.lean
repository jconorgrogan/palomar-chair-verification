module

public import SparseMonotiles.Model
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Compactness of every body specified by a finite list of rational pyramid keys.
No sign condition on the radii and no positive-dimension assumption is needed.
The essential additional ingredient beyond closedness is boundedness: coordinate
boxes bound the carrier and key bases, convex hull preserves boundedness, and
only finitely many keys occur.
-/

namespace SparseMonotiles

private theorem coordinateBox_isCompact {d : ℕ} (a b : Fin d → ℝ) :
    IsCompact {x : Point d | ∀ i, a i ≤ x i ∧ x i ≤ b i} := by
  have hbox : {x : Point d | ∀ i, a i ≤ x i ∧ x i ≤ b i} =
      (WithLp.equiv 2 (Fin d → ℝ)).symm '' Set.Icc a b := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.equiv 2 _ x, ?_, by simp⟩
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
    · rintro ⟨y, ⟨ha, hb⟩, rfl⟩
      exact fun i => ⟨ha i, hb i⟩
  rw [hbox]
  exact isCompact_Icc.image (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ))

theorem keyBase_isCompact {d : ℕ} (k : KeyData d) : IsCompact (keyBase k) := by
  have hbox : keyBase k = {x : Point d | ∀ i,
      (k.centre i : ℝ) - (k.radius i : ℝ) ≤ x i ∧
      x i ≤ (k.centre i : ℝ) + (k.radius i : ℝ)} := by
    ext x
    simp only [keyBase, Set.mem_setOf_eq, abs_le]
    constructor
    · intro hx i
      obtain ⟨hlo, hhi⟩ := hx i
      constructor <;> linarith
    · intro hx i
      obtain ⟨hlo, hhi⟩ := hx i
      constructor <;> linarith
  rw [hbox]
  exact coordinateBox_isCompact _ _

theorem keySolid_isBounded {d : ℕ} (k : KeyData d) :
    Bornology.IsBounded (keySolid k) := by
  unfold keySolid
  exact isBounded_convexHull.mpr ((keyBase_isCompact k).isBounded.insert _)

theorem carrier_isBounded (d : ℕ) : Bornology.IsBounded (carrier d) := by
  apply (coordinateBox_isCompact (fun _ : Fin d => 0) (fun _ => 2)).isBounded.subset
  rintro x ⟨c, _, hx⟩ i
  specialize hx i
  cases h : c i <;> simp [h] at hx <;> constructor <;> linarith

theorem keyUnion_isBounded {d : ℕ} (ks : List (KeyData d)) (b : Bool) :
    Bornology.IsBounded (keyUnion ks b) := by
  induction ks with
  | nil =>
      simpa [keyUnion] using (Bornology.isBounded_empty : Bornology.IsBounded (∅ : Set (Point d)))
  | cons k ks ih =>
      apply ((keySolid_isBounded k).union ih).subset
      rintro x ⟨k', hk', hb, hx⟩
      rcases List.mem_cons.mp hk' with hk' | hk'
      · subst k'
        exact Or.inl hx
      · exact Or.inr ⟨k', hk', hb, hx⟩

theorem body_isCompact {d : ℕ} (ks : List (KeyData d)) : IsCompact (body ks) := by
  unfold body
  exact (((carrier_isBounded d).union (keyUnion_isBounded ks true)).subset
    Set.diff_subset).isCompact_closure

end SparseMonotiles
