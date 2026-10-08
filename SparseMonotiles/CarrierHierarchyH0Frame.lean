module

public import SparseMonotiles.CarrierHierarchyCharts

@[expose] public section

/-!
The H0 geometry allows an unsigned coordinate permutation between the two
actual chosen frames. This avoids any global gauge-lift assumption or changing
which representatives the registered global world contains.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

def h0Transition {d : ℕ} (f : Equiv.Perm (Fin d)) : Pose d where
  perm := f
  negative := fun _ => false
  shift := fun _ => 1

private theorem h0_boxLower {d : ℕ} (f : Equiv.Perm (Fin d)) (p : Pose d) :
    boxLower (compose (h0Transition f) p) = fun i => boxLower p (f i) + 1 := by
  funext i
  simp only [boxLower, compose, h0Transition, Pose.sign, Bool.false_eq_true,
    if_false, Bool.false_xor, one_mul]
  omega

private theorem h0_hole {d : ℕ} (f : Equiv.Perm (Fin d)) (p : Pose d) :
    hole (compose (h0Transition f) p) = fun i => hole p (f i) + 1 := by
  funext i
  simp only [hole_coordinate, compose, h0Transition, Pose.sign, Bool.false_xor,
    Bool.false_eq_true, if_false, one_mul]
  omega

/-- Corrected H0 completion with the actual unsigned frame transition. -/
theorem h0_frame_two_corona_completion {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (S R : LocalPatch d σ r) (hd : 3 ≤ d) (f : Equiv.Perm (Fin d))
    (cross : ∀ p ∈ S.tiles, ∀ q ∈ R.tiles, ∀ c,
      Occupies p c → Occupies (compose (h0Transition f) q) c →
      GaugeRel r p (compose (h0Transition f) q))
    (hempty : R.incoming (emptyRole d)) :
    (∀ a, Proper a → S.incoming a) ∨ (∀ a, Proper a → R.incoming a) := by
  classical
  by_cases hR : ∀ a, Proper a → R.incoming a
  · exact Or.inr hR
  · let j : Fin d := ⟨0, by omega⟩
    let l := f.symm j
    have hk : ∃ k : Fin d, k ≠ l := by
      let i₀ : Fin d := ⟨0, by omega⟩
      let i₁ : Fin d := ⟨1, by omega⟩
      by_cases h : l = i₀
      · refine ⟨i₁, ?_⟩
        intro hh
        have := congrArg Fin.val (hh.trans h)
        simp [i₀, i₁] at this
      · exact ⟨i₀, Ne.symm h⟩
    obtain ⟨k, hkl⟩ := hk
    let a : Bits d := fun i => decide (i ≠ l)
    have ha : Proper a := ⟨l, by simp [a]⟩
    have hna : NonemptyRole a := ⟨k, by simp [a, hkl]⟩
    obtain ⟨q, hq, hb, hh⟩ := R.incomplete_empty_negative_wall hd hR hempty j
    have hiff : ∀ i, f i = j ↔ i = l := by
      intro i
      constructor
      · intro h
        simpa [l] using congrArg f.symm h
      · intro h
        subst i
        simp [l]
    have hshiftBox : boxLower (compose (h0Transition f) q) = fun i => 2 * bit a i - 1 := by
      rw [h0_boxLower, hb]
      funext i
      by_cases h : i = l <;> simp [wallBox, bit, a, hiff, h]
    have hshiftHole : hole (compose (h0Transition f) q) = fun i => bit a i := by
      rw [h0_hole, hh]
      funext i
      by_cases h : i = l <;> simp [unitAxis, bit, a, hiff, h]
    obtain ⟨p, hp, hpx⟩ := S.covers a ha l
    have hqx : Occupies (compose (h0Transition f) q) (exterior a l) := by
      have h := incoming_owns_exterior a (σ a) l
      rw [occupies_box_iff, incoming_boxLower, incoming_hole] at h
      rw [occupies_box_iff, hshiftBox, hshiftHole]
      exact h
    have hg := cross p hp q hq _ hpx hqx
    have hpBox := (gauge_boxLower_eq hg).trans hshiftBox
    have hpHole := (gauge_hole_eq hg).trans hshiftHole
    have hrole := role_of_box_and_hole hpBox hpHole
    have his : IsChairCell (hole p) := by
      rw [hpHole]
      constructor
      · intro i
        cases h : a i <;> simp [bit, h]
      · exact ⟨l, by simp [bit, a]⟩
    have incoming : S.incoming a := by
      refine ⟨p, hp, ?_⟩
      simpa [hrole] using ((S.catalog p hp).2.1 his).2
    exact Or.inl (S.complete_of_nonempty_incoming hd ha hna incoming)

#print axioms h0_frame_two_corona_completion
end SparseMonotiles.CarrierHierarchy
