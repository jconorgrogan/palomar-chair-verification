module

public import SparseMonotiles.CarrierHierarchyRecognition

@[expose] public section

/-!
H0 two-corona completion with genuinely separate root-excluding local patches.
Only overlapping tiles are related across the two coordinate charts. In
particular, the shifted second-chart empty predecessor may be the omitted first
root: there is NO same-index or all-row transport premise.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

/-- Transport from the hole-owner chart to the root chart in the H0 case. -/
def shiftOne {d : ℕ} (p : Pose d) : Pose d where
  perm := p.perm
  negative := p.negative
  shift := fun i => p.shift i + 1

@[simp] theorem shiftOne_boxLower {d : ℕ} (p : Pose d) :
    boxLower (shiftOne p) = fun i => boxLower p i + 1 := by
  funext i
  cases h : p.negative i <;> simp [boxLower, shiftOne, h] <;> omega

@[simp] theorem shiftOne_hole {d : ℕ} (p : Pose d) :
    hole (shiftOne p) = fun i => hole p i + 1 := by
  funext i
  simp only [hole_coordinate, shiftOne]
  omega

theorem gauge_boxLower_eq {d : ℕ} {r : Equiv.Perm (Fin d)} {p q : Pose d}
    (h : GaugeRel r p q) : boxLower p = boxLower q := by
  rcases h with rfl | rfl <;> rfl

def emptyRole (d : ℕ) : Bits d := fun _ => false

private theorem exterior_empty {d : ℕ} (j : Fin d) :
    exterior (emptyRole d) j = fun i => -unitAxis j i := by
  funext i
  by_cases h : i = j <;> simp [exterior, emptyRole, bit, unitAxis, h]

/-- The actual incomplete second corona forces a negative complement wall.
Its missing cell is derived from disjointness with the empty incoming tile. -/
theorem LocalPatch.incomplete_empty_negative_wall {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (R : LocalPatch d σ r) (hd : 3 ≤ d)
    (hincomplete : ¬ ∀ a, Proper a → R.incoming a)
    (hempty : R.incoming (emptyRole d)) (j : Fin d) :
    ∃ q ∈ R.tiles, boxLower q = wallBox j false ∧
      hole q = fun i => -unitAxis j i := by
  obtain ⟨q, hq, hb⟩ := R.fanData.incomplete_all_walls hd hincomplete j false
  refine ⟨q, hq, hb, ?_⟩
  obtain ⟨e, he, hge⟩ := hempty
  have heOwn : Occupies e (fun i => -unitAxis j i) := by
    rw [← exterior_empty]
    exact (gauge_occupies_iff hge _).mp (incoming_owns_exterior _ _ j)
  have hn : ¬ Occupies q (fun i => -unitAxis j i) := by
    intro hqOwn
    have hqe := R.disjoint q hq e he _ hqOwn heOwn
    have heBox : boxLower e = fun _ => (-1 : ℤ) := by
      rw [← gauge_boxLower_eq hge, incoming_boxLower]
      rfl
    have h := congrFun (hb.symm.trans (hqe ▸ heBox)) j
    simp [wallBox] at h
  have hbox : ∀ i, -unitAxis j i = boxLower q i ∨
      -unitAxis j i = boxLower q i + 1 := by
    intro i
    rw [congrFun hb i]
    by_cases h : i = j <;> simp [wallBox, unitAxis, h]
  by_contra hh
  exact hn ((occupies_box_iff q _).mpr ⟨hbox, fun h => hh h.symm⟩)

/-- Independent local patches in charts differing by +1. The guard applies
only to actual overlapping cells and permits coincident physical tiles. -/
def H0CrossCompatible {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (S R : LocalPatch d σ r) : Prop :=
  ∀ p ∈ S.tiles, ∀ q ∈ R.tiles, ∀ c,
    Occupies p c → Occupies (shiftOne q) c → GaugeRel r p (shiftOne q)

/-- The H0 two-corona dichotomy. Neither corona is assumed complete and no
transported tile is required to occur in the first root-excluding index set. -/
theorem h0_two_corona_completion {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (S R : LocalPatch d σ r) (hd : 3 ≤ d)
    (cross : H0CrossCompatible S R) (hempty : R.incoming (emptyRole d)) :
    (∀ a, Proper a → S.incoming a) ∨ (∀ a, Proper a → R.incoming a) := by
  classical
  by_cases hR : ∀ a, Proper a → R.incoming a
  · exact Or.inr hR
  · let j : Fin d := ⟨0, by omega⟩
    let k : Fin d := ⟨1, by omega⟩
    have hkj : k ≠ j := by intro h; have := congrArg Fin.val h; simp [j, k] at this
    let a : Bits d := fun i => decide (i ≠ j)
    have ha : Proper a := ⟨j, by simp [a]⟩
    have hna : NonemptyRole a := ⟨k, by simp [a, hkj]⟩
    obtain ⟨q, hq, hb, hh⟩ := R.incomplete_empty_negative_wall hd hR hempty j
    have hshiftBox : boxLower (shiftOne q) = fun i => 2 * bit a i - 1 := by
      rw [shiftOne_boxLower, hb]
      funext i
      by_cases h : i = j <;> simp [wallBox, bit, a, h]
    have hshiftHole : hole (shiftOne q) = fun i => bit a i := by
      rw [shiftOne_hole, hh]
      funext i
      by_cases h : i = j <;> simp [unitAxis, bit, a, h]
    obtain ⟨p, hp, hpx⟩ := S.covers a ha j
    have hqx : Occupies (shiftOne q) (exterior a j) := by
      have h := incoming_owns_exterior a (σ a) j
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
      · exact ⟨j, by simp [bit, a]⟩
    have incoming : S.incoming a := by
      refine ⟨p, hp, ?_⟩
      simpa [hrole] using ((S.catalog p hp).2.1 his).2
    exact Or.inl (S.complete_of_nonempty_incoming hd ha hna incoming)

#print axioms LocalPatch.incomplete_empty_negative_wall
#print axioms h0_two_corona_completion
end SparseMonotiles.CarrierHierarchy
