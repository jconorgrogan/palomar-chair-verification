module

public import PhysicalRegistration.NativeBoundaryPlanes
public import PhysicalRegistration.KeyNormalRank

@[expose] public section

/-!
# Orthogonal coordinate control of untouched carrier contacts

The actual carrier is regular closed. If the coordinate planes through a point
have normals in one two-vector span, at most two coordinate axes can be active.
The previously derived local Boolean germ then depends on at most two
orthogonal coordinate signs; no ordinary-sector angle is assumed.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Native coordinate planes through a point, ignoring repeated plane labels. -/
def activeCarrierAxes {m : ℕ} (x : Space m) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun i => x i = 0 ∨ x i = 1 ∨ x i = 2)

theorem coordinate_three_linearIndependent {m : ℕ} (i j k : Fin (m + 1))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    LinearIndependent ℝ ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j (1 : ℝ),
      EuclideanSpace.single k (1 : ℝ)] := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg l
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two] at hg
  have hi := congrArg (fun v : Space m => v i) hg
  have hj := congrArg (fun v : Space m => v j) hg
  have hk := congrArg (fun v : Space m => v k) hg
  simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] at hi hj hk
  fin_cases l <;> assumption

/-- A two-dimensional transverse normal space cannot contain three distinct
orthogonal coordinate-plane normals. -/
theorem activeCarrierAxes_card_le_two {m : ℕ} (x p q : Space m)
    (hspan : ∀ i ∈ activeCarrierAxes x,
      EuclideanSpace.single i (1 : ℝ) ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (activeCarrierAxes x).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ :=
    Finset.two_lt_card.mp (by omega : 2 < (activeCarrierAxes x).card)
  exact three_independent_not_mem_span_pair _ _ _ p q
    (coordinate_three_linearIndependent i j k hij hik hjk)
    ⟨hspan i hi, hspan j hj, hspan k hk⟩

/-- Strict coordinate margins plus a strict coordinate below the missing
corner give an actual open subset of the carrier. -/
theorem strict_carrier_mem_interior {m : ℕ} (x : Space m)
    (hbox : ∀ i, 0 < x i ∧ x i < 2) (hmissing : ∃ i, x i < 1) :
    x ∈ interior (carrier m) := by
  let U : Set (Space m) := {y | (∀ i, 0 < y i ∧ y i < 2) ∧ ∃ i, y i < 1}
  have hU : IsOpen U := by
    unfold U
    simp only [ofPred_and, ofPred_forall, ofPred_exists]
    apply IsOpen.inter
    · apply isOpen_iInter_of_finite
      intro i
      exact (isOpen_lt continuous_const (by fun_prop)).inter
        (isOpen_lt (by fun_prop) continuous_const)
    · exact isOpen_iUnion (fun i => isOpen_lt (by fun_prop) continuous_const)
  have hsub : U ⊆ carrier m := by
    intro y hy
    rw [mem_carrier_iff]
    exact ⟨fun i => ⟨(hy.1 i).1.le, (hy.1 i).2.le⟩,
      hy.2.imp (fun _ h => h.le)⟩
  exact interior_maximal hsub hU ⟨hbox, hmissing⟩

/-- Every positive interpolation toward the literal retained cell center
enters the carrier's actual interior. -/
theorem carrier_combination_halfPoint_mem_interior {m : ℕ} (x : Space m)
    (hx : x ∈ carrier m) (t : ℝ) (ht : 0 < t) (htone : t ≤ 1) :
    (1 - t) • x + t • halfPoint m ∈ interior (carrier m) := by
  have hb := (mem_carrier_iff x).mp hx
  apply strict_carrier_mem_interior
  · intro i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, halfPoint]
    have hh := hb.1 i
    have hnonneg := mul_nonneg (sub_nonneg.mpr htone) hh.1
    have hupper := mul_le_mul_of_nonneg_left hh.2 (sub_nonneg.mpr htone)
    constructor <;> nlinarith
  · obtain ⟨i, hi⟩ := hb.2
    refine ⟨i, ?_⟩
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, halfPoint]
    have hupper := mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr htone)
    nlinarith

/-- Thus the literal carrier has no boundary-only appendages. -/
theorem closure_interior_carrier (m : ℕ) : closure (interior (carrier m)) = carrier m := by
  apply subset_antisymm
  · exact closure_minimal interior_subset (carrier_isClosed m)
  · intro x hx
    exact mem_closure_of_positive_interpolation x (halfPoint m)
      (carrier_combination_halfPoint_mem_interior x hx)

/-- At a carrier point, all local membership information is carried by the
signs of the active coordinate planes. Combined with `activeCarrierAxes_card_le_two`,
this is a literal at-most-two-orthogonal-axis Boolean germ. -/
theorem carrier_local_active_sign_germ {m : ℕ} (x : Space m) (hx : x ∈ carrier m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U,
      (∀ i ∈ activeCarrierAxes x,
        (y i ≤ x i ↔ z i ≤ x i) ∧ (x i ≤ y i ↔ x i ≤ z i)) →
      (y ∈ carrier m ↔ z ∈ carrier m) := by
  obtain ⟨U, hU, hxU, heq⟩ := carrier_local_coordinate_germ x hx
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy z hz hsign
  rw [heq y hy, heq z hz]
  have hzero (i : Fin (m + 1)) (hi : x i = 0) : (0 ≤ y i ↔ 0 ≤ z i) := by
    have h := (hsign i (by simp [activeCarrierAxes, hi])).2
    simpa [hi] using h
  have htwo (i : Fin (m + 1)) (hi : x i = 2) : (y i ≤ 2 ↔ z i ≤ 2) := by
    have h := (hsign i (by simp [activeCarrierAxes, hi])).1
    simpa [hi] using h
  have hone (i : Fin (m + 1)) (hi : x i = 1) : (y i ≤ 1 ↔ z i ≤ 1) := by
    have h := (hsign i (by simp [activeCarrierAxes, hi])).1
    simpa [hi] using h
  constructor
  · rintro ⟨hbound, i, hi⟩
    refine ⟨fun j => ⟨fun hj => (hzero j hj).mp ((hbound j).1 hj),
      fun hj => (htwo j hj).mp ((hbound j).2 hj)⟩, i, ?_⟩
    rcases hi with hi | ⟨he, hi⟩
    · exact Or.inl hi
    · exact Or.inr ⟨he, (hone i he).mp hi⟩
  · rintro ⟨hbound, i, hi⟩
    refine ⟨fun j => ⟨fun hj => (hzero j hj).mpr ((hbound j).1 hj),
      fun hj => (htwo j hj).mpr ((hbound j).2 hj)⟩, i, ?_⟩
    rcases hi with hi | ⟨he, hi⟩
    · exact Or.inl hi
    · exact Or.inr ⟨he, (hone i he).mpr hi⟩

#print axioms coordinate_three_linearIndependent
#print axioms activeCarrierAxes_card_le_two
#print axioms carrier_combination_halfPoint_mem_interior
#print axioms closure_interior_carrier
#print axioms carrier_local_active_sign_germ
end
end PhysicalRegistration.NativeChair
