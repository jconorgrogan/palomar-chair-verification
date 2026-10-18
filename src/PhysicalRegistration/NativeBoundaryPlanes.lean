module

public import PhysicalRegistration.BoundaryClassification
public import PhysicalRegistration.NativeAngleSeparation

@[expose] public section

/-!
# Finite affine supporting-plane cover of the actual native boundary

The untouched carrier has a derived local coordinate Boolean germ. Together
with the exact boundary decomposition and affine side coverage, this gives a
literal finite list of planes covering every actual physical boundary point.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Exact coordinate germ of the carrier at any carrier point. Only planes
through the selected point remain as inequalities in the resulting formula. -/
theorem carrier_local_coordinate_germ {m : ℕ} (x : Space m) (hx : x ∈ carrier m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      (y ∈ carrier m ↔
        (∀ i, (x i = 0 → 0 ≤ y i) ∧ (x i = 2 → y i ≤ 2)) ∧
          ∃ i, x i < 1 ∨ (x i = 1 ∧ y i ≤ 1)) := by
  let U : Set (Space m) := {y | ∀ i : Fin (m + 1),
    (0 < x i → 0 < y i) ∧ (x i < 2 → y i < 2) ∧
    (x i < 1 → y i < 1) ∧ (1 < x i → 1 < y i)}
  have hU : IsOpen U := by
    unfold U
    simp only [ofPred_forall, ofPred_and]
    apply isOpen_iInter_of_finite
    intro i
    have hcont : Continuous (fun y : Space m => y i) := by fun_prop
    have h0 : IsOpen {y : Space m | 0 < x i → 0 < y i} := by
      by_cases h : 0 < x i
      · simpa only [h, true_implies] using isOpen_lt continuous_const hcont
      · simp [h]
    have h2 : IsOpen {y : Space m | x i < 2 → y i < 2} := by
      by_cases h : x i < 2
      · simpa only [h, true_implies] using isOpen_lt hcont (continuous_const (y := (2 : ℝ)))
      · simp [h]
    have hm : IsOpen {y : Space m | x i < 1 → y i < 1} := by
      by_cases h : x i < 1
      · simpa only [h, true_implies] using isOpen_lt hcont (continuous_const (y := (1 : ℝ)))
      · simp [h]
    have hp : IsOpen {y : Space m | 1 < x i → 1 < y i} := by
      by_cases h : 1 < x i
      · simpa only [h, true_implies] using isOpen_lt (continuous_const (y := (1 : ℝ))) hcont
      · simp [h]
    simpa only [ofPred_forall] using h0.inter (h2.inter (hm.inter hp))
  refine ⟨U, hU, (by intro i; exact ⟨id, id, id, id⟩), ?_⟩
  intro y hy
  have hxb := (mem_carrier_iff x).mp hx
  rw [mem_carrier_iff]
  constructor
  · intro hyc
    constructor
    · intro i
      exact ⟨fun _ => (hyc.1 i).1, fun _ => (hyc.1 i).2⟩
    · obtain ⟨i, hi⟩ := hyc.2
      refine ⟨i, ?_⟩
      by_cases h : x i < 1
      · exact Or.inl h
      · have hxi : x i ≤ 1 := le_of_not_gt (fun hgt =>
          (not_lt_of_ge hi) ((hy i).2.2.2 hgt))
        exact Or.inr ⟨le_antisymm hxi (le_of_not_gt h), hi⟩
  · intro hyc
    constructor
    · intro i
      constructor
      · by_cases h : x i = 0
        · exact (hyc.1 i).1 h
        · exact ((hy i).1 (lt_of_le_of_ne (hxb.1 i).1 (Ne.symm h))).le
      · by_cases h : x i = 2
        · exact (hyc.1 i).2 h
        · exact ((hy i).2.1 (lt_of_le_of_ne (hxb.1 i).2 h)).le
    · obtain ⟨i, hi⟩ := hyc.2
      refine ⟨i, ?_⟩
      rcases hi with hi | hi
      · exact ((hy i).2.2.1 hi).le
      · exact hi.2

/-- Any actual carrier boundary point lies on an integer coordinate plane. -/
theorem carrier_frontier_coordinate {m : ℕ} (x : Space m) (hx : x ∈ frontier (carrier m)) :
    ∃ i : Fin (m + 1), x i = 0 ∨ x i = 1 ∨ x i = 2 := by
  have hxC : x ∈ carrier m := (carrier_isClosed m).frontier_subset hx
  obtain ⟨U, hU, hxU, heq⟩ := carrier_local_coordinate_germ x hxC
  by_contra! h
  have hUC : U ⊆ carrier m := by
    intro y hy
    apply (heq y hy).mpr
    constructor
    · intro i
      exact ⟨fun hi => (h i).1 hi |>.elim, fun hi => (h i).2.2 hi |>.elim⟩
    · obtain ⟨i, hi⟩ := ((mem_carrier_iff x).mp hxC).2
      exact ⟨i, Or.inl (lt_of_le_of_ne hi (h i).2.1)⟩
  have hxint : x ∈ interior (carrier m) := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hxU) hUC)
  exact hx.2 hxint

/-- Literal finite list: integer carrier coordinate planes and all native
affine side planes. It deliberately permits redundant planes. -/
abbrev BoundaryPlaneIndex (m : ℕ) :=
  (Fin (m + 1) × Fin 3) ⊕ (Site m × Side m)

def boundaryPlane {m J : ℕ} (a : Coefficients m J) : BoundaryPlaneIndex m → Set (Space m)
  | .inl (i, k) => {x | x i = (k.val : ℝ)}
  | .inr (u, s) => {x | ⟪sideNormal a u s, x - siteCenter u⟫_ℝ =
      eta m * (a.value u : ℝ) / denominator m J}

theorem body_frontier_subset_boundaryPlanes {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) : frontier (body a) ⊆ ⋃ b : BoundaryPlaneIndex m, boundaryPlane a b := by
  intro x hx
  rw [frontier_body_eq_keyGraphs_union_untouched_carrier hm a] at hx
  rcases hx with hx | hx
  · obtain ⟨u, hu⟩ := mem_iUnion.mp hx
    rw [keyGraph_eq_iUnion_sideFace] at hu
    obtain ⟨s, hs⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨.inr (u, s), sideFace_plane a u s x hs⟩
  · obtain ⟨i, hi⟩ := carrier_frontier_coordinate x hx.1
    rcases hi with hi | hi | hi
    · exact mem_iUnion.mpr ⟨.inl (i, 0), by simpa [boundaryPlane] using hi⟩
    · exact mem_iUnion.mpr ⟨.inl (i, 1), by simpa [boundaryPlane] using hi⟩
    · exact mem_iUnion.mpr ⟨.inl (i, 2), by simpa [boundaryPlane] using hi⟩

def boundaryPlaneNormal {m J : ℕ} (a : Coefficients m J) : BoundaryPlaneIndex m → Space m
  | .inl (i, _) => EuclideanSpace.single i 1
  | .inr (u, s) => sideNormal a u s

def boundaryPlaneCenter {m : ℕ} : BoundaryPlaneIndex m → Space m
  | .inl _ => 0
  | .inr (u, _) => siteCenter u

def boundaryPlaneLevel {m J : ℕ} (a : Coefficients m J) : BoundaryPlaneIndex m → ℝ
  | .inl (_, k) => k.val
  | .inr (u, _) => eta m * (a.value u : ℝ) / denominator m J

theorem boundaryPlane_eq_affine {m J : ℕ} (a : Coefficients m J)
    (b : BoundaryPlaneIndex m) : boundaryPlane a b =
      {x | ⟪boundaryPlaneNormal a b, x - boundaryPlaneCenter b⟫_ℝ = boundaryPlaneLevel a b} := by
  cases b with
  | inl ik => simp [boundaryPlane, boundaryPlaneNormal, boundaryPlaneCenter,
      boundaryPlaneLevel, EuclideanSpace.inner_single_left]
  | inr us => rfl

theorem boundaryPlaneNormal_ne_zero {m J : ℕ} (a : Coefficients m J)
    (b : BoundaryPlaneIndex m) : boundaryPlaneNormal a b ≠ 0 := by
  cases b with
  | inl ik =>
      have hnorm : ‖boundaryPlaneNormal a (.inl ik)‖ = 1 := by
        simp [boundaryPlaneNormal]
      intro hz
      simp [hz] at hnorm
  | inr us => exact sideNormal_ne_zero a us.1 us.2

/-- Each arbitrary placed plane has an explicit transported normal and center. -/
theorem image_boundaryPlane_eq {m J : ℕ} (a : Coefficients m J)
    (b : BoundaryPlaneIndex m) (f : Space m ≃ᵢ Space m) :
    f '' boundaryPlane a b =
      {y | ⟪placedNormal f (boundaryPlaneNormal a b), y - f (boundaryPlaneCenter b)⟫_ℝ =
        boundaryPlaneLevel a b} := by
  have hmap (x : Space m) :
      ⟪placedNormal f (boundaryPlaneNormal a b), f x - f (boundaryPlaneCenter b)⟫_ℝ =
        ⟪boundaryPlaneNormal a b, x - boundaryPlaneCenter b⟫_ℝ := by
    have hv := f.toRealAffineIsometryEquiv.map_vsub x (boundaryPlaneCenter b)
    change f.toRealAffineIsometryEquiv.linearIsometryEquiv (x - boundaryPlaneCenter b) =
      f x - f (boundaryPlaneCenter b) at hv
    rw [← hv]
    exact f.toRealAffineIsometryEquiv.linearIsometryEquiv.inner_map_map _ _
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ⟪placedNormal f (boundaryPlaneNormal a b), f x - f (boundaryPlaneCenter b)⟫_ℝ = _
    rw [hmap]
    simpa only [boundaryPlane_eq_affine, mem_ofPred_eq] using hx
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    rw [boundaryPlane_eq_affine]
    change ⟪boundaryPlaneNormal a b, f.symm y - boundaryPlaneCenter b⟫_ℝ = _
    rw [← hmap, f.apply_symm_apply]
    exact hy

/-- The finite affine plane cover survives unrestricted ambient placements. -/
theorem placed_body_frontier_subset_boundaryPlanes {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (f : Space m ≃ᵢ Space m) :
    frontier (placedBody a f) ⊆ ⋃ b : BoundaryPlaneIndex m,
      {y | ⟪placedNormal f (boundaryPlaneNormal a b), y - f (boundaryPlaneCenter b)⟫_ℝ =
        boundaryPlaneLevel a b} := by
  intro y hy
  change y ∈ frontier (f.toHomeomorph '' body a) at hy
  rw [← f.toHomeomorph.image_frontier] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨b, hb⟩ := mem_iUnion.mp (body_frontier_subset_boundaryPlanes hm a hx)
  apply mem_iUnion.mpr
  refine ⟨b, ?_⟩
  rw [← image_boundaryPlane_eq]
  exact ⟨x, hb, rfl⟩

#print axioms carrier_local_coordinate_germ
#print axioms carrier_frontier_coordinate
#print axioms body_frontier_subset_boundaryPlanes
#print axioms boundaryPlaneNormal_ne_zero
#print axioms image_boundaryPlane_eq
#print axioms placed_body_frontier_subset_boundaryPlanes
end
end PhysicalRegistration.NativeChair
