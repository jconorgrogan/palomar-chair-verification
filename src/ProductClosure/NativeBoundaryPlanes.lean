module

public import ProductClosure.BoundaryClassification
public import ProductClosure.NativeAngleSeparation
public import ProductClosure.CarrierCoordinateGerm

@[expose] public section

/-! Finite supporting-plane coverage for the literal compiled polycube boundary. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell S)]

/-- Literal finite list: integer carrier coordinate planes and all native
affine side planes. It deliberately permits redundant planes. -/
abbrev BoundaryPlaneIndex (S : Finset (Polycube.LatticeIndex (m + 1))) :=
  CarrierPlaneIndex S ⊕ (Site S × Side m)

def boundaryPlane {J : ℕ} (a : Coefficients S J) : BoundaryPlaneIndex S → Set (Space m)
  | .inl b => {x | x b.2.1 = carrierPlaneLevel b}
  | .inr (u, s) => {x | ⟪sideNormal a u s, x - siteCenter u⟫_ℝ =
      eta m * (a.value u : ℝ) / denominator m J}

theorem body_frontier_subset_boundaryPlanes {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients S J) : frontier (body a) ⊆ ⋃ b : BoundaryPlaneIndex S, boundaryPlane a b := by
  intro x hx
  rw [frontier_body_eq_keyGraphs_union_untouched_carrier hm a] at hx
  rcases hx with hx | hx
  · obtain ⟨u, hu⟩ := mem_iUnion.mp hx
    rw [keyGraph_eq_iUnion_sideFace] at hu
    obtain ⟨s, hs⟩ := mem_iUnion.mp hu
    exact mem_iUnion.mpr ⟨.inr (u, s), sideFace_plane a u s x hs⟩
  · obtain ⟨c, i, hi⟩ := carrier_frontier_coordinate S x hx.1
    rcases hi with hi | hi
    · exact mem_iUnion.mpr ⟨.inl (c, i, false), by simpa [boundaryPlane, carrierPlaneLevel] using hi⟩
    · exact mem_iUnion.mpr ⟨.inl (c, i, true), by simpa [boundaryPlane, carrierPlaneLevel] using hi⟩

def boundaryPlaneNormal {J : ℕ} (a : Coefficients S J) : BoundaryPlaneIndex S → Space m
  | .inl b => EuclideanSpace.single b.2.1 1
  | .inr (u, s) => sideNormal a u s

def boundaryPlaneCenter  : BoundaryPlaneIndex S → Space m
  | .inl _ => 0
  | .inr (u, _) => siteCenter u

def boundaryPlaneLevel {J : ℕ} (a : Coefficients S J) : BoundaryPlaneIndex S → ℝ
  | .inl b => carrierPlaneLevel b
  | .inr (u, _) => eta m * (a.value u : ℝ) / denominator m J

theorem boundaryPlane_eq_affine {J : ℕ} (a : Coefficients S J)
    (b : BoundaryPlaneIndex S) : boundaryPlane a b =
      {x | ⟪boundaryPlaneNormal a b, x - boundaryPlaneCenter b⟫_ℝ = boundaryPlaneLevel a b} := by
  cases b with
  | inl ik => simp [boundaryPlane, boundaryPlaneNormal, boundaryPlaneCenter,
      boundaryPlaneLevel, EuclideanSpace.inner_single_left]
  | inr us => rfl

theorem boundaryPlaneNormal_ne_zero {J : ℕ} (a : Coefficients S J)
    (b : BoundaryPlaneIndex S) : boundaryPlaneNormal a b ≠ 0 := by
  cases b with
  | inl ik =>
      have hnorm : ‖boundaryPlaneNormal a (.inl ik)‖ = 1 := by
        simp [boundaryPlaneNormal]
      intro hz
      simp [hz] at hnorm
  | inr us => exact sideNormal_ne_zero a us.1 us.2

/-- Each arbitrary placed plane has an explicit transported normal and center. -/
theorem image_boundaryPlane_eq {J : ℕ} (a : Coefficients S J)
    (b : BoundaryPlaneIndex S) (f : Space m ≃ᵢ Space m) :
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
theorem placed_body_frontier_subset_boundaryPlanes {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients S J) (f : Space m ≃ᵢ Space m) :
    frontier (placedBody a f) ⊆ ⋃ b : BoundaryPlaneIndex S,
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

#print axioms body_frontier_subset_boundaryPlanes
#print axioms boundaryPlaneNormal_ne_zero
#print axioms image_boundaryPlane_eq
#print axioms placed_body_frontier_subset_boundaryPlanes
end
end ProductClosure.NativeCompiler
