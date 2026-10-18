module

public import ProductClosure.NativeKeySectorMass

@[expose] public section

/-!
# Labels of an actual complementary base incidence

Actual generic body germs give measured deviations from pi. Complementary
masses have equal absolute deviations, so the checked prime separation of
actual normal angles excludes a distinct-axis side companion and identifies
the complete base-side label and coefficient magnitude. The actual material
mass formulas also force opposite union/intersection signs.

The mass-sum premise here is intended for the already derived actual fan
conservation theorem. No preserved-angle, preserved-label or matching premise
is supplied, and the two placements are unrestricted independent isometries.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
open TransversePlaneCoordinates
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

private theorem abs_pi_deviation {δ : ℝ} (hδ : 0 ≤ δ)
    (P : Prop) [Decidable P] :
    |(if P then Real.pi + δ else Real.pi - δ) - Real.pi| = δ := by
  split_ifs <;> simp only [add_sub_cancel_left, sub_sub_cancel_left, abs_neg,
    abs_of_nonneg hδ]

private theorem complementary_abs_deviations {α β : ℝ}
    (hsum : α + β = 2 * Real.pi) : |α - Real.pi| = |β - Real.pi| := by
  have he : α - Real.pi = -(β - Real.pi) := by linarith
  rw [he, abs_neg]

/-- The chosen actual germ has the literal base mass, independently of its
initially selected native-shape witness. -/
theorem ActualTwoNormalGerm.transverseMass_base_eq
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site polyCells) (s : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q) :
    transverseMass p q h G.cone =
      if 0 < (a.value u : ℝ) then
        Real.pi + InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (outward u.1))
      else Real.pi - InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (outward u.1)) := by
  rw [G.cone_eq_base hm u s hx]
  obtain ⟨hn, hw⟩ := base_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s hx
  exact transverseMass_base hm a f u s p q h hn hw

/-- The analogous exact chosen-germ formula at an actual side-side point. -/
theorem ActualTwoNormalGerm.transverseMass_side_eq
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site polyCells) (s t : Side m)
    (hst : s.1 ≠ t.1) (hx : f.symm x ∈ genericSideCrease a u s t)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q) :
    transverseMass p q h G.cone =
      if (a.value u : ℝ) < 0 then
        Real.pi + InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (sideNormal a u t))
      else Real.pi - InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
          (placedNormal f (sideNormal a u t)) := by
  rw [G.cone_eq_side hm u s t hx]
  obtain ⟨hn, hw⟩ := side_normals_mem_rootSpan_of_boundary_span a f x p q hplanes u s t hx
  exact transverseMass_side hm a f u s t hst p q h hn hw

/-- The absolute measured deviation is the actual placed base normal angle. -/
theorem ActualTwoNormalGerm.transverseMass_base_deviation
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site polyCells) (s : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q) :
    |transverseMass p q h G.cone - Real.pi| =
      InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
        (placedNormal f (outward u.1)) := by
  rw [G.transverseMass_base_eq hm u s hx h hplanes]
  exact abs_pi_deviation (InnerProductGeometry.angle_nonneg _ _) _

/-- The absolute measured deviation is the actual placed side normal angle. -/
theorem ActualTwoNormalGerm.transverseMass_side_deviation
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (u : Site polyCells) (s t : Side m)
    (hst : s.1 ≠ t.1) (hx : f.symm x ∈ genericSideCrease a u s t)
    (h : LinearIndependent ℝ ![p, q])
    (hplanes : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q) :
    |transverseMass p q h G.cone - Real.pi| =
      InnerProductGeometry.angle (placedNormal f (sideNormal a u s))
        (placedNormal f (sideNormal a u t)) := by
  rw [G.transverseMass_side_eq hm u s t hst hx h hplanes]
  exact abs_pi_deviation (InnerProductGeometry.angle_nonneg _ _) _

/-- Complementary actual base masses identify both the magnitude and full
side label, and force opposite material union/intersection booleans. -/
theorem ActualTwoNormalGerm.complementary_base_base_labels
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a b : Coefficients polyCells J}
    {f g : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (H : ActualTwoNormalGerm b g x p q)
    (u v : Site polyCells) (s t : Side m)
    (hx : f.symm x ∈ genericBaseCrease a u s)
    (hy : g.symm x ∈ genericBaseCrease b v t)
    (h : LinearIndependent ℝ ![p, q])
    (hplanesG : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q)
    (hplanesH : ∀ z : BoundaryPlaneIndex polyCells, x ∈ g '' boundaryPlane b z →
      placedNormal g (boundaryPlaneNormal b z) ∈ normalSpan p q)
    (hsum : transverseMass p q h G.cone + transverseMass p q h H.cone = 2 * Real.pi) :
    |a.value u| = |b.value v| ∧ s = t ∧
      b.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (b.value v : ℝ)) := by
  have hang := complementary_abs_deviations hsum
  rw [G.transverseMass_base_deviation hm u s hx h hplanesG,
    H.transverseMass_base_deviation hm v t hy h hplanesH] at hang
  obtain ⟨habs, hlabel⟩ := placed_base_normal_angle_injective a b u v s t f g hang
  have hG := G.transverseMass_base_eq hm u s hx h hplanesG
  have hH := H.transverseMass_base_eq hm v t hy h hplanesH
  have hpos := (placed_base_normal_angle_bounds hm a u s f).1
  have hsign : decide (0 < (a.value u : ℝ)) ≠ decide (0 < (b.value v : ℝ)) := by
    intro he
    by_cases ha : 0 < (a.value u : ℝ) <;> by_cases hb : 0 < (b.value v : ℝ)
    · rw [ite_eq_left ha] at hG
      rw [ite_eq_left hb, ← hang] at hH
      linarith
    · simp [ha, hb] at he
    · simp [ha, hb] at he
    · rw [ite_eq_right ha] at hG
      rw [ite_eq_right hb, ← hang] at hH
      linarith
  refine ⟨habs, hlabel, ?_, hsign⟩
  have hneq : a.value u ≠ b.value v := by
    intro he
    apply hsign
    rw [he]
  rcases abs_eq_abs.mp habs with he | he
  · exact (hneq he).elim
  · omega

/-- A generic base and a generic distinct-axis side cannot have complementary
actual measured masses, even under independent unrestricted placements. -/
theorem ActualTwoNormalGerm.base_side_mass_ne_two_pi
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a b : Coefficients polyCells J}
    {f g : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (H : ActualTwoNormalGerm b g x p q)
    (u v : Site polyCells) (s t r : Side m) (htr : t.1 ≠ r.1)
    (hx : f.symm x ∈ genericBaseCrease a u s)
    (hy : g.symm x ∈ genericSideCrease b v t r)
    (h : LinearIndependent ℝ ![p, q])
    (hplanesG : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q)
    (hplanesH : ∀ z : BoundaryPlaneIndex polyCells, x ∈ g '' boundaryPlane b z →
      placedNormal g (boundaryPlaneNormal b z) ∈ normalSpan p q) :
    transverseMass p q h G.cone + transverseMass p q h H.cone ≠ 2 * Real.pi := by
  intro hsum
  have hang := complementary_abs_deviations hsum
  rw [G.transverseMass_base_deviation hm u s hx h hplanesG,
    H.transverseMass_side_deviation hm v t r htr hy h hplanesH] at hang
  exact placed_base_normal_angle_ne_side_normal_angle a b u v s t r htr f g hang

/-- An actual generic companion with complementary mass is a base crease
with exactly the root's full side label, opposite signed coefficient, and
opposite union/intersection sign. The base-or-side input retains literal
native point membership and supplies no matching or angle assumption. -/
theorem ActualTwoNormalGerm.complementary_base_labels
    {J : ℕ} [NeZero m] (hm : 2 ≤ m) {a b : Coefficients polyCells J}
    {f g : Space m ≃ᵢ Space m} {x p q : Space m}
    (G : ActualTwoNormalGerm a f x p q) (H : ActualTwoNormalGerm b g x p q)
    (u : Site polyCells) (s : Side m) (hx : f.symm x ∈ genericBaseCrease a u s)
    (hy : ∃ v : Site polyCells, (∃ t : Side m, g.symm x ∈ genericBaseCrease b v t) ∨
      ∃ t r : Side m, t.1 ≠ r.1 ∧ g.symm x ∈ genericSideCrease b v t r)
    (h : LinearIndependent ℝ ![p, q])
    (hplanesG : ∀ z : BoundaryPlaneIndex polyCells, x ∈ f '' boundaryPlane a z →
      placedNormal f (boundaryPlaneNormal a z) ∈ normalSpan p q)
    (hplanesH : ∀ z : BoundaryPlaneIndex polyCells, x ∈ g '' boundaryPlane b z →
      placedNormal g (boundaryPlaneNormal b z) ∈ normalSpan p q)
    (hsum : transverseMass p q h G.cone + transverseMass p q h H.cone = 2 * Real.pi) :
    ∃ v : Site polyCells, g.symm x ∈ genericBaseCrease b v s ∧
      |a.value u| = |b.value v| ∧ b.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (b.value v : ℝ)) := by
  obtain ⟨v, hy⟩ := hy
  rcases hy with ⟨t, ht⟩ | ⟨t, r, htr, htr'⟩
  · obtain ⟨habs, hlabel, hneg, hsign⟩ := G.complementary_base_base_labels hm H
      u v s t hx ht h hplanesG hplanesH hsum
    exact ⟨v, hlabel.symm ▸ ht, habs, hneg, hsign⟩
  · exact (G.base_side_mass_ne_two_pi hm H u v s t r htr hx htr' h
      hplanesG hplanesH hsum).elim

end
end ProductClosure.NativeCompiler
