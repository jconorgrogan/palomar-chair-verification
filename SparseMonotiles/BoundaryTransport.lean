module

public import SparseMonotiles.SkeletonClearance
public import SparseMonotiles.KeyDiameters

@[expose] public section

/-!
# Local boundary facts for arbitrary physical placements

The tiling model permits every Euclidean isometry, including reflections and
unregistered rotations. These lemmas transport local equality and metric key
clearance by precisely those maps. No integer-frame registration is assumed.
-/

namespace SparseMonotiles

open Set

/-- A set germ transports by any homeomorphism. -/
theorem LocalSetEq.image_homeomorph {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (g : X ≃ₜ Y)
    {p : X} {S T : Set X} (h : LocalSetEq p S T) :
    LocalSetEq (g p) (g '' S) (g '' T) := by
  obtain ⟨U, hU, hp, hEq⟩ := h.exists_open
  apply LocalSetEq.of_open (g.isOpen_image.mpr hU) (Set.mem_image_of_mem g hp)
  rintro _ ⟨x, hx, rfl⟩
  simpa only [Set.mem_image, g.injective.eq_iff, exists_eq_right] using hEq x hx

/-- In particular the geometric germ is preserved by every allowed tile frame. -/
theorem LocalSetEq.image_isometry {d : ℕ} (g : Point d ≃ᵢ Point d)
    {p : Point d} {S T : Set (Point d)} (h : LocalSetEq p S T) :
    LocalSetEq (g p) (g '' S) (g '' T) :=
  h.image_homeomorph g.toHomeomorph

/-- A strict clearance bound remains true in an arbitrary physical frame. -/
theorem isometry_image_clearance {d : ℕ} (g : Point d ≃ᵢ Point d)
    {S K : Set (Point d)} {r : ℝ}
    (h : ∀ x ∈ K, ∀ p ∈ S, r < dist x p) :
    ∀ x ∈ g '' K, ∀ p ∈ g '' S, r < dist x p := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨p, hp, rfl⟩
  rw [g.dist_eq]
  exact h x hx p hp

/-- A small set touching a clear key cannot also reach the forbidden skeleton.
The small set may lie in a completely unrelated physical frame. -/
theorem disjoint_of_small_diameter_and_clearance {d : ℕ}
    {K L S : Set (Point d)} {r : ℝ}
    (hclear : ∀ x ∈ K, ∀ p ∈ S, r < dist x p)
    (hsmall : ∀ x ∈ L, ∀ y ∈ L, dist x y < r)
    (hmeet : (K ∩ L).Nonempty) : Disjoint L S := by
  obtain ⟨x, hxK, hxL⟩ := hmeet
  apply Set.disjoint_left.mpr
  intro p hpL hpS
  exact (lt_asymm (hclear x hxK p hpS) (hsmall x hxL p hpL))

#print axioms LocalSetEq.image_isometry
#print axioms isometry_image_clearance
#print axioms disjoint_of_small_diameter_and_clearance

end SparseMonotiles
