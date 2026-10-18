module

public import ProductClosure.GenericComplementaryKeys
public import ProductClosure.ComplementaryBaseLabels

@[expose] public section

/-!
# Actual dense base-label matching in a physical tiling

The actual two-incidence theorem supplies complementary measured masses.
Their native label rigidity therefore applies without a matching, angle,
angular-conservation or incidence premise in the physical-tiling endpoint.
At every point of the constructed dense set there is exactly one other
incident tile, whose actual generic base crease has the same full side label
and the opposite signed coefficient.

This does not assert that the companion tile is constant along a whole key.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
open TransversePlaneCoordinates
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Actual complementary incidence at a specified root base retains that
complete native side label and negates the signed coefficient. -/
theorem ComplementaryKeyPair.other_base_labels
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m) {a : Coefficients polyCells J}
    {f : ι → Space m ≃ᵢ Space m} {x p q : Space m}
    {F : ActualFiniteConicalFan a f x p q} {h : LinearIndependent ℝ ![p, q]}
    {root other : incidentTiles a f x} (H : ComplementaryKeyPair F h root other)
    (u : Site polyCells) (s : Side m)
    (hx : (f root.val).symm x ∈ genericBaseCrease a u s)
    (hplanes : ∀ i, x ∈ placedBody a (f i) → ∀ z : BoundaryPlaneIndex polyCells,
      x ∈ f i '' boundaryPlane a z →
        placedNormal (f i) (boundaryPlaneNormal a z) ∈ normalSpan p q) :
    ∃ v : Site polyCells, (f other.val).symm x ∈ genericBaseCrease a v s ∧
      |a.value u| = |a.value v| ∧ a.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value v : ℝ)) :=
  (F.germs root).complementary_base_labels hm (F.germs other) u s hx
    H.other_crease h (hplanes root.val root.property)
    (hplanes other.val other.property) H.mass_sum

/-- Every placed base crease has a dense set of actual exactly-two-tile
contacts with preserved full side label and opposite signed coefficient.
No companion, contact, normal-span or mass-balance premise is supplied. -/
theorem PhysicalTiling.genericBaseCrease_labelled_companions
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) (s : Side m) :
    ∃ D : Set (Space m), D ⊆ f root '' genericBaseCrease a u s ∧
      closure D = f root '' baseCrease a u s ∧
      ∀ x ∈ D, ∃ other : ι, other ≠ root ∧
        incidentTiles a f x = {root, other} ∧
        ∃ v : Site polyCells, x ∈ f other '' genericBaseCrease a v s ∧
          |a.value u| = |a.value v| ∧ a.value v = -a.value u ∧
          decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value v : ℝ)) := by
  obtain ⟨D, hDG, hDC, hD⟩ := T.genericBaseCrease_complementary_keys hm root u s
  refine ⟨D, hDG, hDC, fun x hx => ?_⟩
  obtain ⟨hplanes, _, F, hr, other, H, _⟩ := hD x hx
  obtain ⟨y, hy, hxy⟩ := hDG hx
  have hpre : (f root).symm x ∈ genericBaseCrease a u s := by
    simpa [← hxy] using hy
  obtain ⟨v, hv, habs, hneg, hsign⟩ := H.other_base_labels hm u s hpre hplanes
  refine ⟨other.val, fun he => H.distinct (Subtype.ext he), H.incidentTiles_eq_pair,
    v, ?_, habs, hneg, hsign⟩
  exact ⟨(f other.val).symm x, hv, (f other.val).apply_symm_apply x⟩

end
end ProductClosure.NativeCompiler
