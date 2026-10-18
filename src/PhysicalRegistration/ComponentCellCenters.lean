module

public import PhysicalRegistration.NativeLatticeCells
public import PhysicalRegistration.IntegralPoseGroup

@[expose] public section

/-! Literal lattice-cell centers in one actual key-companion component.
Reachability is generated only by whole physical key contacts. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

theorem latticeCenter_injective {m : ℕ} :
    Function.Injective (latticeCenter (m := m)) := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Space m => x i) h
  change (z i : ℝ) + 1 / 2 = (w i : ℝ) + 1 / 2 at hi
  have he : (z i : ℝ) = (w i : ℝ) := by linarith
  exact_mod_cast he

theorem isometry_map_add_smul {m : ℕ} (f : Space m ≃ᵢ Space m)
    (x v : Space m) (r : ℝ) :
    f (x + r • v) = f x + r • placedNormal f v := by
  have h := affineIsometry_map_add f.toRealAffineIsometryEquiv x (r • v)
  simpa [placedNormal] using h

/-- A geometrically matched companion's inward cell is the root facet's
literal outward adjacent cell, at the level of actual placed centers. -/
theorem matched_companion_cellCenter {m : ℕ} (u v : Site m)
    (f g : Space m ≃ᵢ Space m)
    (ht : ∀ j, placedNormal g (siteAxis v j) = placedNormal f (siteAxis u j))
    (hn : placedNormal g (outward v.1) = -placedNormal f (outward u.1))
    (hc : f (siteCenter u) = g (siteCenter v)) :
    g (cellCenter (facetInsideCell v.1)) = f (latticeCenter (facetOutsideIndex u.1)) := by
  have hfacet : g (facetCenter v.1) = f (facetCenter u.1) := by
    have h := relativePlacement_facetCenter u v f g ht hc
    have hh := congrArg f h
    simpa [relativePlacement] using hh
  rw [facetInsideCell_center, facetOutsideIndex_center]
  rw [sub_eq_add_neg, ← neg_smul, isometry_map_add_smul, isometry_map_add_smul,
    hfacet, hn, smul_neg, neg_smul, neg_neg]

/-- A component owns a lattice cell when its literal native occupied-cell
center maps to that lattice center in root coordinates. Registration will
turn this into equality of the entire closed unit cells. -/
def PhysicalTiling.ComponentCell {m J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (z : LatticeIndex m) : Prop :=
  ∃ i, T.KeyReachable root i ∧ ∃ c : Cell m,
    relativePlacement (f root) (f i) (cellCenter c) = latticeCenter z

theorem PhysicalTiling.componentCell_nonempty {m J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) :
    ∃ z, T.ComponentCell root z := by
  refine ⟨cellIndex (zeroCell m), root, T.keyReachable_refl root, zeroCell m, ?_⟩
  simp [relativePlacement, latticeCenter_cellIndex]

/-- Every exposed native facet of a reachable tile supplies its actual
outside-cell center from another reachable tile. -/
theorem PhysicalTiling.exists_reachable_outside_center
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root i : ι} (hi : T.KeyReachable root i) (F : Facet m) :
    ∃ j, T.KeyReachable root j ∧ ∃ c : Cell m,
      relativePlacement (f root) (f j) (cellCenter c) =
        relativePlacement (f root) (f i) (latticeCenter (facetOutsideIndex F)) := by
  let u : Site m := (F, Equiv.refl _, fun _ => true)
  obtain ⟨iv, hiv, _⟩ := T.unique_framed_key_companion hm i u
  have hreach : T.KeyReachable root iv.1 :=
    hi.tail ⟨Ne.symm hiv.1, u, iv.2, hiv.2.1⟩
  refine ⟨iv.1, hreach, facetInsideCell iv.2.1, ?_⟩
  have hc := matched_companion_cellCenter u iv.2 (f i) (f iv.1)
    hiv.2.2.1 hiv.2.2.2.1 hiv.2.2.2.2.1
  have hh := congrArg (f root).symm hc
  exact hh

end
end PhysicalRegistration.NativeChair
