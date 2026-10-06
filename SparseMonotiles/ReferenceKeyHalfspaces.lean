module

public import SparseMonotiles.CanonicalReferenceKeys
public import SparseMonotiles.PyramidGeometry

@[expose] public section

/-!
# Finite halfspaces for the actual Euclidean reference keys

The last coordinate is the normal coordinate. A linear equivalence splits it
from the tangential coordinates and binds `Model.keyBase` and `Model.keySolid`
to the already proved product-space pyramid geometry. Thus the inequalities
below describe the actual convex-hull solids, rather than an auxiliary shape.

The finite H-representation includes the redundant upper-height inequality.
It has ten inequalities in dimension five and fourteen in dimension seven.
The lower-height and lower-side choices use `false`, exactly as in
`PyramidGeometry`. Pullback by a physical pose keeps this convention intact.
-/
namespace SparseMonotiles

/-- Split the last Euclidean coordinate from the tangential coordinates. -/
noncomputable def pointPyramidEquiv (n : ℕ) : Point (n + 1) ≃ₗ[ℝ] PyramidPoint n where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (Fin.lastCases p.2 p.1)
  left_inv x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv p := by
    apply Prod.ext
    · funext i
      simp
    · simp
  map_add' x y := rfl
  map_smul' a x := rfl

@[simp] theorem pointPyramidEquiv_fst (n : ℕ) (x : Point (n + 1)) (i : Fin n) :
    (pointPyramidEquiv n x).1 i = x i.castSucc := rfl

@[simp] theorem pointPyramidEquiv_snd (n : ℕ) (x : Point (n + 1)) :
    (pointPyramidEquiv n x).2 = x (Fin.last n) := rfl

noncomputable def keyPyramidLo {n : ℕ} (k : KeyData (n + 1)) (i : Fin n) : ℝ :=
  (k.centre i.castSucc : ℝ) - (k.radius i.castSucc : ℝ)

noncomputable def keyPyramidHi {n : ℕ} (k : KeyData (n + 1)) (i : Fin n) : ℝ :=
  (k.centre i.castSucc : ℝ) + (k.radius i.castSucc : ℝ)

noncomputable def keyPyramidApex {n : ℕ} (k : KeyData (n + 1)) (i : Fin n) : ℝ :=
  (k.apex i.castSucc : ℝ)

noncomputable def keyPyramidHeight {n : ℕ} (k : KeyData (n + 1)) : ℝ :=
  (k.apex (Fin.last n) : ℝ)

@[simp] theorem pointPyramidEquiv_apex {n : ℕ} (k : KeyData (n + 1)) :
    pointPyramidEquiv n (rationalPoint k.apex) =
      (keyPyramidApex k, keyPyramidHeight k) := rfl

/-- The degenerate last base interval is exactly the height-zero equation. -/
theorem mem_keyBase_iff_pyramidBase {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (x : Point (n + 1)) :
    x ∈ keyBase k ↔ pointPyramidEquiv n x ∈ pyramidBase (keyPyramidLo k) (keyPyramidHi k) := by
  constructor
  · intro hx
    have hn := hx (Fin.last n)
    simp only [hc, hr, Rat.cast_zero, sub_zero] at hn
    refine ⟨abs_eq_zero.mp (le_antisymm hn (abs_nonneg _)), ?_⟩
    intro i
    have hi := abs_le.mp (hx i.castSucc)
    change (k.centre i.castSucc : ℝ) - (k.radius i.castSucc : ℝ) ≤ x i.castSucc ∧
      x i.castSucc ≤ (k.centre i.castSucc : ℝ) + (k.radius i.castSucc : ℝ)
    constructor <;> linarith [hi.1, hi.2]
  · rintro ⟨hn, ht⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change |x (Fin.last n) - (k.centre (Fin.last n) : ℝ)| ≤
        (k.radius (Fin.last n) : ℝ)
      change x (Fin.last n) = 0 at hn
      simp [hc, hr, hn]
    · have hj := ht j
      change (k.centre j.castSucc : ℝ) - (k.radius j.castSucc : ℝ) ≤ x j.castSucc ∧
        x j.castSucc ≤ (k.centre j.castSucc : ℝ) + (k.radius j.castSucc : ℝ) at hj
      apply abs_le.mpr
      constructor <;> linarith [hj.1, hj.2]

/-- Exact base image under the last-coordinate splitting equivalence. -/
theorem pointPyramidEquiv_image_keyBase {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0) :
    pointPyramidEquiv n '' keyBase k = pyramidBase (keyPyramidLo k) (keyPyramidHi k) := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_keyBase_iff_pyramidBase k hc hr x).mp hx
  · intro hp
    obtain ⟨x, rfl⟩ := (pointPyramidEquiv n).surjective p
    exact ⟨x, (mem_keyBase_iff_pyramidBase k hc hr x).mpr hp, rfl⟩

/-- The actual Euclidean convex hull is precisely the coordinate pyramid. -/
theorem pointPyramidEquiv_image_keySolid {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0) :
    pointPyramidEquiv n '' keySolid k =
      pyramidSolid (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) (keyPyramidHeight k) := by
  unfold keySolid
  rw [show (pointPyramidEquiv n : Point (n + 1) → PyramidPoint n) =
    (pointPyramidEquiv n).toLinearMap from rfl]
  rw [LinearMap.image_convexHull]
  change convexHull ℝ (pointPyramidEquiv n '' insert (rationalPoint k.apex) (keyBase k)) = _
  rw [Set.image_insert_eq, pointPyramidEquiv_apex, pointPyramidEquiv_image_keyBase k hc hr]
  rfl

/-- Direct H-representation of an actual key with its base in the last-coordinate-zero plane. -/
theorem mem_keySolid_iff_pyramidHalfspaces {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (x : Point (n + 1)) :
    x ∈ keySolid k ↔ pointPyramidEquiv n x ∈
      pyramidHalfspaces (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) (keyPyramidHeight k) := by
  rw [← pyramidSolid_eq_halfspaces _ _ _ hh, ← pointPyramidEquiv_image_keySolid k hc hr]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    have heq := (pointPyramidEquiv n).injective hxy
    simpa [heq] using hy

/-- Outward linear forms on the actual Euclidean ambient space. -/
noncomputable def keyPyramidHalfspaceNormal {n : ℕ} (k : KeyData (n + 1))
    (j : PyramidHalfspaceIndex n) : Point (n + 1) →ₗ[ℝ] ℝ :=
  (pyramidHalfspaceNormal (keyPyramidLo k) (keyPyramidHi k)
    (keyPyramidApex k) (keyPyramidHeight k) j).comp (pointPyramidEquiv n).toLinearMap

noncomputable def keyPyramidHalfspaceBound {n : ℕ} (k : KeyData (n + 1))
    (j : PyramidHalfspaceIndex n) : ℝ :=
  pyramidHalfspaceBound (keyPyramidLo k) (keyPyramidHi k) (keyPyramidHeight k) j

/-- The complete coordinate inventory, with outward-normal signs made explicit. -/
theorem keyPyramidHalfspaceNormal_apply {n : ℕ} (k : KeyData (n + 1))
    (j : PyramidHalfspaceIndex n) (x : Point (n + 1)) :
    keyPyramidHalfspaceNormal k j x = match j with
      | .inl false => -x (Fin.last n)
      | .inl true => x (Fin.last n)
      | .inr (i, false) =>
          (keyPyramidApex k i - keyPyramidLo k i) * x (Fin.last n) -
            keyPyramidHeight k * x i.castSucc
      | .inr (i, true) =>
          keyPyramidHeight k * x i.castSucc +
            (keyPyramidHi k i - keyPyramidApex k i) * x (Fin.last n) := by
  rcases j with b | ⟨i, b⟩ <;> cases b <;> rfl

/-- Nonnegative slack means that the corresponding closed halfspace is satisfied. -/
noncomputable def keyPyramidHalfspaceSlack {n : ℕ} (k : KeyData (n + 1))
    (j : PyramidHalfspaceIndex n) (x : Point (n + 1)) : ℝ :=
  keyPyramidHalfspaceBound k j - keyPyramidHalfspaceNormal k j x

theorem continuous_keyPyramidHalfspaceSlack {n : ℕ} (k : KeyData (n + 1))
    (j : PyramidHalfspaceIndex n) : Continuous (keyPyramidHalfspaceSlack k j) :=
  continuous_const.sub (keyPyramidHalfspaceNormal k j).continuous_of_finiteDimensional

/-- The finite list of genuine Euclidean linear halfspaces equals `Model.keySolid`. -/
theorem mem_keySolid_iff_forall_halfspace {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (x : Point (n + 1)) :
    x ∈ keySolid k ↔ ∀ j, keyPyramidHalfspaceNormal k j x ≤ keyPyramidHalfspaceBound k j := by
  rw [mem_keySolid_iff_pyramidHalfspaces k hc hr hh,
    mem_pyramidHalfspaces_iff_forall_halfspace]
  rfl

theorem mem_keySolid_iff_nonneg_slacks {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (x : Point (n + 1)) :
    x ∈ keySolid k ↔ ∀ j, 0 ≤ keyPyramidHalfspaceSlack k j x := by
  simp only [keyPyramidHalfspaceSlack, sub_nonneg]
  exact mem_keySolid_iff_forall_halfspace k hc hr hh x

/-- Set-level finite H-representation of the actual Euclidean convex hull. -/
theorem keySolid_eq_iInter_halfspaces {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) :
    keySolid k = ⋂ j : PyramidHalfspaceIndex n,
      {x | keyPyramidHalfspaceNormal k j x ≤ keyPyramidHalfspaceBound k j} := by
  ext x
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  exact mem_keySolid_iff_forall_halfspace k hc hr hh x

namespace Canonical

noncomputable def referenceHalfspaceSlack5 (j : PyramidHalfspaceIndex 4) (x : Point 5) : ℝ :=
  keyPyramidHalfspaceSlack ((referenceBox5 true).toKeyData 19200) j x

noncomputable def referenceHalfspaceSlack7 (j : PyramidHalfspaceIndex 6) (x : Point 7) : ℝ :=
  keyPyramidHalfspaceSlack ((referenceBox7 true).toKeyData 188160) j x

theorem continuous_referenceHalfspaceSlack5 (j : PyramidHalfspaceIndex 4) :
    Continuous (referenceHalfspaceSlack5 j) := continuous_keyPyramidHalfspaceSlack _ j

theorem continuous_referenceHalfspaceSlack7 (j : PyramidHalfspaceIndex 6) :
    Continuous (referenceHalfspaceSlack7 j) := continuous_keyPyramidHalfspaceSlack _ j

/-- Ten exact inequalities for the literal five-dimensional reference pyramid. -/
theorem mem_referenceSolid5_iff (x : Point 5) :
    x ∈ referenceSolid5 ↔ ∀ j, 0 ≤ referenceHalfspaceSlack5 j x := by
  apply mem_keySolid_iff_nonneg_slacks _ (referenceBox5_normal_centre true)
    (referenceBox5_normal_radius true)
  change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
  rw [referenceBox5_height]
  norm_num

/-- Fourteen exact inequalities for the literal seven-dimensional reference pyramid. -/
theorem mem_referenceSolid7_iff (x : Point 7) :
    x ∈ referenceSolid7 ↔ ∀ j, 0 ≤ referenceHalfspaceSlack7 j x := by
  apply mem_keySolid_iff_nonneg_slacks _ (referenceBox7_normal_centre true)
    (referenceBox7_normal_radius true)
  change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
  rw [referenceBox7_height]
  norm_num

/-- Pull back reference inequalities through a physical registered pose. -/
noncomputable def posedHalfspaceSlack5 (p : Contact.Pose 5) (j : PyramidHalfspaceIndex 4)
    (x : Point 5) : ℝ := referenceHalfspaceSlack5 j (p.euclidean.symm x)

noncomputable def posedHalfspaceSlack7 (p : Contact.Pose 7) (j : PyramidHalfspaceIndex 6)
    (x : Point 7) : ℝ := referenceHalfspaceSlack7 j (p.euclidean.symm x)

theorem continuous_posedHalfspaceSlack5 (p : Contact.Pose 5) (j : PyramidHalfspaceIndex 4) :
    Continuous (posedHalfspaceSlack5 p j) :=
  (continuous_referenceHalfspaceSlack5 j).comp p.euclidean.symm.continuous

theorem continuous_posedHalfspaceSlack7 (p : Contact.Pose 7) (j : PyramidHalfspaceIndex 6) :
    Continuous (posedHalfspaceSlack7 p j) :=
  (continuous_referenceHalfspaceSlack7 j).comp p.euclidean.symm.continuous

/-- Any checked canonical-pose equality supplies all inequalities for that actual key. -/
theorem mem_keySolid5_iff_posed_halfspaces {k : KeyData 5} (p : Contact.Pose 5)
    (hk : keySolid k = p.euclidean '' referenceSolid5) (x : Point 5) :
    x ∈ keySolid k ↔ ∀ j, 0 ≤ posedHalfspaceSlack5 p j x := by
  rw [hk]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ∀ j, 0 ≤ referenceHalfspaceSlack5 j (p.euclidean.symm (p.euclidean y))
    rw [p.euclidean.symm_apply_apply]
    exact (mem_referenceSolid5_iff y).mp hy
  · intro hx
    exact ⟨p.euclidean.symm x, (mem_referenceSolid5_iff _).mpr hx,
      p.euclidean.apply_symm_apply x⟩

theorem mem_keySolid7_iff_posed_halfspaces {k : KeyData 7} (p : Contact.Pose 7)
    (hk : keySolid k = p.euclidean '' referenceSolid7) (x : Point 7) :
    x ∈ keySolid k ↔ ∀ j, 0 ≤ posedHalfspaceSlack7 p j x := by
  rw [hk]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ∀ j, 0 ≤ referenceHalfspaceSlack7 j (p.euclidean.symm (p.euclidean y))
    rw [p.euclidean.symm_apply_apply]
    exact (mem_referenceSolid7_iff y).mp hy
  · intro hx
    exact ⟨p.euclidean.symm x, (mem_referenceSolid7_iff _).mpr hx,
      p.euclidean.apply_symm_apply x⟩

end Canonical

#print axioms pointPyramidEquiv_image_keyBase
#print axioms pointPyramidEquiv_image_keySolid
#print axioms mem_keySolid_iff_nonneg_slacks
#print axioms Canonical.mem_referenceSolid5_iff
#print axioms Canonical.mem_referenceSolid7_iff
#print axioms Canonical.mem_keySolid5_iff_posed_halfspaces
#print axioms Canonical.mem_keySolid7_iff_posed_halfspaces

end SparseMonotiles
