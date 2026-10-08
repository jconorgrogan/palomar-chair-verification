module

public import SparseMonotiles.GenericKeyRidgeActive

@[expose] public section

/-!
# Generic incidence bounds in arbitrary physical key frames

Fixed global fields, selected before the generic point, control every later
canonical local key presentation. This proves apex exclusion and the actual
at-most-two-active-planes result for the exact five- and seven-dimensional keys.
-/
namespace SparseMonotiles
open Set Canonical

/-- The generic key result transported by any affine change of physical frame. -/
theorem key_ridge_summary_affine {n : ℕ} (hn : 3 ≤ n)
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    (e : Point (n+1) ≃ᵃ[ℝ] Point (n+1))
    (R : AffineSubspace ℝ (Point (n+1)))
    (hcodim : Module.finrank ℝ R.direction + 2 = n+1)
    {p : Point (n+1)} (hpR : p ∈ R) (hpk : e p ∈ keySolid k)
    (hactive : ∀ j, keyPyramidHalfspaceSlack k j (e p) = 0 →
      ∀ x ∈ R, keyPyramidHalfspaceSlack k j (e x) = 0) :
    e p ≠ rationalPoint k.apex ∧
    Nat.card {j : PyramidHalfspaceIndex n // keyPyramidHalfspaceSlack k j (e p) = 0} ≤ 2 := by
  let S := R.map e.toAffineMap
  have hSc : Module.finrank ℝ S.direction + 2 = n+1 := by
    dsimp [S]
    rw [affineEquiv_map_ridge_finrank e R]
    exact hcodim
  have hep : e p ∈ S := AffineSubspace.mem_map_of_mem e.toAffineMap hpR
  have hSa : ∀ j, keyPyramidHalfspaceSlack k j (e p) = 0 →
      ∀ x ∈ S, keyPyramidHalfspaceSlack k j x = 0 := by
    intro j hj x hx
    rcases hx with ⟨y,hy,rfl⟩
    exact hactive j hj y hy
  have hne := key_ridge_point_ne_apex hn k hh hd S hSc hep hSa
  exact ⟨hne, key_ridge_active_halfspaces_card_le_two k hc hr hh hw hd S hSc hep hpk hne hSa⟩

/-- Inverse world frame followed by the inverse canonical key frame. -/
noncomputable def inverseKeyAffineFrame {d : ℕ} (g : Point d ≃ᵢ Point d)
    (q : Contact.Pose d) : Point d ≃ᵃ[ℝ] Point d :=
  g.symm.toRealAffineIsometryEquiv.toAffineEquiv.trans q.euclidean.symm.toAffineEquiv

@[simp] theorem inverseKeyAffineFrame_apply {d : ℕ} (g : Point d ≃ᵢ Point d)
    (q : Contact.Pose d) (x : Point d) :
    inverseKeyAffineFrame g q x = q.euclidean.symm (g.symm x) := rfl

theorem T5_generic_key_ridge_active_summary
    (g : Point 5 ≃ᵢ Point 5) (i : Fin keys5.length) (q : Contact.Pose 5)
    (hq : keySolid (keys5.get i) = q.euclidean '' referenceSolid5)
    (R : AffineSubspace ℝ (Point 5))
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    {p : Point 5} (hpR : p ∈ R) (hpk : g.symm p ∈ keySolid (keys5.get i))
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0) :
    q.euclidean.symm (g.symm p) ≠ rationalPoint ((referenceBox5 true).toKeyData 19200).apex ∧
    Nat.card {j : PyramidHalfspaceIndex 4 // posedHalfspaceSlack5 q j (g.symm p) = 0} ≤ 2 := by
  have hmem : q.euclidean.symm (g.symm p) ∈ referenceSolid5 := by
    rw [hq] at hpk
    rcases hpk with ⟨x,hx,hxp⟩
    rw [← hxp, q.euclidean.symm_apply_apply]
    exact hx
  apply key_ridge_summary_affine (by decide) ((referenceBox5 true).toKeyData 19200)
    (by simp [Fin.last])
    (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
      exact_mod_cast referenceBox5_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox5_base_interval_pos true j)
    referenceSideDistance5_pos (inverseKeyAffineFrame g q) R hcodim hpR hmem
  intro j hj x hx
  have hglobal : T5WorldAffineFields g (.inr (i,j)) p = 0 := by
    rw [T5WorldAffineFields_eq_local_key g i q hq j p]
    exact hj
  have hh := (mem_affineFormPlane _ _ _).mp (hactive (.inr (i,j)) hglobal hx)
  rw [T5WorldAffineFields_eq_local_key g i q hq j x] at hh
  exact hh

theorem T7_generic_key_ridge_active_summary
    (g : Point 7 ≃ᵢ Point 7) (i : Fin keys7.length) (q : Contact.Pose 7)
    (hq : keySolid (keys7.get i) = q.euclidean '' referenceSolid7)
    (R : AffineSubspace ℝ (Point 7))
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    {p : Point 7} (hpR : p ∈ R) (hpk : g.symm p ∈ keySolid (keys7.get i))
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0) :
    q.euclidean.symm (g.symm p) ≠ rationalPoint ((referenceBox7 true).toKeyData 188160).apex ∧
    Nat.card {j : PyramidHalfspaceIndex 6 // posedHalfspaceSlack7 q j (g.symm p) = 0} ≤ 2 := by
  have hmem : q.euclidean.symm (g.symm p) ∈ referenceSolid7 := by
    rw [hq] at hpk
    rcases hpk with ⟨x,hx,hxp⟩
    rw [← hxp, q.euclidean.symm_apply_apply]
    exact hx
  apply key_ridge_summary_affine (by decide) ((referenceBox7 true).toKeyData 188160)
    (by simp [Fin.last])
    (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
      exact_mod_cast referenceBox7_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox7_base_interval_pos true j)
    referenceSideDistance7_pos (inverseKeyAffineFrame g q) R hcodim hpR hmem
  intro j hj x hx
  have hglobal : T7WorldAffineFields g (.inr (i,j)) p = 0 := by
    rw [T7WorldAffineFields_eq_local_key g i q hq j p]
    exact hj
  have hh := (mem_affineFormPlane _ _ _).mp (hactive (.inr (i,j)) hglobal hx)
  rw [T7WorldAffineFields_eq_local_key g i q hq j x] at hh
  exact hh

#print axioms key_ridge_summary_affine
#print axioms T5_generic_key_ridge_active_summary
#print axioms T7_generic_key_ridge_active_summary
end SparseMonotiles
