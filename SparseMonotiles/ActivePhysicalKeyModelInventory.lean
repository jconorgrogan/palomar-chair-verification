module

public import SparseMonotiles.ActiveKeyRidgeModelInventory

@[expose] public section

/-! # Boundary inventory of arbitrary actual tile copies
The returned nonconstant local model retains every active equation; all active
local key fields vanish on the entire world ridge by the fixed-plane theorem.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_local_key_active_planes_contain_ridge
    (g : Point 5 ≃ᵢ Point 5) {k : KeyData 5} (hk : k ∈ keys5)
    (q : Contact.Pose 5) (hq : keySolid k = q.euclidean '' referenceSolid5)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5}
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0) :
    ∀ j, posedHalfspaceSlack5 q j (g.symm p) = 0 →
      ∀ x ∈ R, posedHalfspaceSlack5 q j (g.symm x) = 0 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  intro j hj x hx
  have hg : T5WorldAffineFields g (.inr (i,j)) p = 0 := by
    rw [T5WorldAffineFields_eq_local_key g i q hq j p]
    exact hj
  have hh := (mem_affineFormPlane _ _ _).mp (hactive (.inr (i,j)) hg hx)
  rwa [T5WorldAffineFields_eq_local_key g i q hq j x] at hh

theorem T5_generic_active_isolated_key_inventory
    (g : Point 5 ≃ᵢ Point 5) {k : KeyData 5} (hk : k ∈ keys5)
    (q : Contact.Pose 5) (hq : keySolid k = q.euclidean '' referenceSolid5)
    (R : AffineSubspace ℝ (Point 5))
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    {p : Point 5} (hpR : p ∈ R)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {T : Set (Point 5)} (hpT : g.symm p ∈ frontier T)
    (hT : LocalSetEq (g.symm p) T
      (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) k.bump))) :
    ∃ M, IsActiveKeyRidgeModel (posedHalfspaceSlack5 q) k.bump (g.symm p) M ∧
      LocalSetEq (g.symm p) T M := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  apply localSetEq_active_keyRidgeModel_inventory ((referenceBox5 true).toKeyData 19200)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
      exact_mod_cast referenceBox5_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox5_base_interval_pos true j)
    q (keys5.get i).bump hpT ?_ hT
  intro hp
  have hpk : g.symm p ∈ keySolid (keys5.get i) := by
    rw [hq]
    exact ⟨q.euclidean.symm (g.symm p), hp, q.euclidean.apply_symm_apply _⟩
  exact T5_generic_key_ridge_active_summary g i q hq R hcodim hpR hpk hactive

/-- The physical boundary model now carries its active equations and the
whole-ridge vanishing needed to restrict its normals to the normal space. -/
theorem T5_generic_active_physical_key_model_inventory
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    {p : Point 5} (hpR : p ∈ R)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    (hboundary : p ∈ frontier (g '' T5)) :
    LocalSetEq p (g '' T5) (g '' carrier 5) ∨
      ∃ k ∈ keys5, ∃ q : Contact.Pose 5, ∃ M,
        keySolid k = q.euclidean '' referenceSolid5 ∧
        (∀ j, posedHalfspaceSlack5 q j (g.symm p) = 0 →
          ∀ x ∈ R, posedHalfspaceSlack5 q j (g.symm x) = 0) ∧
        IsActiveKeyRidgeModel (posedHalfspaceSlack5 q) k.bump (g.symm p) M ∧
        LocalSetEq p (g '' T5) (g '' M) := by
  have hb : g.symm p ∈ frontier T5 := by
    have heq : g '' frontier T5 = frontier (g '' T5) := g.toHomeomorph.image_frontier T5
    rw [← heq] at hboundary
    rcases hboundary with ⟨x,hx,hxp⟩
    rw [← hxp, g.symm_apply_apply]
    exact hx
  rcases T5_local_merged_key_inventory (g.symm p) with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (by simpa only [g.apply_symm_apply] using hcarrier.image_isometry g)
  · obtain ⟨M,hM,heq⟩ := T5_generic_active_isolated_key_inventory g hk q hq R hcodim hpR
      hactive hb hlocal
    exact Or.inr ⟨k,hk,q,M,hq,T5_local_key_active_planes_contain_ridge g hk q hq R hactive,
      hM,by simpa only [g.apply_symm_apply] using heq.image_isometry g⟩

#print axioms T5_local_key_active_planes_contain_ridge
#print axioms T5_generic_active_physical_key_model_inventory

theorem T7_local_key_active_planes_contain_ridge
    (g : Point 7 ≃ᵢ Point 7) {k : KeyData 7} (hk : k ∈ keys7)
    (q : Contact.Pose 7) (hq : keySolid k = q.euclidean '' referenceSolid7)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7}
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0) :
    ∀ j, posedHalfspaceSlack7 q j (g.symm p) = 0 →
      ∀ x ∈ R, posedHalfspaceSlack7 q j (g.symm x) = 0 := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  intro j hj x hx
  have hg : T7WorldAffineFields g (.inr (i,j)) p = 0 := by
    rw [T7WorldAffineFields_eq_local_key g i q hq j p]
    exact hj
  have hh := (mem_affineFormPlane _ _ _).mp (hactive (.inr (i,j)) hg hx)
  rwa [T7WorldAffineFields_eq_local_key g i q hq j x] at hh

theorem T7_generic_active_isolated_key_inventory
    (g : Point 7 ≃ᵢ Point 7) {k : KeyData 7} (hk : k ∈ keys7)
    (q : Contact.Pose 7) (hq : keySolid k = q.euclidean '' referenceSolid7)
    (R : AffineSubspace ℝ (Point 7))
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    {p : Point 7} (hpR : p ∈ R)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {T : Set (Point 7)} (hpT : g.symm p ∈ frontier T)
    (hT : LocalSetEq (g.symm p) T
      (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) k.bump))) :
    ∃ M, IsActiveKeyRidgeModel (posedHalfspaceSlack7 q) k.bump (g.symm p) M ∧
      LocalSetEq (g.symm p) T M := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  apply localSetEq_active_keyRidgeModel_inventory ((referenceBox7 true).toKeyData 188160)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
      exact_mod_cast referenceBox7_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox7_base_interval_pos true j)
    q (keys7.get i).bump hpT ?_ hT
  intro hp
  have hpk : g.symm p ∈ keySolid (keys7.get i) := by
    rw [hq]
    exact ⟨q.euclidean.symm (g.symm p), hp, q.euclidean.apply_symm_apply _⟩
  exact T7_generic_key_ridge_active_summary g i q hq R hcodim hpR hpk hactive

/-- The physical boundary model now carries its active equations and the
whole-ridge vanishing needed to restrict its normals to the normal space. -/
theorem T7_generic_active_physical_key_model_inventory
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    {p : Point 7} (hpR : p ∈ R)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    (hboundary : p ∈ frontier (g '' T7)) :
    LocalSetEq p (g '' T7) (g '' carrier 7) ∨
      ∃ k ∈ keys7, ∃ q : Contact.Pose 7, ∃ M,
        keySolid k = q.euclidean '' referenceSolid7 ∧
        (∀ j, posedHalfspaceSlack7 q j (g.symm p) = 0 →
          ∀ x ∈ R, posedHalfspaceSlack7 q j (g.symm x) = 0) ∧
        IsActiveKeyRidgeModel (posedHalfspaceSlack7 q) k.bump (g.symm p) M ∧
        LocalSetEq p (g '' T7) (g '' M) := by
  have hb : g.symm p ∈ frontier T7 := by
    have heq : g '' frontier T7 = frontier (g '' T7) := g.toHomeomorph.image_frontier T7
    rw [← heq] at hboundary
    rcases hboundary with ⟨x,hx,hxp⟩
    rw [← hxp, g.symm_apply_apply]
    exact hx
  rcases T7_local_merged_key_inventory (g.symm p) with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (by simpa only [g.apply_symm_apply] using hcarrier.image_isometry g)
  · obtain ⟨M,hM,heq⟩ := T7_generic_active_isolated_key_inventory g hk q hq R hcodim hpR
      hactive hb hlocal
    exact Or.inr ⟨k,hk,q,M,hq,T7_local_key_active_planes_contain_ridge g hk q hq R hactive,
      hM,by simpa only [g.apply_symm_apply] using heq.image_isometry g⟩

#print axioms T7_local_key_active_planes_contain_ridge
#print axioms T7_generic_active_physical_key_model_inventory

end SparseMonotiles
