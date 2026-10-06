module

public import SparseMonotiles.KeyRidgeModelInventory
public import SparseMonotiles.Tile5MergedModels
public import SparseMonotiles.Tile7MergedModels
public import SparseMonotiles.BoundaryTransport

@[expose] public section

/-! # Exact physical key ridge models in fixed generic frames
The arbitrary physical frame and its global plane family are fixed before
choosing the ridge point. Every actual isolated-key germ is now reduced to
constant material, a genuine halfspace, or the classified two-plane wedge.
-/
namespace SparseMonotiles
open Set Canonical

theorem T5_generic_isolated_key_inventory
    (g : Point 5 ≃ᵢ Point 5) {k : KeyData 5} (hk : k ∈ keys5)
    (q : Contact.Pose 5) (hq : keySolid k = q.euclidean '' referenceSolid5)
    (R : AffineSubspace ℝ (Point 5))
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    {p : Point 5} (hpR : p ∈ R)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0)
    {T : Set (Point 5)}
    (hT : LocalSetEq (g.symm p) T
      (closure (mergedKeyRegion (posedHalfspaceSlack5 q) (.inl false) k.bump))) :
    ∃ M, IsKeyRidgeModel (posedHalfspaceSlack5 q) k.bump M ∧ LocalSetEq (g.symm p) T M := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  apply localSetEq_keyRidgeModel_inventory ((referenceBox5 true).toKeyData 19200)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
      exact_mod_cast referenceBox5_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox5_base_interval_pos true j)
    q (keys5.get i).bump ?_ hT
  intro hp
  have hpk : g.symm p ∈ keySolid (keys5.get i) := by
    rw [hq]
    exact ⟨q.euclidean.symm (g.symm p), hp, q.euclidean.apply_symm_apply _⟩
  exact T5_generic_key_ridge_active_summary g i q hq R hcodim hpR hpk hactive

/-- Complete arbitrary-copy local inventory, with its carrier branch retained
for the independent orthogonal-carrier classification. -/
theorem T5_generic_physical_key_model_inventory
    (g : Point 5 ≃ᵢ Point 5) (R : AffineSubspace ℝ (Point 5))
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    {p : Point 5} (hpR : p ∈ R)
    (hactive : ∀ j, T5WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T5WorldAffineFields g j) 0) :
    LocalSetEq p (g '' T5) (g '' carrier 5) ∨
      ∃ k ∈ keys5, ∃ q : Contact.Pose 5, ∃ M,
        keySolid k = q.euclidean '' referenceSolid5 ∧
        IsKeyRidgeModel (posedHalfspaceSlack5 q) k.bump M ∧
        LocalSetEq p (g '' T5) (g '' M) := by
  rcases T5_local_merged_key_inventory (g.symm p) with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (by simpa only [g.apply_symm_apply] using hcarrier.image_isometry g)
  · obtain ⟨M,hM,heq⟩ := T5_generic_isolated_key_inventory g hk q hq R hcodim hpR hactive hlocal
    exact Or.inr ⟨k,hk,q,M,hq,hM,by simpa only [g.apply_symm_apply] using heq.image_isometry g⟩

#print axioms T5_generic_isolated_key_inventory
#print axioms T5_generic_physical_key_model_inventory

theorem T7_generic_isolated_key_inventory
    (g : Point 7 ≃ᵢ Point 7) {k : KeyData 7} (hk : k ∈ keys7)
    (q : Contact.Pose 7) (hq : keySolid k = q.euclidean '' referenceSolid7)
    (R : AffineSubspace ℝ (Point 7))
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    {p : Point 7} (hpR : p ∈ R)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0)
    {T : Set (Point 7)}
    (hT : LocalSetEq (g.symm p) T
      (closure (mergedKeyRegion (posedHalfspaceSlack7 q) (.inl false) k.bump))) :
    ∃ M, IsKeyRidgeModel (posedHalfspaceSlack7 q) k.bump M ∧ LocalSetEq (g.symm p) T M := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
  apply localSetEq_keyRidgeModel_inventory ((referenceBox7 true).toKeyData 188160)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by
      change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
      exact_mod_cast referenceBox7_height_pos true)
    (fun j => by
      unfold keyPyramidLo keyPyramidHi
      exact_mod_cast referenceBox7_base_interval_pos true j)
    q (keys7.get i).bump ?_ hT
  intro hp
  have hpk : g.symm p ∈ keySolid (keys7.get i) := by
    rw [hq]
    exact ⟨q.euclidean.symm (g.symm p), hp, q.euclidean.apply_symm_apply _⟩
  exact T7_generic_key_ridge_active_summary g i q hq R hcodim hpR hpk hactive

/-- Complete arbitrary-copy local inventory, with its carrier branch retained
for the independent orthogonal-carrier classification. -/
theorem T7_generic_physical_key_model_inventory
    (g : Point 7 ≃ᵢ Point 7) (R : AffineSubspace ℝ (Point 7))
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    {p : Point 7} (hpR : p ∈ R)
    (hactive : ∀ j, T7WorldAffineFields g j p = 0 →
      R ≤ affineFormPlane (T7WorldAffineFields g j) 0) :
    LocalSetEq p (g '' T7) (g '' carrier 7) ∨
      ∃ k ∈ keys7, ∃ q : Contact.Pose 7, ∃ M,
        keySolid k = q.euclidean '' referenceSolid7 ∧
        IsKeyRidgeModel (posedHalfspaceSlack7 q) k.bump M ∧
        LocalSetEq p (g '' T7) (g '' M) := by
  rcases T7_local_merged_key_inventory (g.symm p) with hcarrier | ⟨k,hk,q,hq,hlocal⟩
  · exact Or.inl (by simpa only [g.apply_symm_apply] using hcarrier.image_isometry g)
  · obtain ⟨M,hM,heq⟩ := T7_generic_isolated_key_inventory g hk q hq R hcodim hpR hactive hlocal
    exact Or.inr ⟨k,hk,q,M,hq,hM,by simpa only [g.apply_symm_apply] using heq.image_isometry g⟩

#print axioms T7_generic_isolated_key_inventory
#print axioms T7_generic_physical_key_model_inventory

end SparseMonotiles
