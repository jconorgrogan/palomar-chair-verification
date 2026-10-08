module

public import SparseMonotiles.KeyCompanionFeatureMatchingPlanes
public import SparseMonotiles.KeySideFacePatchTransport

@[expose] public section

/-! # Every genuine key side plane survives in a local apex boundary cover
The nonempty relative patches and the distinctness of all side planes are
proved from the actual key geometry, including arbitrarily close to the apex.
-/
namespace SparseMonotiles
open Set

theorem closure_posedKeySidePatch {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    closure (posedKeySidePatch k i b W)=W '' keySideClosedFace k i b := by
  change closure (W.toHomeomorph '' keySideStrictPatch k i b)=_
  rw [← W.toHomeomorph.image_closure,closure_keySideStrictPatch k hc hr hh hd i b]
  rfl

theorem posedKeySidePlanes_injective {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    Function.Injective (fun a : Fin n × Bool => posedKeySidePlane k a.1 a.2 W) := by
  intro a b hab
  change posedKeySidePlane k a.1 a.2 W=posedKeySidePlane k b.1 b.2 W at hab
  by_contra hne
  have hx := keySideStrictPoint_mem k hh hd a.1 a.2
  have hxa : W (keySideStrictPoint k a.1 a.2) ∈ posedKeySidePlane k a.1 a.2 W :=
    posedKeySidePatch_subset_plane k hd a.1 a.2 W ⟨_,hx,rfl⟩
  rw [hab] at hxa
  have hxb := (mem_keySideAffinePlane_iff k hd b.1 b.2 _).mp
    ((mem_posedKeySidePlane_iff k b.1 b.2 W _).mp hxa)
  rw [W.symm_apply_apply] at hxb
  have hpos := hx.2 (.inr (b.1,b.2)) (fun h => hne (Prod.ext
    (congrArg Prod.fst (Sum.inr.inj h)).symm (congrArg Prod.snd (Sum.inr.inj h)).symm))
  exact (ne_of_gt hpos) hxb

theorem posed_key_apex_mem_closed_side {n : ℕ} (k : KeyData (n+1))
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) :
    W (rationalPoint k.apex) ∈ W '' keySideClosedFace k i b := by
  refine ⟨_,⟨?_,key_apex_side_slack_zero k i b⟩,rfl⟩
  exact subset_convexHull ℝ _ (Set.mem_insert _ _)

theorem key_side_patch_near_apex_nonempty {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    {U : Set (Point (n+1))} (hU : IsOpen U) (hp : W (rationalPoint k.apex) ∈ U) :
    (Subtype.val ⁻¹' (posedKeySidePatch k i b W ∩ U) : Set (posedKeySidePlane k i b W)).Nonempty := by
  have hcl : W (rationalPoint k.apex) ∈ closure (posedKeySidePatch k i b W) := by
    rw [closure_posedKeySidePatch k hc hr hh hd]
    exact posed_key_apex_mem_closed_side k i b W
  obtain ⟨x,hxU,hxP⟩ := mem_closure_iff.mp hcl U hU hp
  exact ⟨⟨x,posedKeySidePatch_subset_plane k hd i b W hxP⟩,hxP,hxU⟩

/-- A local proper-plane cover of all the actual closed key sides must contain
at least all `2n` distinct supporting planes. -/
theorem key_apex_local_boundary_plane_card_bound {n : ℕ} {κ : Type*} [Fintype κ]
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (S : Set (Point (n+1))) (hside : ∀ i b, W '' keySideClosedFace k i b ⊆ S)
    {U : Set (Point (n+1))} (hU : IsOpen U) (hp : W (rationalPoint k.apex) ∈ U)
    (H : κ → AffineSubspace ℝ (Point (n+1))) (hH : ∀ a, H a ≠ ⊤)
    (hcover : ∀ x ∈ U, x ∈ S → ∃ a, x ∈ H a) : 2*n ≤ Fintype.card κ := by
  let P : Fin n × Bool → AffineSubspace ℝ (Point (n+1)) := fun a => posedKeySidePlane k a.1 a.2 W
  let O : ∀ a, Set (P a) := fun a => Subtype.val ⁻¹' (posedKeySidePatch k a.1 a.2 W ∩ U)
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (isOpen_posedKeySidePatch_in_plane k hd a.1 a.2 W).inter (hU.preimage continuous_subtype_val)
  have hne : ∀ a, (O a).Nonempty := fun a => key_side_patch_near_apex_nonempty k hc hr hh hd a.1 a.2 W hU hp
  have hdim : ∀ a, Module.finrank ℝ (P a).direction+1=Module.finrank ℝ (Point (n+1)) := by
    intro a
    simpa only [finrank_euclideanSpace_fin] using posedKeySidePlane_finrank k a.1 a.2 W
  have hcov : ∀ a x, x ∈ O a → ∃ b, (x : Point (n+1)) ∈ H b := by
    intro a x hx
    apply hcover x hx.2
    apply hside a.1 a.2
    rcases hx.1 with ⟨y,hy,hey⟩
    exact ⟨y,keySideStrictPatch_subset_face k hc hr hh a.1 a.2 hy,hey⟩
  have hcard := finite_hyperplane_patch_cover_card_le P (posedKeySidePlanes_injective k hh hd W)
    O hO hne hdim H hH hcov
  simpa only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Nat.mul_comm] using hcard

/-- In an equally sized family, local coverage identifies and exhausts all
side planes, rather than only giving a cardinality bound. -/
theorem key_apex_local_boundary_side_plane_equiv {n : ℕ} (k l : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (W V : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (S : Set (Point (n+1))) (hside : ∀ i b, W '' keySideClosedFace k i b ⊆ S)
    {U : Set (Point (n+1))} (hU : IsOpen U) (hp : W (rationalPoint k.apex) ∈ U)
    (hcover : ∀ x ∈ U, x ∈ S → ∃ a : Fin n × Bool, x ∈ posedKeySidePlane l a.1 a.2 V) :
    ∃ σ : (Fin n × Bool) ≃ (Fin n × Bool), ∀ a,
      posedKeySidePlane k a.1 a.2 W=posedKeySidePlane l (σ a).1 (σ a).2 V := by
  let P : Fin n × Bool → AffineSubspace ℝ (Point (n+1)) := fun a => posedKeySidePlane k a.1 a.2 W
  let O : ∀ a, Set (P a) := fun a => Subtype.val ⁻¹' (posedKeySidePatch k a.1 a.2 W ∩ U)
  let H : Fin n × Bool → AffineSubspace ℝ (Point (n+1)) := fun a => posedKeySidePlane l a.1 a.2 V
  have hO : ∀ a, IsOpen (O a) := fun a =>
    (isOpen_posedKeySidePatch_in_plane k hd a.1 a.2 W).inter (hU.preimage continuous_subtype_val)
  have hne : ∀ a, (O a).Nonempty := fun a => key_side_patch_near_apex_nonempty k hc hr hh hd a.1 a.2 W hU hp
  have hdim : ∀ a, Module.finrank ℝ (P a).direction+1=Module.finrank ℝ (Point (n+1)) := by
    intro a
    simpa only [finrank_euclideanSpace_fin] using posedKeySidePlane_finrank k a.1 a.2 W
  have hH : ∀ a, H a ≠ ⊤ := by
    intro a heq
    have h := posedKeySidePlane_finrank l a.1 a.2 V
    change Module.finrank ℝ (H a).direction+1=n+1 at h
    rw [heq,AffineSubspace.direction_top,finrank_top,finrank_euclideanSpace_fin] at h
    omega
  have hcov : ∀ a x, x ∈ O a → ∃ b, (x : Point (n+1)) ∈ H b := by
    intro a x hx
    apply hcover x hx.2
    apply hside a.1 a.2
    rcases hx.1 with ⟨y,hy,hey⟩
    exact ⟨y,keySideStrictPatch_subset_face k hc hr hh a.1 a.2 hy,hey⟩
  obtain ⟨σ,hσ,heq⟩ := finite_hyperplane_patch_cover_injection P
    (posedKeySidePlanes_injective k hh hd W) O hO hne hdim H hH hcov
  exact ⟨Equiv.ofBijective σ ⟨hσ,Finite.surjective_of_injective hσ⟩,heq⟩

#print axioms key_apex_local_boundary_plane_card_bound
#print axioms key_apex_local_boundary_side_plane_equiv
end SparseMonotiles
