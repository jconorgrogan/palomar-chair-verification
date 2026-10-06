module

public import SparseMonotiles.KeyCompanionFeatureMatchingClosedCover
public import SparseMonotiles.KeyCompanionFeatureMatchingApexPatches

@[expose] public section

/-! # One closed disjoint key support contains the entire connected side
Carrier-plane restrictions are removed on the full relatively open side patch;
closedness and connectedness then identify the support by the common apex.
-/
namespace SparseMonotiles
open Set

theorem closed_key_side_subset_anchored_support {n : ℕ} {ι κ : Type*}
    [Finite ι] [Countable κ] (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (i : Fin n) (b : Bool) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    (K : ι → Set (Point (n+1))) (hclosed : ∀ a, IsClosed (K a))
    (hdisjoint : ∀ a c, a ≠ c → Disjoint (K a) (K c))
    (a₀ : ι) (hapex : W (rationalPoint k.apex) ∈ K a₀)
    (H : κ → AffineSubspace ℝ (Point (n+1)))
    (hproper : ∀ c, ¬ posedKeySidePlane k i b W ≤ H c)
    (hcover : ∀ x ∈ W '' keySideClosedFace k i b,
      x ∈ ⋃ a, K a ∨ ∃ c, x ∈ H c) : W '' keySideClosedFace k i b ⊆ K a₀ := by
  let P := posedKeySidePlane k i b W
  let O : Set P := Subtype.val ⁻¹' posedKeySidePatch k i b W
  have hO : IsOpen O := isOpen_posedKeySidePatch_in_plane k hd i b W
  have hK : IsClosed (⋃ a, K a) := isClosed_iUnion_of_finite hclosed
  have hcov : ∀ x ∈ O, (x : Point (n+1)) ∈ ⋃ a, K a ∨ ∃ c, (x : Point (n+1)) ∈ H c := by
    intro x hx
    apply hcover x
    obtain ⟨y,hy,hey⟩ := hx
    exact ⟨y,keySideStrictPatch_subset_face k hc hr hh i b hy,hey⟩
  have hsub := affine_patch_closed_cover_remove_planes P hO (⋃ a, K a) hK H hproper hcov
  rw [posedKeySidePatch_intrinsic_closure k hc hr hh hd i b W] at hsub
  have hconv : Convex ℝ (W '' keySideClosedFace k i b) := by
    rw [← closure_posedKeySidePatch k hc hr hh hd i b W]
    exact (convex_posedKeySidePatch k i b W).closure
  exact preconnected_subset_closed_member_of_finite_disjoint_cover hconv.isPreconnected
    K hclosed hdisjoint hsub a₀ (posed_key_apex_mem_closed_side k i b W) hapex

#print axioms closed_key_side_subset_anchored_support
end SparseMonotiles
