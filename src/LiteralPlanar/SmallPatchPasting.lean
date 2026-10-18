module

public import SpectreGeometry.DeformationHomeomorphism
public import SpectreGeometry.DeformationHomeomorphismGluing

@[expose] public section


/-! Quantitative pasting on genuine closed covers. This reusable theorem has
explicit contact compatibility and small-residual premises; no target tiling
or global inverse is hidden in a record. The curved reverse application must
derive compatibility from its actual polynomial arc geometry. -/
namespace LiteralPlanar
noncomputable section
open scoped NNReal
open SpectreGeometry

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_homeomorph_of_compatible_small_patches
    (C : I → Set E) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i) (G : I → E → E)
    (hcompatible : ∀ i j x, x ∈ C i → x ∈ C j → G i x = G j x)
    (q : ℝ≥0) (hq : q < 1)
    (hsmall : ∀ i, LipschitzOnWith q (fun x => G i x-x) (C i)) :
    ∃ H : E ≃ₜ E, ∀ i x, x ∈ C i → H x = G i x := by
  let chooseTile (x : E) := Classical.choose (hcover x)
  have hchoose (x : E) : x ∈ C (chooseTile x) := Classical.choose_spec (hcover x)
  let r (x : E) := G (chooseTile x) x-x
  have hr (i : I) (x : E) (hx : x ∈ C i) : r x = G i x-x := by
    exact congrArg (fun y => y-x) (hcompatible (chooseTile x) i x (hchoose x) hx)
  have hl : LipschitzWith q r := by
    apply Deformation.lipschitz_of_locallyFinite_closed_cover C hlocal hclosed hcover
    intro i
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hr i x hx,hr i y hy]
    exact (hsmall i).dist_le_mul x hx y hy
  let H := Deformation.identitySubHomeomorph (fun x => -r x) q hq hl.neg
  refine ⟨H,?_⟩
  intro i x hx
  change x-(-r x) = G i x
  rw [hr i x hx]
  abel

theorem tiling_transfer_of_compatible_small_patches
    (C D : I → Set E) (hlocal : LocallyFinite C) (hclosed : ∀ i, IsClosed (C i))
    (hcover : ∀ x, ∃ i, x ∈ C i)
    (hpack : Pairwise fun i j => Disjoint (interior (C i)) (interior (C j)))
    (G : I → E → E)
    (hcompatible : ∀ i j x, x ∈ C i → x ∈ C j → G i x = G j x)
    (q : ℝ≥0) (hq : q < 1)
    (hsmall : ∀ i, LipschitzOnWith q (fun x => G i x-x) (C i))
    (himage : ∀ i, G i '' C i = D i) :
    (∀ x, ∃ i, x ∈ D i) ∧
      Pairwise (fun i j => Disjoint (interior (D i)) (interior (D j))) := by
  obtain ⟨H,hH⟩ := exists_homeomorph_of_compatible_small_patches C hlocal hclosed hcover
    G hcompatible q hq hsmall
  apply Deformation.tiling_transport H C D hcover hpack
  intro i
  rw [←himage i]
  apply Set.image_congr
  exact hH i

end
end LiteralPlanar
