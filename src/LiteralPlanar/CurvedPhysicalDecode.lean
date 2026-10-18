module

public import LiteralPlanar.CurvedDecodeCompatibility
public import LiteralPlanar.CurvedInverseBounds
public import LiteralPlanar.SmallPatchPasting

@[expose] public section


/-! A whole-plane inverse decoder for every physical tiling by the literal
polynomial body. Coverage, packing, and compatibility are genuine conclusions
of the derived small-residual homeomorphism. Chirality normalization is separate. -/
namespace LiteralPlanar.Forward
noncomputable section
open SpectreGeometry Candidate FanBounds
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p) (root : I)
include p T root

theorem physical_curved_tiling_to_source_tiling {J : Type*} (q : J → EPlane ≃ᵢ EPlane)
    (hcover : ∀ x, ∃ j, x ∈ q j '' curvedBody)
    (hpack : Pairwise fun i j => Disjoint (interior (q i '' curvedBody))
      (interior (q j '' curvedBody))) :
    (∀ x, ∃ j, x ∈ q j '' euclideanBody) ∧
      Pairwise (fun i j => Disjoint (interior (q i '' euclideanBody))
        (interior (q j '' euclideanBody))) := by
  apply tiling_transfer_of_compatible_small_patches
    (fun j => q j '' curvedBody) (fun j => q j '' euclideanBody)
    (CompactPacking.locallyFinite curvedBody curvedBody_compact
      (curvedBody_interior_nonempty p T root) q hpack)
    (fun j => (curvedBody_compact.image (q j).continuous).isClosed)
    hcover hpack (fun j => placedInverse p T root (q j))
    (curved_inverse_contact_compatible p T root q hcover hpack)
    (1/4) (by norm_num)
    (fun j => (placedInverse_residual_lipschitz p T root (q j)).lipschitzOnWith)
    (fun j => placedInverse_image p T root (q j))

end
end LiteralPlanar.Forward
