module

public import LiteralPlanar.GlobalPasting

@[expose] public section


/-! Topology of the literal polynomial body. Compactness is unconditional.
The exhibited source tiling yields an ambient homeomorphism to the checked P
carrier, giving nonempty interior and regular closedness without assuming them.
An actual disk certificate remains a separate source-polygon obligation. -/
namespace LiteralPlanar
noncomputable section
open SpectreGeometry FanBounds Forward

namespace Candidate

theorem parameterSimplex_compact : IsCompact parameterSimplex := by
  have hc : IsClosed parameterSimplex :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  apply ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).prod
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))).of_isClosed_subset hc
  intro w hw
  exact ⟨⟨hw.1,by linarith [hw.2.1,hw.2.2]⟩,⟨hw.2.1,by linarith [hw.1,hw.2.2]⟩⟩

theorem fanPatch_continuous (e : Fin 14) : Continuous (fanPatch e) := by
  unfold fanPatch Quintic.fanHeight
  fun_prop

theorem body_compact : IsCompact body :=
  isCompact_iUnion fun e => parameterSimplex_compact.image (fanPatch_continuous e)

end Candidate

theorem curvedBody_compact : IsCompact curvedBody :=
  Candidate.body_compact.image euclideanCoordinates.continuous

namespace Forward
variable {I : Type*} (p : I → EPlane ≃ᵢ EPlane) (T : SourceTiling p)

def tileHomeomorph (i : I) : EPlane ≃ₜ EPlane :=
  (p i).toHomeomorph.trans ((curvedHomeomorph p T).trans (p i).symm.toHomeomorph)

theorem tileHomeomorph_on_body (i : I) (x : EPlane) (hx : x ∈ euclideanBody) :
    tileHomeomorph p T i x = tileMap x := by
  simp only [tileHomeomorph,Homeomorph.trans_apply,IsometryEquiv.coe_toHomeomorph]
  rw [curvedHomeomorph_on_tile p T i _ ⟨x,hx,rfl⟩]
  simp only [placedTileMap,IsometryEquiv.symm_apply_apply]

theorem tileHomeomorph_image_body (i : I) :
    tileHomeomorph p T i '' euclideanBody = curvedBody := by
  rw [←tileMap_image_body]
  apply Set.image_congr
  exact tileHomeomorph_on_body p T i

include p T in
theorem curvedBody_interior_nonempty (i : I) : (interior curvedBody).Nonempty := by
  rw [←tileHomeomorph_image_body p T i,←(tileHomeomorph p T i).image_interior]
  exact euclideanBody_interior_nonempty.image _

include p T in
theorem curvedBody_closure_interior (i : I) : closure (interior curvedBody) = curvedBody := by
  rw [←tileHomeomorph_image_body p T i,←(tileHomeomorph p T i).image_interior,
    ←(tileHomeomorph p T i).image_closure,euclideanBody_closure_interior]

end Forward
end
end LiteralPlanar
