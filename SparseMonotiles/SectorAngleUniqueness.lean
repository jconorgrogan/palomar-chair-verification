module

public import SparseMonotiles.SectorAngleSumPlaneGeometry

@[expose] public section

/-! # The angle of an actual sector is geometrically unique
The value is recovered from the actual angular-trace measure. This lets a
right-angle seam be recognized without carrying a chosen numerical label.
-/
namespace SparseMonotiles.SectorAngleSum
open Set MeasureTheory

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem HasSectorAngle.measure_angularTraceWith
    {S : Set E} {θ : ℝ} (h : HasSectorAngle S θ) (e : ℂ ≃ₗᵢ[ℝ] E) :
    volume (angularTraceWith e S) = ENNReal.ofReal θ := by
  obtain ⟨c,hclosed,hopen⟩ := h.arc_sandwich e
  have hc := measure_closedArc c h.bounds.2
  have ho : volume (openArc c θ) = ENNReal.ofReal θ := by
    calc
      volume (openArc c θ) = volume (closedArc c θ) :=
        (measure_congr (closedArc_ae_eq_openArc c θ)).symm
      _ = ENNReal.ofReal θ := hc
  apply le_antisymm
  · exact (measure_mono hclosed).trans_eq hc
  · rw [← ho]
    apply measure_mono
    intro q hq
    change e (direction q) ∈ S
    exact interior_subset (show e (direction q) ∈ interior S from hopen hq)

/-- Genuine geometric sector witnesses cannot assign different angles to the
same cone, even if they use different supporting-normal descriptions. -/
theorem HasSectorAngle.angle_unique [FiniteDimensional ℝ E]
    (hdim : Module.finrank ℝ E = 2) {S : Set E} {θ φ : ℝ}
    (hθ : HasSectorAngle S θ) (hφ : HasSectorAngle S φ) : θ = φ := by
  let b : OrthonormalBasis (Fin 2) ℝ E := (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let e := Complex.isometryOfOrthonormal b
  have h := (hθ.measure_angularTraceWith e).symm.trans (hφ.measure_angularTraceWith e)
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_ofReal hθ.bounds.1,ENNReal.toReal_ofReal hφ.bounds.1] using hr

#print axioms HasSectorAngle.measure_angularTraceWith
#print axioms HasSectorAngle.angle_unique
end SparseMonotiles.SectorAngleSum
