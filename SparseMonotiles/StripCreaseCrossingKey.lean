module

public import SparseMonotiles.StripCreaseCrossing
public import SparseMonotiles.StripCreaseCrossingRank
public import SparseMonotiles.Compactness

@[expose] public section

/-! # Unit-strip crossing for actual Euclidean key side faces -/
namespace SparseMonotiles
open Set

/-- The pruned inequalities describe the actual closed side face in any
intrinsic affine chart of its selected supporting plane. -/
theorem keySideBoundary_chart_region {n : ℕ} (hn : 2 ≤ n)
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (i : Fin n) (b : Bool) (chart : E →ᵃ[ℝ] Point (n+1))
    (hselected : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) (chart x) = 0) :
    chart ⁻¹' keySolid k = {x | ∀ a, 0 ≤ keySideBoundarySlack k i chart a x} := by
  ext x
  exact keySidePlane_mem_solid_iff_pruned hn k hc hr hh hw i b (hselected x)

/-- Actual key-sideface version of the thin-strip crossing theorem. The
codimension-two exceptional-set bounds and finite H-representation are now
proved from the key geometry. Every choice of strip, side, and affine-isometric
chart is allowed. The diameter bound is the actual ambient key diameter. -/
theorem keySideFace_unit_strip_crosses_generic_crease
    {n : ℕ} (hn : 2 ≤ n) {E κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Countable κ]
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (hd : ∀ j b, 0 < keySideDistance k j b)
    (i : Fin n) (b : Bool) (chart : E →ᵃⁱ[ℝ] Point (n+1))
    (hdim : Module.finrank ℝ E = n)
    (hselected : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) (chart x) = 0)
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O)
    {p u : E} {r : ℝ} (hradius : 0 < r)
    (hp : p ∈ interior (chart ⁻¹' keySolid k)) (hu : ‖u‖ = 1)
    (hdiam : Metric.diam (keySolid k) < r)
    (hray : ∀ t : ℝ, 0 < t → t < r → p+t•u ∈ O)
    (H : κ → AffineSubspace ℝ E) :
    ∃ a : PyramidSideBoundaryIndex i, ∃ x ∈ O,
      chart x ∈ keySolid k ∧
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a))
        (chart x) = 0 ∧
      (∀ c : PyramidSideBoundaryIndex i, c ≠ a →
        0 < keyPyramidHalfspaceSlack k
          (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i c)) (chart x)) ∧
      ∀ j, x ∈ H j → affineFormPlane (keySideBoundarySlack k i chart.toAffineMap a) 0 ≤ H j := by
  classical
  let f := keySideBoundarySlack k i chart.toAffineMap
  have hf (a : PyramidSideBoundaryIndex i) : Continuous (f a) :=
    (continuous_keyPyramidHalfspaceSlack k _).comp chart.continuous
  have hregion : closedAffineRegion f = chart ⁻¹' keySolid k :=
    (keySideBoundary_chart_region hn k hc hr hh hw i b chart.toAffineMap hselected).symm
  have hbound : Bornology.IsBounded (chart ⁻¹' keySolid k) := by
    apply Metric.isBounded_iff.mpr
    refine ⟨Metric.diam (keySolid k),?_⟩
    intro x hx y hy
    rw [← chart.isometry.dist_eq x y]
    exact Metric.dist_le_diam_of_mem (keySolid_isBounded k) hx hy
  have hdiam' : Metric.diam (chart ⁻¹' keySolid k) < r := by
    have hm : Metric.diam (chart ⁻¹' keySolid k) ≤ Metric.diam (keySolid k) := by
      rw [← chart.isometry.diam_image (chart ⁻¹' keySolid k)]
      exact Metric.diam_mono (image_preimage_subset _ _) (keySolid_isBounded k)
    exact hm.trans_lt hdiam
  have hrank := keySideBoundary_chart_pair_codimension hn k hh hd i b
    chart.toAffineMap chart.injective hdim hselected
  obtain ⟨a,x,hx,hzero,hstrict,hgeneric⟩ := unit_strip_crosses_generic_affine_crease f hf
    hO hconv hrank hradius (hregion.symm ▸ hp) hu (hregion.symm ▸ hbound)
    (hregion.symm ▸ hdiam') hray H
  have hxF : x ∈ closedAffineRegion f := by
    intro c
    by_cases hca : c = a
    · simpa [hca,hzero]
    · exact (hstrict c hca).le
  have hxSolid : chart x ∈ keySolid k := by
    change x ∈ chart ⁻¹' keySolid k
    rw [← hregion]
    exact hxF
  exact ⟨a,x,hx,hxSolid,hzero,hstrict,hgeneric⟩

#print axioms keySideBoundary_chart_region
#print axioms keySideFace_unit_strip_crosses_generic_crease
end SparseMonotiles
