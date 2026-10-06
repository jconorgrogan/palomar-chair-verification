module

public import SparseMonotiles.StripCreaseCrossingKey
public import SparseMonotiles.StripCreaseCrossingRidge
public import SparseMonotiles.StripCreaseCrossingStrict
public import SparseMonotiles.StripCreaseCrossingChart

@[expose] public section

/-!
# Complete strip-to-generic-key-crease bridge

The crossing supplies the actual solid membership, genuine facet pair,
exact codimension-two affine span, strictly inactive omitted inequalities,
and the active-neighbor-plane containment required by physical sector proofs.
-/
namespace SparseMonotiles
open Set

/-- Ambient affine span of a pruned side-face crease in an intrinsic chart. -/
noncomputable def keySideCreasePlane {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : KeyData (n+1)) (i : Fin n)
    (chart : E →ᵃ[ℝ] Point (n+1)) (a : PyramidSideBoundaryIndex i) :
    AffineSubspace ℝ (Point (n+1)) :=
  (affineFormPlane (keySideBoundarySlack k i chart a) 0).map chart

/-- A strip crossing of an actual key side face yields all the geometric
premises of the literal physical key-crease inventory, simultaneously generic
for every plane in the supplied countable ambient inventory. -/
theorem keySideFace_strip_crosses_full_generic_crease
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
    (H : κ → AffineSubspace ℝ (Point (n+1))) :
    ∃ a : PyramidSideBoundaryIndex i, ∃ x ∈ O,
      chart x ∈ keySolid k ∧
      IsPyramidRidgePair (some (i,b)) (pyramidSideBoundaryFacet i a) ∧
      keyPyramidHalfspaceSlack k (.inr (i,b)) (chart x) = 0 ∧
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a))
        (chart x) = 0 ∧
      (∀ j : PyramidHalfspaceIndex n, j ≠ .inr (i,b) →
        j ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) →
        0 < keyPyramidHalfspaceSlack k j (chart x)) ∧
      chart x ∈ keySideCreasePlane k i chart.toAffineMap a ∧
      Module.finrank ℝ (keySideCreasePlane k i chart.toAffineMap a).direction+2=n+1 ∧
      (∀ y ∈ keySideCreasePlane k i chart.toAffineMap a,
        keyPyramidHalfspaceSlack k (.inr (i,b)) y = 0 ∧
        keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) y = 0) ∧
      ∀ j, chart x ∈ H j → keySideCreasePlane k i chart.toAffineMap a ≤ H j := by
  obtain ⟨a,x,hx,hsolid,hzero,hstrict,hgeneric⟩ := keySideFace_unit_strip_crosses_generic_crease
    hn k hc hr hh hw hd i b chart hdim hselected hO hconv hradius hp hu hdiam hray
    (fun j => (H j).comap chart.toAffineMap)
  have hcodim := (keySideBoundary_chart_crease_codimension hn k hh hd i b
    chart.toAffineMap chart.injective hdim hselected a hzero).2
  refine ⟨a,x,hx,hsolid,pyramidSideBoundary_is_genuine_ridge_pair i b a,hselected x,hzero,
    keySideBoundary_full_other_slacks_pos hn k hc hr hh hw i b a hsolid (hselected x) hstrict,
    ?_,hcodim,?_,?_⟩
  · exact ⟨x,(mem_affineFormPlane _ _ _).mpr hzero,rfl⟩
  · rintro y ⟨z,hz,rfl⟩
    exact ⟨hselected z,(mem_affineFormPlane _ _ _).mp hz⟩
  · intro j hxH y hy
    rcases hy with ⟨z,hz,rfl⟩
    exact hgeneric j hxH hz

/-- Quarter-strip specialization with an explicitly constructed Euclidean
sideplane chart. The chart dimension and selected-plane equations are proved
internally; the diameter input is supplied by the exact T5/T7 key estimates. -/
theorem keySideFace_quarter_strip_crossing
    {n : ℕ} (hn : 2 ≤ n) {κ : Type*} [Countable κ]
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    {O : Set (keySideAffinePlane k i b).direction}
    (hO : IsOpen O) (hconv : Convex ℝ O)
    {p u : (keySideAffinePlane k i b).direction}
    (hp : p ∈ interior (keySideChart k i b ⁻¹' keySolid k)) (hu : ‖u‖ = 1)
    (hdiam : Metric.diam (keySolid k) < 1/4)
    (hray : ∀ t : ℝ, 0 < t → t < 1/4 → p+t•u ∈ O)
    (H : κ → AffineSubspace ℝ (Point (n+1))) :
    ∃ a : PyramidSideBoundaryIndex i, ∃ x ∈ O,
      keySideChart k i b x ∈ keySolid k ∧
      IsPyramidRidgePair (some (i,b)) (pyramidSideBoundaryFacet i a) ∧
      keyPyramidHalfspaceSlack k (.inr (i,b)) (keySideChart k i b x) = 0 ∧
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a))
        (keySideChart k i b x) = 0 ∧
      (∀ j : PyramidHalfspaceIndex n, j ≠ .inr (i,b) →
        j ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) →
        0 < keyPyramidHalfspaceSlack k j (keySideChart k i b x)) ∧
      keySideChart k i b x ∈ keySideCreasePlane k i (keySideChart k i b).toAffineMap a ∧
      Module.finrank ℝ (keySideCreasePlane k i (keySideChart k i b).toAffineMap a).direction+2=n+1 ∧
      (∀ y ∈ keySideCreasePlane k i (keySideChart k i b).toAffineMap a,
        keyPyramidHalfspaceSlack k (.inr (i,b)) y = 0 ∧
        keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) y = 0) ∧
      ∀ j, keySideChart k i b x ∈ H j →
        keySideCreasePlane k i (keySideChart k i b).toAffineMap a ≤ H j :=
  keySideFace_strip_crosses_full_generic_crease hn k hc hr hh hw hd i b (keySideChart k i b)
    (keySideAffinePlane_direction_finrank k i b) (keySideChart_selected_zero k hd i b)
    hO hconv (by norm_num) hp hu hdiam hray H

#print axioms keySideFace_strip_crosses_full_generic_crease
#print axioms keySideFace_quarter_strip_crossing
end SparseMonotiles
