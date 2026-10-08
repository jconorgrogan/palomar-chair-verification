module

public import SparseMonotiles.StripCreaseCrossingGenericKey
public import SparseMonotiles.StripCreaseCrossingCarrierStrip

@[expose] public section

/-! # Build the actual carrier strip in a key-side Euclidean chart -/
namespace SparseMonotiles
open Set

@[simp] theorem keySideChart_coe_apply {n : ℕ} (k : KeyData (n+1)) (i : Fin n) (b : Bool)
    (v : (keySideAffinePlane k i b).direction) :
    keySideChart k i b v = (v : Point (n+1)) + rationalPoint k.apex := rfl

/-- A retained side-face boundary equation is never the selected side. -/
theorem pyramidSideBoundary_halfspace_ne_selected {n : ℕ} (i : Fin n) (b : Bool)
    (a : PyramidSideBoundaryIndex i) :
    pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) ≠ (.inr (i,b) : PyramidHalfspaceIndex n) := by
  cases a with
  | none => simp [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex]
  | some a =>
      rcases a with ⟨j,c⟩
      intro heq
      have hpair : (j.val,c) = (i,b) := Sum.inr.inj heq
      exact j.property (congrArg Prod.fst hpair)

/-- From an aligned physical carrier edge, construct the whole open convex
quarter strip and its inward unit ray inside the actual key-side chart. -/
theorem keySideChart_aligned_carrier_strip
    {n : ℕ} (hn : 2 ≤ n) (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (f : Contact.Facet (n+1))
    (j : Fin (n+1)) (hj : j ≠ f.axis) (upper : Bool) {p : Point (n+1)}
    (hside : keyPyramidHalfspaceSlack k (.inr (i,b)) p = 0)
    (hother : ∀ a : PyramidHalfspaceIndex n, a ≠ .inr (i,b) → 0 < keyPyramidHalfspaceSlack k a p)
    (hplane : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0 ↔
      e x f.axis = (f.gridFacet.anchor f.axis : ℝ))
    (hjend : e p j = (f.cell j : ℝ)+(if upper then 1 else 0))
    (hotherCell : ∀ a, a ≠ f.axis → a ≠ j →
      (f.cell a : ℝ) < e p a ∧ e p a < (f.cell a : ℝ)+1) :
    ∃ O : Set (keySideAffinePlane k i b).direction,
      IsOpen O ∧ Convex ℝ O ∧
      (∀ x ∈ O, e (keySideChart k i b x) ∈ carrierFacetEdgeStrip f j upper) ∧
      ∃ r u : (keySideAffinePlane k i b).direction,
        keySideChart k i b r = p ∧ r ∈ interior (keySideChart k i b ⁻¹' keySolid k) ∧
        ‖u‖ = 1 ∧ ∀ t : ℝ, 0 < t → t < 1/4 → r+t•u ∈ O := by
  classical
  let P := keySideAffinePlane k i b
  let chart := keySideChart k i b
  have hpP : p ∈ P := (mem_keySideAffinePlane_iff k hd i b p).mpr hside
  obtain ⟨r,hrp⟩ := (Set.ext_iff.mp (range_keySideChart k i b) p).mpr hpP
  let v := carrierEdgeInwardVector j upper
  have hv : ‖v‖ = 1 := carrierEdgeInwardVector_norm j upper
  have hpaxis : e p f.axis = (f.gridFacet.anchor f.axis : ℝ) := (hplane p).mp hside
  have hnew : e.symm (e p+v) ∈ P := by
    apply (mem_keySideAffinePlane_iff k hd i b _).mpr
    apply (hplane _).mpr
    simpa [v,carrierEdgeInwardVector,EuclideanSpace.single_apply,Ne.symm hj] using hpaxis
  have hvec : e.linearIsometryEquiv.symm v = e.symm (e p+v)-p := by
    apply e.linearIsometryEquiv.injective
    rw [e.linearIsometryEquiv.apply_symm_apply]
    have h := e.map_vsub (e.symm (e p+v)) p
    simpa using h.symm
  have hdir : e.linearIsometryEquiv.symm v ∈ P.direction := by
    rw [hvec]
    exact AffineSubspace.vsub_mem_direction hnew hpP
  let u : P.direction := ⟨e.linearIsometryEquiv.symm v,hdir⟩
  let c : P.direction →ᵃⁱ[ℝ] Point (n+1) := e.toAffineIsometry.comp chart
  let O : Set P.direction := c ⁻¹' carrierFacetEdgeStrip f j upper
  have hcplane (x : P.direction) : c x f.axis = (f.gridFacet.anchor f.axis : ℝ) :=
    (hplane (chart x)).mp (keySideChart_selected_zero k hd i b x)
  refine ⟨O,carrierFacetEdgeStrip_preimage_isOpen f j upper c.toAffineMap c.continuous hcplane,
    (carrierFacetEdgeStrip_convex f j upper).affine_preimage c.toAffineMap,
    fun x hx => hx,r,u,hrp,?_,?_,?_⟩
  · let sf := keySideBoundarySlack k i chart.toAffineMap
    have hs (a : PyramidSideBoundaryIndex i) : 0 < sf a r := by
      change 0 < keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) (chart r)
      rw [hrp]
      exact hother _ (pyramidSideBoundary_halfspace_ne_selected i b a)
    have hreg := keySideBoundary_chart_region hn k hc hr hh hw i b chart.toAffineMap
      (keySideChart_selected_zero k hd i b)
    change r ∈ interior (chart.toAffineMap ⁻¹' keySolid k)
    rw [hreg]
    exact mem_interior_closedAffineRegion_of_pos sf
      (fun a => (continuous_keyPyramidHalfspaceSlack k _).comp chart.continuous) hs
  · change ‖e.linearIsometryEquiv.symm v‖ = 1
    simpa using hv
  · intro t ht htq
    have hmap : c (r+t•u) = e p+t•v := by
      change e (chart (r+t•u)) = _
      have hchart : chart (r+t•u) = p+t•(u : Point (n+1)) := by
        change ((r : Point (n+1))+t•(u : Point (n+1)))+rationalPoint k.apex = _
        have hrp' : (r : Point (n+1))+rationalPoint k.apex = p := hrp
        rw [add_right_comm,hrp']
      rw [hchart]
      have he := e.map_vadd p (t•(u : Point (n+1)))
      simpa [u,map_smul,add_comm] using he
    change c (r+t•u) ∈ carrierFacetEdgeStrip f j upper
    rw [hmap]
    exact carrierFacetEdgeStrip_contains_unit_ray f j hj upper hpaxis hjend hotherCell t ht htq

/-- An aligned actual carrier edge forces a generic genuine key crease
inside its explicit quarter strip, with an actual codimension-two span. -/
theorem aligned_carrier_edge_crosses_generic_key_crease
    {n : ℕ} (hn : 2 ≤ n) {κ : Type*} [Countable κ] (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (hd : ∀ j b, 0 < keySideDistance k j b) (i : Fin n) (b : Bool)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (f : Contact.Facet (n+1))
    (j : Fin (n+1)) (hj : j ≠ f.axis) (upper : Bool) {p : Point (n+1)}
    (hside : keyPyramidHalfspaceSlack k (.inr (i,b)) p = 0)
    (hother : ∀ a : PyramidHalfspaceIndex n, a ≠ .inr (i,b) → 0 < keyPyramidHalfspaceSlack k a p)
    (hplane : ∀ x, keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0 ↔
      e x f.axis = (f.gridFacet.anchor f.axis : ℝ))
    (hjend : e p j = (f.cell j : ℝ)+(if upper then 1 else 0))
    (hotherCell : ∀ a, a ≠ f.axis → a ≠ j →
      (f.cell a : ℝ) < e p a ∧ e p a < (f.cell a : ℝ)+1)
    (hdiam : Metric.diam (keySolid k) < 1/4)
    (H : κ → AffineSubspace ℝ (Point (n+1))) :
    ∃ a : PyramidSideBoundaryIndex i, ∃ y : Point (n+1), ∃ L : AffineSubspace ℝ (Point (n+1)),
      y ∈ keySolid k ∧ e y ∈ carrierFacetEdgeStrip f j upper ∧
      keyPyramidHalfspaceSlack k (.inr (i,b)) y = 0 ∧
      keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) y = 0 ∧
      (∀ z : PyramidHalfspaceIndex n, z ≠ .inr (i,b) →
        z ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) → 0 < keyPyramidHalfspaceSlack k z y) ∧
      y ∈ L ∧ Module.finrank ℝ L.direction+2=n+1 ∧
      (∀ x ∈ L, keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0) ∧
      ∀ z, y ∈ H z → L ≤ H z := by
  obtain ⟨O,hO,hconv,hstrip,r,u,hrp,hrInterior,hu,hray⟩ := keySideChart_aligned_carrier_strip
    hn k hc hr hh hw hd i b e f j hj upper hside hother hplane hjend hotherCell
  obtain ⟨a,x,hx,hsolid,_,hside',ha,hstrict,hxL,hcodim,hzeros,hgeneric⟩ :=
    keySideFace_quarter_strip_crossing hn k hc hr hh hw hd i b hO hconv hrInterior hu hdiam hray H
  exact ⟨a,keySideChart k i b x,keySideCreasePlane k i (keySideChart k i b).toAffineMap a,
    hsolid,hstrip x hx,hside',ha,hstrict,hxL,hcodim,fun y hy => (hzeros y hy).1,hgeneric⟩

#print axioms aligned_carrier_edge_crosses_generic_key_crease
#print axioms keySideChart_aligned_carrier_strip
end SparseMonotiles
