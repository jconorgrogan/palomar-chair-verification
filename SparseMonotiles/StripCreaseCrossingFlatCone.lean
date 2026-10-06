module

public import SparseMonotiles.StripCreaseCrossingPhysical
public import SparseMonotiles.SectorRootBoundary

@[expose] public section

/-! # Exact flat-cone adapter for the carrier edge strip -/
namespace SparseMonotiles
open Set NormalSpaceGeometry

/-- A carrier facet halfspace in any physical frame restricts to a genuine
π-sector whenever its supporting plane contains the ridge. -/
theorem carrier_facet_halfspace_normal_model_angle {d : ℕ}
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (f : Contact.Facet d)
    (R : AffineSubspace ℝ (Point d)) {p : Point d} (hp : p ∈ R)
    (hplane : ∀ x ∈ R, e x f.axis = (f.gridFacet.anchor f.axis : ℝ))
    {T : Set (Point d)} {S : Set R.directionᗮ}
    (hS : IsPositiveCone S)
    (hmodel : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' S))
    (hlocal : LocalSetEq p T (e ⁻¹' f.inwardHalfspace)) :
    SectorAngleSum.HasSectorAngle S Real.pi := by
  let n : Point d := e.linearIsometryEquiv.symm (EuclideanSpace.single f.axis 1)
  let slack : Point d → ℝ := fun x => e x f.axis - (f.gridFacet.anchor f.axis : ℝ)
  have hn : n ≠ 0 := by
    have hh : ‖n‖ = 1 := by simp [n]
    intro hz
    simp [hz] at hh
  have hform (x : Point d) : slack x = slack p + 1 * inner (𝕜 := ℝ) n (x-p) := by
    have hmap := e.map_vsub x p
    change e.linearIsometryEquiv (x-p) = e x - e p at hmap
    have hi : inner (𝕜 := ℝ) n (x-p) = e x f.axis-e p f.axis := by
      change inner (𝕜 := ℝ) (e.linearIsometryEquiv.symm (EuclideanSpace.single f.axis 1))
        (x-p) = _
      rw [← e.linearIsometryEquiv.inner_map_map,e.linearIsometryEquiv.apply_symm_apply,hmap]
      simp [EuclideanSpace.inner_single_left]
    rw [hi]
    dsimp [slack]
    ring
  obtain ⟨nR,_,hne,_,_,hpos,hneg⟩ := active_supporting_slack_adapter R hp slack n hn
    (by norm_num : (0 : ℝ) < 1) hform
    (fun x hx => by dsimp [slack]; rw [hplane x hx,sub_self])
  have htransfer {Q : Set R.directionᗮ} (hQ : SectorAngleSum.HasSectorAngle Q Real.pi)
      (hl : LocalSetEq p T (ridgeNormalProjection R p ⁻¹' Q)) :
      SectorAngleSum.HasSectorAngle S Real.pi := by
    have heq := normalCones_eq_of_localSetEq R p hS hQ.positive (hmodel.symm.trans hl)
    exact heq.symm ▸ hQ
  cases hb : f.positive
  · have heq : e ⁻¹' f.inwardHalfspace = {x | 0 ≤ slack x} := by
      ext x
      simp [Contact.Facet.inwardHalfspace,hb,slack,sub_nonneg]
    rw [heq,hpos] at hlocal
    exact htransfer (.halfplane nR hne rfl) hlocal
  · have heq : e ⁻¹' f.inwardHalfspace = {x | slack x ≤ 0} := by
      ext x
      simp [Contact.Facet.inwardHalfspace,hb,slack,sub_nonpos]
    rw [heq,hneg] at hlocal
    exact htransfer (.halfplane (-nR) (neg_ne_zero.mpr hne) rfl) hlocal


/-- At a generic key crease, the literal T5 flat edge strip gives a
contradiction directly. The flat sector and root boundary are derived. -/
theorem T5_key_root_no_carrier_edge_strip
    {tiles : Set (Set (Point 5))} (ht : IsTiling T5 tiles)
    (R : AffineSubspace ℝ (Point 5)) {p : Point 5} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 5)
    (g : tiles → Point 5 ≃ᵢ Point 5)
    (hg : ∀ A : tiles, (A : Set (Point 5)) = g A '' T5)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T5WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T5WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root flat : incidentTiles tiles p) (hne : flat ≠ root) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T5IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (f : Contact.Facet 5) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (hfacet : (g ⟨flat,flat.property.1⟩).symm p ∈ f.relativeInterior)
    (hplane : ∀ x ∈ R, (g ⟨flat,flat.property.1⟩).symm x f.axis =
      (f.gridFacet.anchor f.axis : ℝ))
    {z : Point 5} (hz : z ∈ integerSkeleton 5)
    (hdist : dist ((g ⟨flat,flat.property.1⟩).symm p) z < 1/4) : False := by
  let a := g ⟨flat,flat.property.1⟩
  have hpart := T5_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hlocal := T5_copy_facet_halfspace_near_skeleton a f howner hexposed hfacet hz hdist
  have hpre : a.symm.toRealAffineIsometryEquiv ⁻¹' f.inwardHalfspace = a '' f.inwardHalfspace := by
    ext x
    change a.symm x ∈ f.inwardHalfspace ↔ x ∈ a '' f.inwardHalfspace
    exact ⟨fun hx => ⟨a.symm x,hx,a.apply_symm_apply x⟩,
      fun ⟨y,hy,hxy⟩ => by simpa only [← hxy,a.symm_apply_apply] using hy⟩
  have hlocal' : LocalSetEq p (flat : Set (Point 5))
      (a.symm.toRealAffineIsometryEquiv ⁻¹' f.inwardHalfspace) := by
    rw [hpre,hg ⟨flat,flat.property.1⟩]
    simpa only [a,IsometryEquiv.apply_symm_apply] using hlocal
  have hflat := carrier_facet_halfspace_normal_model_angle a.symm.toRealAffineIsometryEquiv
    f R hp hplane (hpart.2.2.1 flat).2.1 (hpart.2.2.1 flat).2.2 hlocal'
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  have hb := angleInventory_pos_lt_two_pi hinv
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot hb.1 hb.2
    (hpart.2.2.1 root).2.2
  exact T5_generic_key_root_no_flat_incident ht R hp hcodim g hg hactive root flat hne
    hroot hδ hδ' hkey hboundary hflat

/-- At a generic key crease, the literal T7 flat edge strip gives a
contradiction directly. The flat sector and root boundary are derived. -/
theorem T7_key_root_no_carrier_edge_strip
    {tiles : Set (Set (Point 7))} (ht : IsTiling T7 tiles)
    (R : AffineSubspace ℝ (Point 7)) {p : Point 7} (hp : p ∈ R)
    (hcodim : Module.finrank ℝ R.direction + 2 = 7)
    (g : tiles → Point 7 ≃ᵢ Point 7)
    (hg : ∀ A : tiles, (A : Set (Point 7)) = g A '' T7)
    (hactive : ∀ A : incidentTiles tiles p, ∀ j,
      T7WorldAffineFields (g ⟨A,A.property.1⟩) j p = 0 →
        R ≤ affineFormPlane (T7WorldAffineFields (g ⟨A,A.property.1⟩) j) 0)
    (root flat : incidentTiles tiles p) (hne : flat ≠ root) {θ δ : ℝ}
    (hroot : SectorAngleSum.HasSectorAngle (T7IncidentNormalCone g R p root) θ)
    (hδ : 0 < δ) (hδ' : δ < Real.pi/4)
    (hkey : θ = Real.pi-δ ∨ θ = Real.pi+δ)
    (f : Contact.Facet 7) (howner : Contact.IsChairCell f.cell)
    (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (hfacet : (g ⟨flat,flat.property.1⟩).symm p ∈ f.relativeInterior)
    (hplane : ∀ x ∈ R, (g ⟨flat,flat.property.1⟩).symm x f.axis =
      (f.gridFacet.anchor f.axis : ℝ))
    {z : Point 7} (hz : z ∈ integerSkeleton 7)
    (hdist : dist ((g ⟨flat,flat.property.1⟩).symm p) z < 1/4) : False := by
  let a := g ⟨flat,flat.property.1⟩
  have hpart := T7_tiling_normal_cone_partition ht R hp hcodim g hg hactive
  have hlocal := T7_copy_facet_halfspace_near_skeleton a f howner hexposed hfacet hz hdist
  have hpre : a.symm.toRealAffineIsometryEquiv ⁻¹' f.inwardHalfspace = a '' f.inwardHalfspace := by
    ext x
    change a.symm x ∈ f.inwardHalfspace ↔ x ∈ a '' f.inwardHalfspace
    exact ⟨fun hx => ⟨a.symm x,hx,a.apply_symm_apply x⟩,
      fun ⟨y,hy,hxy⟩ => by simpa only [← hxy,a.symm_apply_apply] using hy⟩
  have hlocal' : LocalSetEq p (flat : Set (Point 7))
      (a.symm.toRealAffineIsometryEquiv ⁻¹' f.inwardHalfspace) := by
    rw [hpre,hg ⟨flat,flat.property.1⟩]
    simpa only [a,IsometryEquiv.apply_symm_apply] using hlocal
  have hflat := carrier_facet_halfspace_normal_model_angle a.symm.toRealAffineIsometryEquiv
    f R hp hplane (hpart.2.2.1 flat).2.1 (hpart.2.2.1 flat).2.2 hlocal'
  have hinv : SectorArithmetic.InAngleInventory θ :=
    Or.inr (Or.inr (Or.inr ⟨δ,hδ,hδ',hkey⟩))
  have hb := angleInventory_pos_lt_two_pi hinv
  have hboundary := mem_frontier_of_normal_sector R p hpart.2.1 hroot hb.1 hb.2
    (hpart.2.2.1 root).2.2
  exact T7_generic_key_root_no_flat_incident ht R hp hcodim g hg hactive root flat hne
    hroot hδ hδ' hkey hboundary hflat

#print axioms carrier_facet_halfspace_normal_model_angle
#print axioms T5_key_root_no_carrier_edge_strip
#print axioms T7_key_root_no_carrier_edge_strip
end SparseMonotiles
