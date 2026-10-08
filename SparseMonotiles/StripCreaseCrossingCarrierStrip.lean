module

public import SparseMonotiles.StripCreaseCrossingPhysical

@[expose] public section

/-! # The explicit open quarter-width carrier edge strip -/
namespace SparseMonotiles
open Set

noncomputable def carrierEdgeDepth {d : ℕ} (f : Contact.Facet d) (j : Fin d)
    (upper : Bool) : Point d →ᵃ[ℝ] ℝ :=
  if upper then AffineMap.const ℝ (Point d) ((f.cell j : ℝ)+1) -
    (EuclideanSpace.proj j).toLinearMap.toAffineMap
  else (EuclideanSpace.proj j).toLinearMap.toAffineMap -
    AffineMap.const ℝ (Point d) (f.cell j : ℝ)

@[simp] theorem carrierEdgeDepth_apply {d : ℕ} (f : Contact.Facet d)
    (j : Fin d) (upper : Bool) (x : Point d) :
    carrierEdgeDepth f j upper x =
      if upper then (f.cell j : ℝ)+1-x j else x j-(f.cell j : ℝ) := by
  cases upper <;> rfl

/-- The entire relative-open strip adjoining a unit facet's chosen edge. -/
def carrierFacetEdgeStrip {d : ℕ} (f : Contact.Facet d) (j : Fin d)
    (upper : Bool) : Set (Point d) :=
  f.relativeInterior ∩ carrierEdgeDepth f j upper ⁻¹' Ioo 0 (1/4)

/-- The relative interior of a literal unit carrier facet is convex. -/
theorem carrierFacet_relativeInterior_convex {d : ℕ} (f : Contact.Facet d) :
    Convex ℝ f.relativeInterior := by
  have heq : f.relativeInterior =
      (EuclideanSpace.proj f.axis).toLinearMap.toAffineMap ⁻¹'
        {(f.gridFacet.anchor f.axis : ℝ)} ∩
      ⋂ j : Fin d, ⋂ (_ : j ≠ f.axis),
        (EuclideanSpace.proj j).toLinearMap.toAffineMap ⁻¹'
          Ioo (f.cell j : ℝ) ((f.cell j : ℝ)+1) := by
    ext x
    simp [Contact.Facet.relativeInterior]
  rw [heq]
  exact ((convex_singleton _).affine_preimage _).inter
    (convex_iInter fun j => convex_iInter fun _ => (convex_Ioo _ _).affine_preimage _)

/-- The edge strip is convex in its actual supporting hyperplane. -/
theorem carrierFacetEdgeStrip_convex {d : ℕ} (f : Contact.Facet d) (j : Fin d)
    (upper : Bool) : Convex ℝ (carrierFacetEdgeStrip f j upper) :=
  (carrierFacet_relativeInterior_convex f).inter ((convex_Ioo _ _).affine_preimage _)

/-- In any continuous intrinsic chart lying in the supporting plane, the
carrier edge strip is genuinely open. -/
theorem carrierFacetEdgeStrip_preimage_isOpen {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Contact.Facet d) (j : Fin d) (upper : Bool)
    (chart : E →ᵃ[ℝ] Point d) (hchart : Continuous chart)
    (hplane : ∀ x, chart x f.axis = (f.gridFacet.anchor f.axis : ℝ)) :
    IsOpen (chart ⁻¹' carrierFacetEdgeStrip f j upper) := by
  have hcoord (a : Fin d) : Continuous (fun x : E => chart x a) :=
    (EuclideanSpace.proj a).continuous.comp hchart
  have hfacet : IsOpen (chart ⁻¹' f.relativeInterior) := by
    have heq : chart ⁻¹' f.relativeInterior =
        {x | ∀ a, a ≠ f.axis → (f.cell a : ℝ) < chart x a ∧
          chart x a < (f.cell a : ℝ)+1} := by
      ext x
      simp [Contact.Facet.relativeInterior,hplane]
    rw [heq]
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun _ =>
      (isOpen_lt continuous_const (hcoord a)).inter (isOpen_lt (hcoord a) continuous_const)
  have hdepth : Continuous (fun x : E => carrierEdgeDepth f j upper (chart x)) := by
    cases upper
    · exact (hcoord j).sub continuous_const
    · exact continuous_const.sub (hcoord j)
  exact hfacet.inter (isOpen_Ioo.preimage hdepth)

/-- Each actual strip point is less than a quarter from a genuine integer
codimension-two skeleton point on the chosen edge. -/
theorem carrierFacetEdgeStrip_near_integerSkeleton {d : ℕ} (f : Contact.Facet d)
    (j : Fin d) (hj : j ≠ f.axis) (upper : Bool) {x : Point d}
    (hx : x ∈ carrierFacetEdgeStrip f j upper) :
    ∃ z ∈ integerSkeleton d, dist x z < 1/4 := by
  let m : ℤ := f.cell j + if upper then 1 else 0
  let z : Point d := x + ((m : ℝ)-x j) • EuclideanSpace.single j 1
  have hzaxis : z f.axis = (f.gridFacet.anchor f.axis : ℝ) := by
    simpa [z,EuclideanSpace.single_apply,Ne.symm hj] using hx.1.1
  have hzj : z j = (m : ℝ) := by simp [z,EuclideanSpace.single_apply]
  refine ⟨z,⟨f.axis,j,Ne.symm hj,⟨f.gridFacet.anchor f.axis,hzaxis⟩,⟨m,hzj⟩⟩,?_⟩
  have hdist : dist x z = |(m : ℝ)-x j| := by
    rw [dist_comm,dist_eq_norm]
    change ‖x+((m : ℝ)-x j) • EuclideanSpace.single j 1-x‖ = _
    rw [add_sub_cancel_left,norm_smul]
    simp
  rw [hdist]
  have hdepth := hx.2
  cases upper
  · change 0 < x j-(f.cell j : ℝ) ∧ x j-(f.cell j : ℝ) < 1/4 at hdepth
    have hm : (m : ℝ) = (f.cell j : ℝ) := by simp [m]
    rw [hm,abs_sub_comm]
    rw [abs_of_pos hdepth.1]
    exact hdepth.2
  · change 0 < (f.cell j : ℝ)+1-x j ∧ (f.cell j : ℝ)+1-x j < 1/4 at hdepth
    have hm : (m : ℝ) = (f.cell j : ℝ)+1 := by simp [m]
    rw [hm,abs_of_pos hdepth.1]
    exact hdepth.2

/-- Unit coordinate vector pointing from the edge into the facet. -/
noncomputable def carrierEdgeInwardVector {d : ℕ} (j : Fin d) (upper : Bool) : Point d :=
  EuclideanSpace.single j (if upper then -1 else 1)

@[simp] theorem carrierEdgeInwardVector_norm {d : ℕ} (j : Fin d) (upper : Bool) :
    ‖carrierEdgeInwardVector j upper‖ = 1 := by
  cases upper <;> simp [carrierEdgeInwardVector]

/-- Starting at any relative-interior edge point, the entire open unit ray
of length one quarter lies in the strip. The other facet coordinates need
only lie strictly inside their unit intervals. -/
theorem carrierFacetEdgeStrip_contains_unit_ray {d : ℕ} (f : Contact.Facet d)
    (j : Fin d) (hj : j ≠ f.axis) (upper : Bool) {z : Point d}
    (hzaxis : z f.axis = (f.gridFacet.anchor f.axis : ℝ))
    (hzj : z j = (f.cell j : ℝ)+if upper then 1 else 0)
    (hzother : ∀ a, a ≠ f.axis → a ≠ j →
      (f.cell a : ℝ) < z a ∧ z a < (f.cell a : ℝ)+1) :
    ∀ t : ℝ, 0 < t → t < 1/4 →
      z+t•carrierEdgeInwardVector j upper ∈ carrierFacetEdgeStrip f j upper := by
  intro t ht htq
  constructor
  · constructor
    · simpa [carrierEdgeInwardVector,EuclideanSpace.single_apply,Ne.symm hj] using hzaxis
    · intro a hai
      by_cases haj : a = j
      · subst a
        cases upper <;>
          simp [carrierEdgeInwardVector,EuclideanSpace.single_apply] at hzj ⊢ <;>
          constructor <;> linarith
      · simpa [carrierEdgeInwardVector,EuclideanSpace.single_apply,haj] using hzother a hai haj
  · change 0 < carrierEdgeDepth f j upper (z+t•carrierEdgeInwardVector j upper) ∧
      carrierEdgeDepth f j upper (z+t•carrierEdgeInwardVector j upper) < 1/4
    have hdepth : carrierEdgeDepth f j upper (z+t•carrierEdgeInwardVector j upper) = t := by
      cases upper <;> simp [carrierEdgeInwardVector,EuclideanSpace.single_apply] at hzj ⊢ <;> linarith
    rw [hdepth]
    exact ⟨ht,htq⟩

/-- Every point of the literal T5 edge strip has the exact halfspace germ. -/
theorem T5_carrierFacetEdgeStrip_halfspace (f : Contact.Facet 5)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 5) (hj : j ≠ f.axis) (upper : Bool) {x : Point 5}
    (hx : x ∈ carrierFacetEdgeStrip f j upper) : LocalSetEq x T5 f.inwardHalfspace := by
  obtain ⟨z,hz,hd⟩ := carrierFacetEdgeStrip_near_integerSkeleton f j hj upper hx
  exact T5_facet_halfspace_near_skeleton f howner hexposed hx.1 hz hd

/-- Every point of the literal T7 edge strip has the exact halfspace germ. -/
theorem T7_carrierFacetEdgeStrip_halfspace (f : Contact.Facet 7)
    (howner : Contact.IsChairCell f.cell) (hexposed : ¬ Contact.IsChairCell f.neighbor)
    (j : Fin 7) (hj : j ≠ f.axis) (upper : Bool) {x : Point 7}
    (hx : x ∈ carrierFacetEdgeStrip f j upper) : LocalSetEq x T7 f.inwardHalfspace := by
  obtain ⟨z,hz,hd⟩ := carrierFacetEdgeStrip_near_integerSkeleton f j hj upper hx
  exact T7_facet_halfspace_near_skeleton f howner hexposed hx.1 hz hd

#print axioms carrierFacetEdgeStrip_contains_unit_ray
#print axioms carrierFacetEdgeStrip_convex
#print axioms carrierFacetEdgeStrip_preimage_isOpen
#print axioms carrierFacetEdgeStrip_near_integerSkeleton
#print axioms T5_carrierFacetEdgeStrip_halfspace
#print axioms T7_carrierFacetEdgeStrip_halfspace
end SparseMonotiles
