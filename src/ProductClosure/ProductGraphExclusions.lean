module

public import ProductClosure.ProductGraphPlacements
public import ProductClosure.FacetCompatibility

@[expose] public section

/-! Wrong-factor and cross-type edges are impossible for the actual product
carrier. This uses exposed-facet occupancy, rather than stipulating a typed graph. -/
namespace ProductClosure.ProductGraphExclusions
noncomputable section
open ProductGraphSites ProductGraphOrbit ProductGraphPlacements NativeCompiler
variable {a b : ℕ}
variable {S : Finset (Polycube.LatticeIndex (a+1))}
    {T : Finset (Polycube.LatticeIndex b)}

/-- A right-type facet in the same native dimension normalization as leftSite. -/
def rightRawFacet (c : Polycube.Cell S) (f : Polycube.Facet T) :
    Polycube.Facet (nativeProduct S T) :=
  Polycube.castFacetEquiv (productDim a b) _ (Polycube.productFacetRight c f)

def rightRawSite (c : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    Site (nativeProduct S T) := (rightRawFacet c f,F)

@[simp] theorem rightRawFacet_axis (c : Polycube.Cell S) (f : Polycube.Facet T) :
    (rightRawFacet c f).axis = ambientEquiv a b (.inr f.axis) := by
  simp [rightRawFacet, ambientEquiv, Polycube.productFacetRight]

@[simp] theorem rightRawFacet_positive (c : Polycube.Cell S) (f : Polycube.Facet T) :
    (rightRawFacet c f).positive = f.positive := by
  simp [rightRawFacet, Polycube.productFacetRight]

theorem rightRawSite_normal (c : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    outward (rightRawSite c f F).1 = appendNative 0 (Polycube.outward f) := by
  simp only [rightRawSite, outward, normalSign, normalIndex,
    rightRawFacet_axis, rightRawFacet_positive]
  rw [← appendNative_single_passive]
  change sign f.positive • appendNative 0 (EuclideanSpace.single f.axis 1) = _
  rw [← appendNative_smul, smul_zero]
  rfl

theorem rightRawSite_facetCenter (c : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    facetCenter (rightRawSite c f F).1 =
      appendNative (Polycube.latticeCenter c.val) (Polycube.facetCenter f) := by
  change Polycube.facetCenter (Polycube.castFacetEquiv (productDim a b) _ _) = _
  rw [Polycube.castFacetEquiv_center, Polycube.productFacetRight_center]
  rfl

/-- An A-only generator cannot create a B-normal contact: its unchanged
B carrier would need two exposed facets at the same center with opposite normals. -/
theorem no_left_transport_right_right (g : Space a ≃ᵢ Space a)
    (c d : Polycube.Cell S) (f h : Polycube.Facet T) (F H : Frame (a+b)) :
    ¬SiteTransport (liftLeft g) (rightRawSite c f F) (rightRawSite d h H) := by
  intro ht
  have hn := ht.2.1
  rw [rightRawSite_normal, rightRawSite_normal, placedNormal_liftLeft, appendNative_neg] at hn
  have hz : placedNormal g 0 = 0 := by simp [placedNormal]
  rw [hz, neg_zero] at hn
  have hnorm := (appendNative_eq_iff _ _ _ _).mp hn |>.2
  have hc := transport_facetCenter ht
  rw [rightRawSite_facetCenter, rightRawSite_facetCenter, liftLeft_append] at hc
  have hcenter := (appendNative_eq_iff _ _ _ _).mp hc |>.2
  exact Polycube.not_same_center_opposite_outward h f ⟨hcenter,hnorm⟩

/-- An active-block isometry cannot transport a passive normal to an active one. -/
theorem no_left_transport_left_right (g : Space a ≃ᵢ Space a)
    (u : Site S) (c : Polycube.Cell T) (p : Passive a b)
    (d : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    ¬SiteTransport (liftLeft g) (leftSite u c p) (rightRawSite d f F) := by
  intro ht
  have hn := ht.2.1
  rw [rightRawSite_normal, leftSite_normal, placedNormal_liftLeft, appendNative_neg] at hn
  have hz : placedNormal g 0 = 0 := by simp [placedNormal]
  rw [hz, neg_zero] at hn
  have hzero := (appendNative_eq_iff _ _ _ _).mp hn |>.1
  have hnzero : outward u.1 = 0 := by simpa using congrArg Neg.neg hzero.symm
  have hunit := outward_unit u.1
  rw [hnzero, norm_zero] at hunit
  norm_num at hunit

/-- The reversed cross-type direction is equally impossible, without a
properness hypothesis on the active placement. -/
theorem no_left_transport_right_left (g : Space a ≃ᵢ Space a)
    (u : Site S) (c : Polycube.Cell T) (p : Passive a b)
    (d : Polycube.Cell S) (f : Polycube.Facet T) (F : Frame (a+b)) :
    ¬SiteTransport (liftLeft g) (rightRawSite d f F) (leftSite u c p) := by
  intro ht
  have hn := ht.2.1
  rw [leftSite_normal, rightRawSite_normal, placedNormal_liftLeft, appendNative_neg, neg_zero] at hn
  have hzero := (appendNative_eq_iff _ _ _ _).mp hn |>.1
  have hnorm := congrArg norm hzero
  simp [placedNormal, outward_unit] at hnorm

#print axioms no_left_transport_right_right
#print axioms no_left_transport_left_right
#print axioms no_left_transport_right_left
end
end ProductClosure.ProductGraphExclusions
