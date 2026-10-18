module

public import ProductClosure.ProductGraphSiteCoproduct
public import ProductClosure.ProductGraphExclusions

@[expose] public section

/-! All wrong-factor and cross-type contacts are excluded in one common dimension. -/
namespace ProductClosure.ProductGraphCommonExclusions
noncomputable section
open NativeCompiler ProductGraphOrbit ProductGraphSites ProductGraphPlacements
open ProductGraphRightSites ProductGraphRightPlacements ProductGraphSiteCoproduct ProductGraphExclusions
variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a+1))}
    {SB : Finset (Polycube.LatticeIndex (b+1))}

@[simp] theorem commonRightSite_eq_rightRawSite (u : Site SB) (c : Polycube.Cell SA)
    (p : Passive b (a+1)) :
    commonRightSite u c p = rightRawSite c u.1 (rightCommonFrameEquiv (u.2,p)) := by
  apply Prod.ext
  · exact facetCast_chain (rightProductDim b (a+1)) (tangentSwap a b) (productDim a (b+1))
      (Polycube.productCells SA SB) (nativeRightProduct_cast_eq SA SB)
      (Polycube.productFacetRight c u.1)
  · rfl

@[simp] theorem placedNormal_commonLiftRight (g : Space b ≃ᵢ Space b)
    (x : Space a) (y : Space b) :
    placedNormal (commonLiftRight g) (appendNative x y) = appendNative x (placedNormal g y) := by
  rw [placedNormal_eq_sub, ← appendNative_zero (a := a) (b := b+1), commonLiftRight_append,
    commonLiftRight_append, appendNative_sub, sub_zero, placedNormal_eq_sub]

theorem commonLiftRight_proper (g : Space b ≃ᵢ Space b) (hg : IsProperPlacement g) :
    IsProperPlacement (commonLiftRight (a := a) g) := by
  rw [commonLiftRight, poseCast_proper_iff]
  exact liftRight_proper g hg

/-- A B-only placement leaves the A carrier unchanged, so two A-normal
exposed facets cannot acquire a genuine opposite contact. -/
theorem no_right_transport_left_left (g : Space b ≃ᵢ Space b)
    (u v : Site SA) (c d : Polycube.Cell SB) (p q : Passive a (b+1)) :
    ¬SiteTransport (commonLiftRight g) (leftSite u c p) (leftSite v d q) := by
  intro ht
  have hn := ht.2.1
  rw [leftSite_normal, leftSite_normal, placedNormal_commonLiftRight, appendNative_neg] at hn
  have hz : placedNormal g 0 = 0 := by simp [placedNormal]
  rw [hz, neg_zero] at hn
  have hnorm := (appendNative_eq_iff _ _ _ _).mp hn |>.1
  have hc := transport_facetCenter ht
  rw [leftSite_facetCenter, leftSite_facetCenter, commonLiftRight_append] at hc
  have hcenter := (appendNative_eq_iff _ _ _ _).mp hc |>.1
  exact Polycube.not_same_center_opposite_outward v.1 u.1 ⟨hcenter,hnorm⟩

/-- A right-active placement cannot carry a B normal to an A normal. -/
theorem no_right_transport_left_right (g : Space b ≃ᵢ Space b)
    (u : Site SA) (c : Polycube.Cell SB) (p : Passive a (b+1))
    (v : Site SB) (d : Polycube.Cell SA) (q : Passive b (a+1)) :
    ¬SiteTransport (commonLiftRight g) (leftSite u c p) (commonRightSite v d q) := by
  intro ht
  have hn := ht.2.1
  rw [commonRightSite_normal, leftSite_normal, placedNormal_commonLiftRight,
    appendNative_neg, neg_zero] at hn
  have hz := (appendNative_eq_iff _ _ _ _).mp hn |>.1
  have hzero : outward u.1 = 0 := by simpa using congrArg Neg.neg hz.symm
  have hunit := outward_unit u.1
  rw [hzero, norm_zero] at hunit
  norm_num at hunit

/-- The reversed cross-type direction is also impossible. -/
theorem no_right_transport_right_left (g : Space b ≃ᵢ Space b)
    (u : Site SA) (c : Polycube.Cell SB) (p : Passive a (b+1))
    (v : Site SB) (d : Polycube.Cell SA) (q : Passive b (a+1)) :
    ¬SiteTransport (commonLiftRight g) (commonRightSite v d q) (leftSite u c p) := by
  intro ht
  have hn := ht.2.1
  rw [leftSite_normal, commonRightSite_normal, placedNormal_commonLiftRight,
    appendNative_neg, neg_zero] at hn
  have hz := (appendNative_eq_iff _ _ _ _).mp hn |>.1
  have hunit := outward_unit u.1
  rw [hz, norm_zero] at hunit
  norm_num at hunit

#print axioms commonRightSite_eq_rightRawSite
#print axioms no_right_transport_left_left
#print axioms no_right_transport_left_right
#print axioms no_right_transport_right_left
end
end ProductClosure.ProductGraphCommonExclusions
