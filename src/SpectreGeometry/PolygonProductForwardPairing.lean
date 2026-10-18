module

public import SpectreGeometry.PolygonProductForwardKeyPoses
public import SpectreGeometry.PolygonProductForwardSurgery
public import SpectreGeometry.PolygonProductRawExistence

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

/-- Explicit reversed whole-edge partners; supplied by the planar registration
bridge, rather than included in the definition of physical tiling. -/
def ReversedPlanarPartners {I : Type*} (f : I → EPlane ≃ᵢ EPlane) : Prop :=
  ∀ i e, ∃ j, j ≠ i ∧ ∃ k : Fin 14,
    f i (euclideanVertex e) = f j (euclideanVertex (next k)) ∧
    f i (euclideanVertex (next e)) = f j (euclideanVertex k)

theorem product_key_pairing_of_reversed_partners {I J : Type*}
    (f : I → EPlane ≃ᵢ EPlane) (g : J → EPlane ≃ᵢ EPlane)
    (hf : ∀ i, DirectPlacement (f i)) (hg : ∀ j, DirectPlacement (g j))
    (hfe : ReversedPlanarPartners f) (hge : ReversedPlanarPartners g) :
    Nonempty (ProductKeyPairing (fun ij : I × J => productPlacement (f ij.1) (g ij.2))) := by
  classical
  let F : I × J → EFour ≃ᵢ EFour := fun ij => productPlacement (f ij.1) (g ij.2)
  have hall (ij : I × J) (s : ProductKeySite) :
      ∃ jt : (I × J) × ProductKeySite,
        jt.1 ≠ ij ∧ s.1 = jt.2.1 ∧
        (productKeySignedAffineIsometry s).toIsometryEquiv.trans (F ij) =
          (productKeySignedAffineIsometry jt.2).toIsometryEquiv.trans (F jt.1) ∧
        productKeySign jt.2 = -productKeySign s := by
    rcases s with ⟨b,k,e⟩
    fin_cases b
    · obtain ⟨i,hi,l,ha,hb⟩ := hfe ij.1 k
      refine ⟨((i,ij.2),(0,l,!e)),?_,rfl,?_,?_⟩
      · intro he; exact hi (congrArg Prod.fst he)
      · exact product_left_key_pose (f ij.1) (f i) (g ij.2) (hf _) (hf _) k l e ha hb
      · cases e <;> norm_num [productKeySign]
    · obtain ⟨j,hj,l,ha,hb⟩ := hge ij.2 k
      refine ⟨((ij.1,j),(1,l,!e)),?_,rfl,?_,?_⟩
      · intro he; exact hj (congrArg Prod.snd he)
      · exact product_right_key_pose (g ij.2) (g j) (f ij.1) (hg _) (hg _) k l e ha hb
      · cases e <;> norm_num [productKeySign]
  choose p hd hl hp hs using hall
  exact ⟨⟨p,hd,hl,hp,hs⟩⟩

/-- Two proper planar tilings with registered reversed edges construct a
whole-space physical tiling by the literal keyed 4D body. -/
theorem physical_product_tiling_of_planar_partners {I J : Type*}
    (f : I → EPlane ≃ᵢ EPlane) (g : J → EPlane ≃ᵢ EPlane)
    (hf : ∀ i, DirectPlacement (f i)) (hg : ∀ j, DirectPlacement (g j))
    (hfc : ∀ x, ∃ i, x ∈ f i '' euclideanBody)
    (hgc : ∀ x, ∃ j, x ∈ g j '' euclideanBody)
    (hfp : Pairwise fun i j => Disjoint (interior (f i '' euclideanBody))
      (interior (f j '' euclideanBody)))
    (hgp : Pairwise fun i j => Disjoint (interior (g i '' euclideanBody))
      (interior (g j '' euclideanBody)))
    (hfe : ReversedPlanarPartners f) (hge : ReversedPlanarPartners g) :
    PolygonProductPhysicalTiling (fun ij : I × J => productPlacement (f ij.1) (g ij.2)) := by
  obtain ⟨P⟩ := product_key_pairing_of_reversed_partners f g hf hg hfe hge
  exact physical_product_tiling_of_raw_and_pairing
    ⟨product_placements_cover f g hfc hgc,product_placements_pack f g hfp hgp⟩ P

end
end SpectreGeometry
