module

public import SpectreGeometry.PolygonProductKeyDenseCompanions
public import SpectreGeometry.PolygonProductCreasePose

@[expose] public section


namespace SpectreGeometry.ProductCrease
open Set ProductKeyReference
noncomputable section

/-- Physical whole-crease containment reverses: a third key would violate
three-key exclusion, and a different key on the original tile violates
its disjoint collars. -/
theorem physical_crease_companion_eq {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (root j : ι) (u v : ProductKeySite)
    (hjr : j ≠ root) (hsub : f root '' creaseComplex u ⊆ f j '' creaseComplex v) :
    f root '' creaseComplex u = f j '' creaseComplex v := by
  obtain ⟨⟨k,w⟩,⟨hkj,hnext⟩,_⟩ := physical_whole_crease_companion T j v
  obtain ⟨z,hz⟩ := (creaseComplex_isConnected u).nonempty
  have hx : f root z ∈ f root '' creaseComplex u := ⟨z,hz,rfl⟩
  have hjx := hsub hx
  have hkx := hnext hjx
  have hkr : k = root := by
    by_contra hne
    exact no_three_distinct_key_incidents f T.interiors_disjoint root j k
      (Ne.symm hjr) (Ne.symm hne) (Ne.symm hkj) u v w (f root z)
      (image_mono (creaseComplex_subset_graphWindow u) hx)
      (image_mono (creaseComplex_subset_graphWindow v) hjx)
      (image_mono (creaseComplex_subset_graphWindow w) hkx)
  subst k
  have hwu : w = u := by
    by_contra hne
    obtain ⟨z',hz',he⟩ := hkx
    have hez : z' = z := (f root).injective he
    subst z'
    exact Set.disjoint_left.mp (creaseComplex_pairwise_disjoint hne) hz' hz
  subst w
  exact Subset.antisymm hsub hnext

/-- Every actual key in every physical tiling has a unique coincident whole
key in another tile, fixing its absolute label and full signed pose. -/
theorem physical_key_pose_registration {ι : Type*} {f : ι → EFour ≃ᵢ EFour}
    (T : PolygonProductPhysicalTiling f) (root : ι) (u : ProductKeySite) :
    ∃ j : ι, ∃ v : ProductKeySite, j ≠ root ∧ u.1 = v.1 ∧
      (productKeySignedAffineIsometry u).toIsometryEquiv.trans (f root) =
      (productKeySignedAffineIsometry v).toIsometryEquiv.trans (f j) := by
  obtain ⟨⟨j,v⟩,⟨hjr,hsub⟩,_⟩ := physical_whole_crease_companion T root u
  obtain ⟨hlabel,hpose⟩ := coincident_actualCreases u v (f root) (f j)
    (physical_crease_companion_eq T root j u v hjr hsub)
  exact ⟨j,v,hjr,hlabel,hpose⟩

end
end SpectreGeometry.ProductCrease
