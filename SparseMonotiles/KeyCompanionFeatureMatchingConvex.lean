module

public import SparseMonotiles.KeySideFacePatchTransport
public import SparseMonotiles.ConeExclusion

@[expose] public section

/-! # Closed side coverage determines the whole convex key solid
Every base point lies between points of two opposite side faces. Thus a convex
set containing all closed sides also contains the entire pyramid solid.
-/
namespace SparseMonotiles
open Set

theorem keySolid_subset_convex_of_closed_sides {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (i : Fin n) {L : Set (Point (n+1))} (hL : Convex ℝ L)
    (hside : ∀ j b, keySideClosedFace k j b ⊆ L) : keySolid k ⊆ L := by
  apply convexHull_min _ hL
  rintro x (hxa | hxb)
  · subst x
    exact hside i false ⟨subset_convexHull ℝ _ (Set.mem_insert _ _),key_apex_side_slack_zero k i false⟩
  · let e := pointPyramidEquiv n
    let z := e x
    let u : PyramidPoint n := (Function.update z.1 i (keyPyramidLo k i),z.2)
    let v : PyramidPoint n := (Function.update z.1 i (keyPyramidHi k i),z.2)
    have hbase : z ∈ pyramidBase (keyPyramidLo k) (keyPyramidHi k) :=
      (mem_keyBase_iff_pyramidBase k hc hr x).mp hxb
    have hwidth : keyPyramidLo k i ≤ keyPyramidHi k i := (hbase.2 i).1.trans (hbase.2 i).2
    have hu : e.symm u ∈ keyBase k := by
      apply (mem_keyBase_iff_pyramidBase k hc hr _).mpr
      change e (e.symm u) ∈ pyramidBase _ _
      rw [e.apply_symm_apply]
      refine ⟨hbase.1,?_⟩
      intro j
      by_cases hji : j=i
      · subst j; simpa [u] using And.intro (le_refl (keyPyramidLo k i)) hwidth
      · simpa [u,Function.update_of_ne hji] using hbase.2 j
    have hv : e.symm v ∈ keyBase k := by
      apply (mem_keyBase_iff_pyramidBase k hc hr _).mpr
      change e (e.symm v) ∈ pyramidBase _ _
      rw [e.apply_symm_apply]
      refine ⟨hbase.1,?_⟩
      intro j
      by_cases hji : j=i
      · subst j; simpa [v] using And.intro hwidth (le_refl (keyPyramidHi k i))
      · simpa [v,Function.update_of_ne hji] using hbase.2 j
    have huside : keyPyramidHalfspaceSlack k (.inr (i,false)) (e.symm u)=0 := by
      have hlast : e.symm u (Fin.last n)=0 := by
        have h := congrArg Prod.snd (e.apply_symm_apply u)
        change e.symm u (Fin.last n)=z.2 at h
        exact h.trans hbase.1
      have hi : e.symm u i.castSucc=keyPyramidLo k i := by
        have h := congrArg (fun p : PyramidPoint n => p.1 i) (e.apply_symm_apply u)
        change e.symm u i.castSucc=u.1 i at h
        simpa only [u,Function.update_self] using h
      simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
        keyPyramidHalfspaceNormal_apply,hi,hlast]
    have hvside : keyPyramidHalfspaceSlack k (.inr (i,true)) (e.symm v)=0 := by
      have hlast : e.symm v (Fin.last n)=0 := by
        have h := congrArg Prod.snd (e.apply_symm_apply v)
        change e.symm v (Fin.last n)=z.2 at h
        exact h.trans hbase.1
      have hi : e.symm v i.castSucc=keyPyramidHi k i := by
        have h := congrArg (fun p : PyramidPoint n => p.1 i) (e.apply_symm_apply v)
        change e.symm v i.castSucc=v.1 i at h
        simpa only [v,Function.update_self] using h
      simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
        keyPyramidHalfspaceNormal_apply,hi,hlast]
    have hulo : e.symm u ∈ L := hside i false
      ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hu),huside⟩
    have hvhi : e.symm v ∈ L := hside i true
      ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _ hv),hvside⟩
    have hsegment : z ∈ segment ℝ u v := mem_segment_coordinate_update z i (hbase.2 i).1 (hbase.2 i).2
    have himage : e.symm '' segment ℝ u v = segment ℝ (e.symm u) (e.symm v) :=
      image_segment ℝ e.symm.toLinearMap.toAffineMap u v
    apply hL.segment_subset hulo hvhi
    rw [← himage]
    exact ⟨z,hsegment,e.symm_apply_apply x⟩

theorem posed_keySolid_subset_convex_of_closed_sides {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (i : Fin n) (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1))
    {L : Set (Point (n+1))} (hL : Convex ℝ L)
    (hside : ∀ j b, W '' keySideClosedFace k j b ⊆ L) : W '' keySolid k ⊆ L := by
  have hpre : keySolid k ⊆ W ⁻¹' L := keySolid_subset_convex_of_closed_sides k hc hr i
    (hL.affine_preimage W.toAffineEquiv.toAffineMap) (fun j b x hx => hside j b ⟨x,hx,rfl⟩)
  rintro x ⟨y,hy,rfl⟩
  exact hpre hy

#print axioms keySolid_subset_convex_of_closed_sides
#print axioms posed_keySolid_subset_convex_of_closed_sides
end SparseMonotiles
