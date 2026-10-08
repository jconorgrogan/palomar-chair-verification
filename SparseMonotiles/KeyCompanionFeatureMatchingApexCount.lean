module

public import SparseMonotiles.KeyCompanionFeatureMatchingApexPatches
public import SparseMonotiles.LocalBoundaryPlanes

@[expose] public section

/-! # The companion cannot have a non-apex boundary germ at the root apex
Actual closed side coverage supplies more distinct planes than any carrier
or non-apex key boundary germ can carry in the ambient dimension.
-/
namespace SparseMonotiles
open Set Filter
open scoped Topology

theorem key_apex_not_small_local_boundary_cover {n : ℕ} (hn : n+1 < 2*n)
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ i b, 0 < keySideDistance k i b)
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (T : Set (Point (n+1)))
    (hside : ∀ i b, W '' keySideClosedFace k i b ⊆ frontier T) :
    ¬ HasLocalBoundaryPlaneCover T (W (rationalPoint k.apex)) (n+1) := by
  classical
  rintro ⟨planes,hcard,hplanes,hcover⟩
  obtain ⟨U,hUc,hU,hp⟩ := mem_nhds_iff.mp hcover
  let I := {P : AffineSubspace ℝ (Point (n+1)) // P ∈ planes}
  letI : Fintype I := (planes.finite_toSet).fintype
  have hbound := key_apex_local_boundary_plane_card_bound k hc hr hh hd W (frontier T) hside hU hp
    (fun P : I => P.val) (fun P => (hplanes P.val P.property).2.2) (by
      intro x hx hf
      obtain ⟨P,hP,hxP⟩ := hUc hx hf
      exact ⟨⟨P,hP⟩,hxP⟩)
  have hI : Fintype.card I=planes.card := by simp [I]
  rw [hI] at hbound
  omega

theorem isometry_symm_mem_frontier_image {d : ℕ} (g : Point d ≃ᵢ Point d)
    (T : Set (Point d)) {x : Point d} (hx : x ∈ frontier (g '' T)) :
    g.symm x ∈ frontier T := by
  have hx' : x ∈ g.toHomeomorph '' frontier T := by
    rw [g.toHomeomorph.image_frontier]
    exact hx
  obtain ⟨y,hy,hey⟩ := hx'
  rw [← hey]
  change g.symm (g y) ∈ frontier T
  rw [g.symm_apply_apply]
  exact hy

/-- Pull a physical boundary-side cover into the companion's native frame. -/
theorem key_closed_sides_pullback_frontier {n : ℕ} (k : KeyData (n+1))
    (W : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (g : Point (n+1) ≃ᵢ Point (n+1))
    (T : Set (Point (n+1)))
    (hside : ∀ i b, W '' keySideClosedFace k i b ⊆ frontier (g '' T)) :
    ∀ i b, (W.trans g.symm.toRealAffineIsometryEquiv) '' keySideClosedFace k i b ⊆ frontier T := by
  intro i b x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact isometry_symm_mem_frontier_image g T (hside i b ⟨y,hy,rfl⟩)

#print axioms key_apex_not_small_local_boundary_cover
#print axioms key_closed_sides_pullback_frontier
end SparseMonotiles
