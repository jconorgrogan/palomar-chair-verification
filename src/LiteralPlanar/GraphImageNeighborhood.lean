module

public import LiteralPlanar.PairedGraphNeighborhood
public import LiteralPlanar.ThirdContactExclusion

@[expose] public section


/-! Concrete graph neighborhoods survive arbitrary ambient homeomorphisms.
This supplies the chart transport for literal curved-arc neighborhoods. -/
namespace LiteralPlanar.Quintic
noncomputable section
open Set
variable {X : Type*} [TopologicalSpace X]

theorem paired_graph_image_frontiers_cover_neighborhood
    (H : (ℝ × ℝ) ≃ₜ X) (ε t : ℝ) (S T V : Set X)
    (hS : IsClosed S) (hT : IsClosed T)
    (hregS : S ⊆ closure (interior S)) (hregT : T ⊆ closure (interior T))
    (hpack : Disjoint (interior S) (interior T))
    (hV : IsOpen V) (hxV : H (t,height ε t) ∈ V)
    (hxS : H (t,height ε t) ∈ S) (hxT : H (t,height ε t) ∈ T)
    (hfrontS : frontier S ∩ V = H '' wholeGraph ε ∩ V)
    (hfrontT : frontier T ∩ V = H '' wholeGraph ε ∩ V) :
    ∃ U : Set X, IsOpen U ∧ H (t,height ε t) ∈ U ∧ U ⊆ S ∪ T := by
  have image_inv (A : Set (ℝ × ℝ)) : H.symm '' (H '' A) = A := by
    rw [Set.image_image]
    simp only [Homeomorph.symm_apply_apply,Set.image_id,Set.image_id']
  have reg (A : Set X) (hA : A ⊆ closure (interior A)) :
      H.symm '' A ⊆ closure (interior (H.symm '' A)) := by
    rw [←H.symm.image_interior,←H.symm.image_closure]
    exact Set.image_mono hA
  have hlocal (A : Set X) (hA : frontier A ∩ V = H '' wholeGraph ε ∩ V) :
      frontier (H.symm '' A) ∩ H.symm '' V = wholeGraph ε ∩ H.symm '' V := by
    rw [←H.symm.image_frontier,←Set.image_inter H.symm.injective,hA,
      Set.image_inter H.symm.injective,image_inv]
  have pack : Disjoint (interior (H.symm '' S)) (interior (H.symm '' T)) := by
    rw [←H.symm.image_interior,←H.symm.image_interior]
    exact Set.disjoint_image_of_injective H.symm.injective hpack
  have mem (A : Set X) (hxA : H (t,height ε t) ∈ A) :
      (t,height ε t) ∈ H.symm '' A :=
    ⟨H (t,height ε t),hxA,H.symm_apply_apply _⟩
  obtain ⟨U,hU,hxU,hcover⟩ := paired_graph_frontiers_cover_neighborhood ε t
    (H.symm '' S) (H.symm '' T) (H.symm '' V)
    (H.symm.isClosedMap _ hS) (H.symm.isClosedMap _ hT)
    (reg S hregS) (reg T hregT) pack (H.symm.isOpenMap _ hV)
    (mem V hxV) (mem S hxS) (mem T hxT) (hlocal S hfrontS) (hlocal T hfrontT)
  refine ⟨H '' U,H.isOpenMap _ hU,⟨_,hxU,rfl⟩,?_⟩
  rintro x ⟨y,hy,rfl⟩
  rcases hcover hy with hs | ht
  · obtain ⟨z,hz,rfl⟩ := hs
    left
    simpa only [Homeomorph.apply_symm_apply] using hz
  · obtain ⟨z,hz,rfl⟩ := ht
    right
    simpa only [Homeomorph.apply_symm_apply] using hz

end
end LiteralPlanar.Quintic
