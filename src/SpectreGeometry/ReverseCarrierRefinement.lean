module

public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section


namespace SpectreGeometry.ReverseExistence
open Set

/-- Refining each member of a covering family gives a covering sigma-family. -/
theorem carrier_refinement_covers {X I : Type*} {J : I → Type*}
    (C : I → Set X) (P : (i : I) → J i → Set X)
    (hc : ∀ x, ∃ i, x ∈ C i) (hp : ∀ i, C i = ⋃ j, P i j) :
    ∀ x, ∃ a : Sigma J, x ∈ P a.1 a.2 := by
  intro x
  obtain ⟨i,hi⟩ := hc x
  rw [hp i] at hi
  obtain ⟨j,hj⟩ := mem_iUnion.mp hi
  exact ⟨⟨i,j⟩,hj⟩

/-- Disjoint cluster interiors and disjoint within-cluster piece interiors
imply disjoint interiors of the complete sigma-indexed piece family. -/
theorem carrier_refinement_interiors_disjoint {X I : Type*} [TopologicalSpace X]
    {J : I → Type*} (C : I → Set X) (P : (i : I) → J i → Set X)
    (hc : Pairwise (fun i k => Disjoint (interior (C i)) (interior (C k))))
    (hp : ∀ i j, P i j ⊆ C i)
    (hd : ∀ i, Pairwise (fun j k => Disjoint (interior (P i j)) (interior (P i k)))) :
    Pairwise (fun a b : Sigma J =>
      Disjoint (interior (P a.1 a.2)) (interior (P b.1 b.2))) := by
  rintro ⟨i,j⟩ ⟨k,l⟩ hab
  by_cases hik : i = k
  · subst k
    apply hd i
    intro hjl
    apply hab
    cases hjl
    rfl
  · exact (hc hik).mono (interior_mono (hp i j)) (interior_mono (hp k l))

/-- Homeomorphisms transport ordinary ambient interior disjointness. -/
theorem homeomorph_images_interiors_disjoint {X Y I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (C : I → Set X)
    (hc : Pairwise (fun i j => Disjoint (interior (C i)) (interior (C j)))) :
    Pairwise (fun i j => Disjoint (interior (e '' C i)) (interior (e '' C j))) := by
  intro i j hij
  rw [←e.image_interior,←e.image_interior]
  exact Set.disjoint_image_of_injective e.injective (hc hij)

end SpectreGeometry.ReverseExistence
