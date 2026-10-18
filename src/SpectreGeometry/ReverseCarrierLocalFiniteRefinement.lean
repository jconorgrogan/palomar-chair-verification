module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section


namespace SpectreGeometry.ReverseExistence
open Set

/-- A homeomorphism transports local finiteness of a carrier family. -/
theorem homeomorph_images_locallyFinite {X Y I : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (C : I → Set X)
    (hc : LocallyFinite C) : LocallyFinite (fun i => e '' C i) := by
  simpa only [e.preimage_symm] using hc.preimage_continuous e.symm.continuous

/-- Any finite, possibly varying-size refinement of each locally finite
carrier remains locally finite as a sigma-indexed family. -/
theorem locallyFinite_sigma_refinement {X I : Type*} [TopologicalSpace X]
    {J : I → Type*} [∀ i, Finite (J i)] (C : I → Set X)
    (P : (i : I) → J i → Set X) (hc : LocallyFinite C)
    (hp : ∀ i j, P i j ⊆ C i) : LocallyFinite (fun a : Sigma J => P a.1 a.2) := by
  intro x
  obtain ⟨U,hU,hfin⟩ := hc x
  have hs : (⋃ i ∈ {i | (C i ∩ U).Nonempty},
      (Sigma.mk i '' (univ : Set (J i)))).Finite :=
    hfin.biUnion (fun i _ => (Set.finite_univ : (univ : Set (J i)).Finite).image (Sigma.mk i))
  refine ⟨U,hU,hs.subset ?_⟩
  rintro ⟨i,j⟩ ⟨y,hy,hyU⟩
  exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨y,hp i j hy,hyU⟩,⟨j,mem_univ j,rfl⟩⟩⟩

end SpectreGeometry.ReverseExistence
