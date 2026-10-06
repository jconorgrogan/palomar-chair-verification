module

public import SparseMonotiles.GenericRidgePoints

@[expose] public section

/-! # Extract actual supporting planes from finite local boundary covers
A nonempty relatively open affine patch cannot be covered by proper
restrictions of finitely (or countably) many affine planes.
-/
namespace SparseMonotiles
open Set

section AffineCover
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem affine_patch_cover_contains_plane {κ : Type*} [Countable κ]
    (P : AffineSubspace ℝ E) {O : Set P} (hO : IsOpen O) (hne : O.Nonempty)
    (H : κ → AffineSubspace ℝ E) (hcover : ∀ x ∈ O, ∃ a, (x : E) ∈ H a) :
    ∃ a, P ≤ H a := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨x,hx,hgeneric⟩ := exists_genericRidgePoint_in_open P ⟨p,p.property⟩ H hO ⟨p,hp⟩
  obtain ⟨a,ha⟩ := hcover x hx
  exact ⟨a,hgeneric a ha⟩

theorem affine_hyperplane_eq_of_le_proper
    (P H : AffineSubspace ℝ E) (hne : (P : Set E).Nonempty)
    (hdim : Module.finrank ℝ P.direction+1=Module.finrank ℝ E)
    (hH : H ≠ ⊤) (hle : P ≤ H) : P=H := by
  classical
  have hdir : P.direction ≤ H.direction := AffineSubspace.direction_le hle
  by_contra hnequal
  have hlt : P.direction < H.direction := lt_of_le_of_ne hdir (fun h =>
    hnequal (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le h hne hle))
  have hrank := Submodule.finrank_lt_finrank_of_lt hlt
  have hlefin := H.direction.finrank_le
  have htop : H.direction=⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  exact hH ((AffineSubspace.direction_eq_top_iff_of_nonempty (hne.mono hle)).mp htop)

/-- Retain every actual matched plane, with injectivity derived from distinct
root planes. No facet labels or face-to-face correspondence are assumed. -/
theorem finite_hyperplane_patch_cover_injection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → AffineSubspace ℝ E) (hP : Function.Injective P)
    (O : ∀ i, Set (P i)) (hO : ∀ i, IsOpen (O i)) (hne : ∀ i, (O i).Nonempty)
    (hdim : ∀ i, Module.finrank ℝ (P i).direction+1=Module.finrank ℝ E)
    (H : κ → AffineSubspace ℝ E) (hH : ∀ a, H a ≠ ⊤)
    (hcover : ∀ i x, x ∈ O i → ∃ a, (x : E) ∈ H a) :
    ∃ σ : ι → κ, Function.Injective σ ∧ ∀ i, P i=H (σ i) := by
  classical
  choose σ hσ using (fun i => affine_patch_cover_contains_plane (P i) (hO i) (hne i) H (hcover i))
  have heq : ∀ i, P i=H (σ i) := by
    intro i
    obtain ⟨x,hx⟩ := hne i
    exact affine_hyperplane_eq_of_le_proper (P i) (H (σ i)) ⟨x,x.property⟩ (hdim i) (hH _) (hσ i)
  refine ⟨σ,?_,heq⟩
  intro i j hij
  apply hP
  rw [heq i,heq j,hij]

theorem finite_hyperplane_patch_cover_card_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → AffineSubspace ℝ E) (hP : Function.Injective P)
    (O : ∀ i, Set (P i)) (hO : ∀ i, IsOpen (O i)) (hne : ∀ i, (O i).Nonempty)
    (hdim : ∀ i, Module.finrank ℝ (P i).direction+1=Module.finrank ℝ E)
    (H : κ → AffineSubspace ℝ E) (hH : ∀ a, H a ≠ ⊤)
    (hcover : ∀ i x, x ∈ O i → ∃ a, (x : E) ∈ H a) :
    Fintype.card ι ≤ Fintype.card κ := by
  obtain ⟨σ,hσ,_⟩ := finite_hyperplane_patch_cover_injection P hP O hO hne hdim H hH hcover
  exact Fintype.card_le_of_injective σ hσ

end AffineCover
#print axioms affine_patch_cover_contains_plane
#print axioms finite_hyperplane_patch_cover_injection
#print axioms finite_hyperplane_patch_cover_card_le
end SparseMonotiles
