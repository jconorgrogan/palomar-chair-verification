module

public import SparseMonotiles.Model
public import Mathlib.Data.Set.Image

set_option autoImplicit false
@[expose] public section

/-! Uncompiled draft. Generic conversion between indexed physical placements
and the existing unmarked `SparseMonotiles` model. No geometric recognition,
frame-equivariance, or nonempty-interior premise is added by these bridges. -/
namespace FinalAssemblyDraft
noncomputable section
open Set SparseMonotiles
universe u

/-- An indexed physical tiling gives an unmarked collection of its image sets. -/
theorem indexed_tiling_hasTiling {d : ℕ} {I : Type u}
    (T : Set (Point d)) (p : I → Point d ≃ᵢ Point d)
    (hcover : ∀ x, ∃ i, x ∈ p i '' T)
    (hpack : Pairwise fun i j =>
      Disjoint (interior (p i '' T)) (interior (p j '' T))) :
    HasTiling T := by
  refine ⟨Set.range (fun i => p i '' T), ?_, ?_, ?_⟩
  · rintro A ⟨i, rfl⟩
    exact ⟨p i, rfl⟩
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨p i '' T, ⟨i, rfl⟩, hi⟩
  · rintro A ⟨i, rfl⟩ B ⟨j, rfl⟩ hne
    have hij : i ≠ j := by
      intro h
      exact hne (h ▸ rfl)
    exact hpack hij

/-- Translation by the negative vector supplies predecessors of every set. -/
private theorem translate_inverse_cancel {d : ℕ}
    (v : Point d) (A : Set (Point d)) :
    SparseMonotiles.translate v (SparseMonotiles.translate (-v) A) = A := by
  simp only [SparseMonotiles.translate, Set.image_image]
  have hf : (fun x : Point d => (x + -v) + v) = id := by
    funext x
    simp
  rw [hf, Set.image_id]

/-- Carrier-range rigidity at index universe zero already covers every
unmarked collection, by indexing it by its subtype and choosing placements. -/
theorem indexed_period_rigidity_isAperiodic {d : ℕ} (T : Set (Point d))
    (H : ∀ (I : Type) (p : I → Point d ≃ᵢ Point d),
      (∀ x, ∃ i, x ∈ p i '' T) →
      (Pairwise fun i j =>
        Disjoint (interior (p i '' T)) (interior (p j '' T))) →
      ∀ v : Point d,
        (Set.range (fun i => (fun x : Point d => x + v) '' (p i '' T)) =
          Set.range (fun i => p i '' T)) → v = 0) :
    IsAperiodic T := by
  classical
  intro tiles ht v hv
  let g : tiles → Point d ≃ᵢ Point d :=
    fun A => Classical.choose (ht.1 A A.property)
  have hg : ∀ A : tiles, (A : Set (Point d)) = g A '' T :=
    fun A => Classical.choose_spec (ht.1 A A.property)
  have hcover : ∀ x, ∃ A : tiles, x ∈ g A '' T := by
    intro x
    obtain ⟨A, hA, hx⟩ := ht.2.1 x
    refine ⟨⟨A, hA⟩, ?_⟩
    have he := hg ⟨A, hA⟩
    change A = g ⟨A, hA⟩ '' T at he
    rwa [← he]
  have hpack : Pairwise fun A B : tiles =>
      Disjoint (interior (g A '' T)) (interior (g B '' T)) := by
    intro A B hne
    have hAB : (A : Set (Point d)) ≠ (B : Set (Point d)) :=
      fun h => hne (Subtype.ext h)
    simpa only [hg A, hg B] using ht.2.2 A A.property B B.property hAB
  have hrange : Set.range (fun A : tiles => g A '' T) = tiles := by
    ext A
    constructor
    · rintro ⟨B, rfl⟩
      change g B '' T ∈ tiles
      rw [← hg B]
      exact B.property
    · intro hA
      exact ⟨⟨A, hA⟩, (hg ⟨A, hA⟩).symm⟩
  have htranslated :
      Set.range (fun A : tiles =>
        (fun x : Point d => x + v) '' (g A '' T)) = tiles := by
    ext A
    constructor
    · rintro ⟨B, rfl⟩
      change SparseMonotiles.translate v (g B '' T) ∈ tiles
      apply (hv (g B '' T)).mp
      rw [← hg B]
      exact B.property
    · intro hA
      let B : Set (Point d) := SparseMonotiles.translate (-v) A
      have hback : SparseMonotiles.translate v B = A :=
        translate_inverse_cancel v A
      have hB : B ∈ tiles := by
        apply (hv B).mpr
        rw [hback]
        exact hA
      refine ⟨⟨B, hB⟩, ?_⟩
      change SparseMonotiles.translate v (g ⟨B, hB⟩ '' T) = A
      rw [← hg ⟨B, hB⟩]
      exact hback
  exact H tiles g hcover hpack v (htranslated.trans hrange.symm)

/-- Compactness, actual indexed existence, and universal indexed carrier
rigidity package into the existing unmarked monotile predicate. -/
theorem isAperiodicMonotile_of_indexed {d : ℕ} (T : Set (Point d))
    (hcompact : IsCompact T)
    (hexists : ∃ (I : Type) (p : I → Point d ≃ᵢ Point d),
      (∀ x, ∃ i, x ∈ p i '' T) ∧
      Pairwise fun i j =>
        Disjoint (interior (p i '' T)) (interior (p j '' T)))
    (H : ∀ (I : Type) (p : I → Point d ≃ᵢ Point d),
      (∀ x, ∃ i, x ∈ p i '' T) →
      (Pairwise fun i j =>
        Disjoint (interior (p i '' T)) (interior (p j '' T))) →
      ∀ v : Point d,
        (Set.range (fun i => (fun x : Point d => x + v) '' (p i '' T)) =
          Set.range (fun i => p i '' T)) → v = 0) :
    IsAperiodicMonotile T := by
  obtain ⟨I, p, hcover, hpack⟩ := hexists
  exact ⟨hcompact, indexed_tiling_hasTiling T p hcover hpack,
    indexed_period_rigidity_isAperiodic T H⟩

end
end FinalAssemblyDraft
