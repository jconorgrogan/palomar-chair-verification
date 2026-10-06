module

public import SparseMonotiles.IncidentTileLocalization

@[expose] public section

/-! # Physical interior disjointness in a tile's native frame
The relative isometry remains arbitrary here. Registration is a later proved
input from whole-key recognition, not assumed by this transport lemma.
-/
namespace SparseMonotiles
open Set

theorem IsTiling.relative_copies_interior_disjoint {d : ℕ}
    {T : Set (Point d)} {tiles : Set (Set (Point d))} (ht : IsTiling T tiles)
    (g : tiles → Point d ≃ᵢ Point d)
    (hg : ∀ A : tiles, (A : Set (Point d))=g A '' T)
    (A B : tiles) (hBA : B ≠ A) :
    Disjoint (interior T) (interior (((g B).trans (g A).symm) '' T)) := by
  have hAB : (A : Set (Point d)) ≠ (B : Set (Point d)) := fun h => hBA (Subtype.ext h.symm)
  have hdis := ht.2.2 A A.property B B.property hAB
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  have hxA' : g A x ∈ interior (A : Set (Point d)) := by
    rw [hg A]
    change (g A).toHomeomorph x ∈ interior ((g A).toHomeomorph '' T)
    rw [← (g A).toHomeomorph.image_interior]
    exact ⟨x,hxA,rfl⟩
  have hBset : g A '' (((g B).trans (g A).symm) '' T)=(B : Set (Point d)) := by
    rw [hg B,Set.image_image]
    apply Set.image_congr
    intro y hy
    exact (g A).apply_symm_apply (g B y)
  have hxB' : g A x ∈ interior (B : Set (Point d)) := by
    rw [← hBset]
    change (g A).toHomeomorph x ∈ interior
      ((g A).toHomeomorph '' (((g B).trans (g A).symm) '' T))
    rw [← (g A).toHomeomorph.image_interior]
    exact ⟨x,hxB,rfl⟩
  exact Set.disjoint_left.mp hdis hxA' hxB'

#print axioms IsTiling.relative_copies_interior_disjoint
end SparseMonotiles
