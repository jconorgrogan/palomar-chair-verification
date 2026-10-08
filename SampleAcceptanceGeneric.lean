module
public import SparseMonotiles.ContactChairChecker
@[expose] public section
namespace SparseMonotiles.Contact.SampleAcceptanceGeneric7

/-- A checked certificate supplies full BoxKey equality on every shared facet.
This generic lemma does not assume a physical tiling or candidate classification. -/
theorem profiles_of_acceptance {d n : ℕ} {g : IndexedGeometry d n}
    (owned : ∀ j, (g.facet j).cell ∈ g.cells)
    (unique : Function.Injective g.facet)
    {p : Pose d} {mates : Fin n → Option (Fin n)}
    (checked : g.AcceptanceValid p mates) {i j : Fin n}
    (shared : Shared p (g.facet i) (g.facet j)) :
    g.profile i = (g.profile j).image (p.boxKey g.denominator) := by
  have hi := checked.2.2 i
  cases hm : mates i with
  | none =>
    have hn : (g.facet i).neighbor ∉ g.cells.image p.cell := by
      simpa only [hm, IndexedGeometry.AcceptanceAt] using hi
    exact (hn (Finset.mem_image.mpr ⟨(g.facet j).cell, owned j,
      shared_cell_neighbor shared⟩)).elim
  | some k =>
    have hk : Shared p (g.facet i) (g.facet k) ∧
        g.profile i = (g.profile k).image (p.boxKey g.denominator) := by
      simpa only [hm, IndexedGeometry.AcceptanceAt] using hi
    have hjk := unique (shared_source_unique shared hk.1)
    simpa only [hjk] using hk.2

/-- The absent-neighbor branch of a certificate cannot hide an occupied neighbor. -/
theorem mate_of_acceptance {d n : ℕ} {g : IndexedGeometry d n}
    {p : Pose d} {mates : Fin n → Option (Fin n)}
    (checked : g.AcceptanceValid p mates) {i : Fin n}
    (occupied : (g.facet i).neighbor ∈ g.cells.image p.cell) :
    ∃ j, Shared p (g.facet i) (g.facet j) ∧
      g.profile i = (g.profile j).image (p.boxKey g.denominator) := by
  have hi := checked.2.2 i
  cases hm : mates i with
  | none =>
    have hn : (g.facet i).neighbor ∉ g.cells.image p.cell := by
      simpa only [hm, IndexedGeometry.AcceptanceAt] using hi
    exact (hn occupied).elim
  | some j =>
    exact ⟨j, by simpa only [hm, IndexedGeometry.AcceptanceAt] using hi⟩

theorem key_mate_of_acceptance {d n : ℕ} {g : IndexedGeometry d n}
    {p : Pose d} {mates : Fin n → Option (Fin n)}
    (checked : g.AcceptanceValid p mates) {i : Fin n}
    (occupied : (g.facet i).neighbor ∈ g.cells.image p.cell)
    {root : BoxKey d} (hr : root ∈ g.profile i) :
    ∃ j, ∃ source ∈ g.profile j,
      Shared p (g.facet i) (g.facet j) ∧
      root = p.boxKey g.denominator source := by
  obtain ⟨j, hs, hp⟩ := mate_of_acceptance checked occupied
  rw [hp] at hr
  obtain ⟨source, hsource, he⟩ := Finset.mem_image.mp hr
  exact ⟨j, source, hsource, hs, he.symm⟩

#print axioms profiles_of_acceptance
#print axioms mate_of_acceptance
#print axioms key_mate_of_acceptance
end SparseMonotiles.Contact.SampleAcceptanceGeneric7
