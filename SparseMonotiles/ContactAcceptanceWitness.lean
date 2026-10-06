module

public import SparseMonotiles.ContactCertificateAggregateTools

@[expose] public section

/-! Sufficiency-only access to the full facet-mate witnesses carried by accepted
rows. No candidate completeness or rejection-table premise is used. -/
namespace SparseMonotiles.Contact

theorem indexedAcceptedPoses_fastCertificate {d n : ℕ} {g : IndexedGeometry d n}
    {rows : List (IndexedRow d n)} (checked : indexedValidate g rows = true)
    {p : Pose d} (hp : p ∈ indexedAcceptedPoses rows) :
    ∃ cert : MateCertificate n, g.FastAcceptanceValid p cert := by
  rcases List.mem_map.mp hp with ⟨row, hrow, he⟩
  rcases List.mem_filter.mp hrow with ⟨hrow, ha⟩
  have hv := (indexedValidate_eq_true g rows).mp checked row hrow
  cases row with
  | mk q verdict =>
    change q = p at he
    subst p
    cases verdict with
    | accepted cert => exact ⟨cert, hv⟩
    | rejected reason => simp [IndexedRow.accepted] at ha

/-- An occupied neighboring carrier cell must have an explicitly checked full
mate; the `none` branch cannot hide a missing facet. -/
theorem IndexedGeometry.mate_of_fastCertificate {d n : ℕ} {g : IndexedGeometry d n}
    (cells : g.cells = chairCells d) {p : Pose d} {cert : MateCertificate n}
    (checked : g.FastAcceptanceValid p cert) (i : Fin n)
    (occupied : (g.facet i).neighbor ∈ g.cells.image p.cell) :
    ∃ j, Shared p (g.facet i) (g.facet j) ∧
      g.profile i = (g.profile j).image (p.boxKey g.denominator) := by
  have hi := (IndexedGeometry.fastAcceptance_valid cells checked).2.2 i
  cases hm : cert.mates i with
  | none =>
    have hn : (g.facet i).neighbor ∉ g.cells.image p.cell := by
      simpa only [hm, IndexedGeometry.AcceptanceAt] using hi
    exact (hn occupied).elim
  | some j =>
    exact ⟨j, by simpa only [hm, IndexedGeometry.AcceptanceAt] using hi⟩

/-- In particular every literal root key has an actual full signature mate. -/
theorem IndexedGeometry.key_mate_of_fastCertificate {d n : ℕ} {g : IndexedGeometry d n}
    (cells : g.cells = chairCells d) {p : Pose d} {cert : MateCertificate n}
    (checked : g.FastAcceptanceValid p cert) {i : Fin n}
    (occupied : (g.facet i).neighbor ∈ g.cells.image p.cell)
    {root : BoxKey d} (hroot : root ∈ g.profile i) :
    ∃ j, ∃ source ∈ g.profile j, Shared p (g.facet i) (g.facet j) ∧
      root = p.boxKey g.denominator source := by
  obtain ⟨j, shared, profile⟩ := g.mate_of_fastCertificate cells checked i occupied
  rw [profile] at hroot
  rcases Finset.mem_image.mp hroot with ⟨source, hs, he⟩
  exact ⟨j, source, hs, shared, he.symm⟩

#print axioms indexedAcceptedPoses_fastCertificate
#print axioms IndexedGeometry.key_mate_of_fastCertificate
end SparseMonotiles.Contact
