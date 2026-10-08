module

public import SparseMonotiles.PrescribedContactProfilesSymmetry
public import SparseMonotiles.CarrierHierarchyPartition

@[expose] public section

/-! Exact pose inversion exchanges the two copies in a contact.  No
coordinate-permutation/body-symmetry assumption is used.  Carrier cells,
opposed oriented facets, and all literal profile vertices remain explicit. -/
namespace SparseMonotiles.ContactInverseReuse
open Contact CarrierHierarchy

@[simp] theorem inversePose_inversePose {d : ℕ} (p : Pose d) :
    inversePose (inversePose p) = p := by
  apply compose_left_injective (inversePose p)
  rw [compose_inversePose, inversePose_compose]

@[simp] theorem inversePose_scaledPoint_scaledPoint {d : ℕ} (p : Pose d)
    (den : ℤ) (x : ScaledPoint d) :
    (inversePose p).scaledPoint den (p.scaledPoint den x) = x := by
  funext i
  simp only [Pose.scaledPoint, inversePose, Equiv.apply_symm_apply]
  cases h : p.negative (p.perm.symm i) <;>
    simp [Pose.sign, h]

/-- Both the vertex transform and the bump/dent reversal cancel exactly. -/
@[simp] theorem inversePose_key_key {d : ℕ} (p : Pose d)
    (den : ℤ) (k : VertexKey d) :
    (inversePose p).key den (p.key den k) = k := by
  cases k with
  | mk vertices bump =>
    simp [Pose.key, Finset.image_image, Function.comp_def]

/-- Carrier disjointness reverses using the exact signed lower-cell action. -/
theorem disjoint_inversePose {d : ℕ} (p : Pose d) (cells : Finset (Cell d))
    (h : Disjoint cells (cells.image p.cell)) :
    Disjoint cells (cells.image (inversePose p).cell) := by
  apply Finset.disjoint_left.mpr
  intro c hc him
  rcases Finset.mem_image.mp him with ⟨a, ha, hac⟩
  apply Finset.disjoint_left.mp h ha
  apply Finset.mem_image.mpr
  refine ⟨c, hc, ?_⟩
  rw [← hac, inversePose_cell, Pose.cell_inverseCell]

/-- Every clause of indexed literal contact is preserved by swapping the
copies and inverting the full pose.  No body automorphism is required. -/
theorem legalContact_inversePose {d n : ℕ} {g : IndexedGeometry d n}
    {p : Pose d} (h : g.LegalContact p) : g.LegalContact (inversePose p) := by
  rcases h with ⟨hd, he, hm⟩
  refine ⟨disjoint_inversePose p g.cells hd, ?_, ?_⟩
  · obtain ⟨i, j, hs⟩ := he
    exact ⟨j, i, shared_inversePose hs⟩
  · intro i j hs
    have hs' : Shared p (g.facet j) (g.facet i) := by
      simpa only [inversePose_inversePose] using shared_inversePose hs
    have hk := congrArg (Finset.image ((inversePose p).key g.denominator)) (hm j i hs')
    simpa only [Finset.image_image, Function.comp_def, inversePose_key_key, Finset.image_id] using hk.symm

theorem legalContact_inversePose_iff {d n : ℕ} (g : IndexedGeometry d n)
    (p : Pose d) : g.LegalContact p ↔ g.LegalContact (inversePose p) := by
  constructor
  · exact legalContact_inversePose
  · intro h
    simpa only [inversePose_inversePose] using legalContact_inversePose h

/-- A full-pose inversion certificate safely reuses any proved rejection. -/
theorem reject_of_eq_inversePose {d n : ℕ} {g : IndexedGeometry d n}
    {p q : Pose d} (he : p = inversePose q) (hq : ¬g.LegalContact q) :
    ¬g.LegalContact p := by
  subst p
  exact fun hp => hq ((legalContact_inversePose_iff g q).mpr hp)

/-- Transfer a classification implication from a representative, provided the
exact target catalog is itself closed under inversion. -/
theorem classify_of_eq_inversePose {d n : ℕ} {g : IndexedGeometry d n}
    {catalog : Set (Pose d)}
    (closed : ∀ q ∈ catalog, inversePose q ∈ catalog)
    {p q : Pose d} (he : p = inversePose q)
    (hq : g.LegalContact q → q ∈ catalog) :
    g.LegalContact p → p ∈ catalog := by
  subst p
  intro hp
  exact closed q (hq ((legalContact_inversePose_iff g q).mpr hp))

#print axioms inversePose_inversePose
#print axioms inversePose_scaledPoint_scaledPoint
#print axioms inversePose_key_key
#print axioms disjoint_inversePose
#print axioms legalContact_inversePose_iff
#print axioms reject_of_eq_inversePose
#print axioms classify_of_eq_inversePose
end SparseMonotiles.ContactInverseReuse
