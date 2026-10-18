module

public import SparseMonotiles.CoarseContactCertificates5Symmetry
public import SparseMonotiles.CarrierHierarchyCoarseSymmetry

@[expose] public section

/-!
The full canonical source generator reduces to the checked ordered-child-pair
orbits by simultaneous coordinate conjugation. Every original source triple is
covered symbolically; the representative arithmetic checks do not stand in for
an unproved claim that omitted triples are redundant. This is not a body gauge.
-/
namespace SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
open Contact CoarseContactCertificates5

 theorem language_iff (s : Fin 4) (p : Pose 5) :
    conjugatePose (symmetry s) p ∈ L ↔ p ∈ L := by
  apply conjugate_membership_iff (symmetry s) L
  · exact registry_closed s
  · have h : ∀ q ∈ L, conjugatePose (symmetry (inverseIndex s)) q ∈ L :=
      registry_closed (inverseIndex s)
    simpa only [symmetry_inverse] using h

def expandedRows {ρ : Type} (rows : ρ → CoarseRow 5) (a : ρ × Fin 4) : CoarseRow 5 :=
  (rows a.1).conjugate (symmetry a.2)

theorem expandedRows_valid {ρ : Type} (rows : ρ → CoarseRow 5)
    (valid : ∀ i, (rows i).witness.Valid C L (rows i).pose) (a : ρ × Fin 4) :
    (expandedRows rows a).witness.Valid C L (expandedRows rows a).pose := by
  rcases a with ⟨i, s⟩
  exact CoarseWitness.conjugate_valid (symmetry s) C L (child_closed s) (language_iff s) (valid i)

/-- The exhaustive 32×32 source pair domain is reduced by the kernel-checked
index orbit table, and legal contact conjugation is independently justified. -/
theorem expandedRows_complete {ρ : Type} (rows : ρ → CoarseRow 5)
    (covered : ∀ a : Fin 280, ∀ k : Fin 284,
      (∀ i, (parentCandidate (child (representativePair a).1)
        (child (representativePair a).2) (registry k)).shift i % 2 = 0) →
      ∃ r, parentCandidate (child (representativePair a).1)
        (child (representativePair a).2) (registry k) = (rows r).pose)
    (a : Pose 5) (ha : a ∈ C) (b : Pose 5) (hb : b ∈ C) (k : Pose 5) (hk : k ∈ L)
    (heven : ∀ i, (parentCandidate a b k).shift i % 2 = 0) :
    ∃ r, parentCandidate a b k = (expandedRows rows r).pose := by
  obtain ⟨i, rfl⟩ := child_indexed ha
  obtain ⟨j, rfl⟩ := child_indexed hb
  let s := (pairReduction i j).1
  let rep := (pairReduction i j).2
  have hpair := pair_reduction i j
  have hai : conjugatePose (symmetry s) (child i) = child (representativePair rep).1 := by
    have h : conjugatePose (symmetry s) (child i) = child (childAction s i) := child_action s i
    exact h.trans (congrArg child hpair.1)
  have hbj : conjugatePose (symmetry s) (child j) = child (representativePair rep).2 := by
    have h : conjugatePose (symmetry s) (child j) = child (childAction s j) := child_action s j
    exact h.trans (congrArg child hpair.2)
  have hk' : conjugatePose (symmetry s) k ∈ L := registry_closed s k hk
  obtain ⟨l, hl⟩ := registry_complete hk'
  have hconj : conjugatePose (symmetry s) (parentCandidate (child i) (child j) k) =
      parentCandidate (child (representativePair rep).1)
        (child (representativePair rep).2) (registry l) := by
    rw [conjugatePose_candidate, hai, hbj, ← hl]
  have hEven := (conjugatePose_even_iff (symmetry s) (parentCandidate (child i) (child j) k)).mpr heven
  rw [hconj] at hEven
  obtain ⟨r, hr⟩ := covered rep l hEven
  refine ⟨(r, inverseIndex s), ?_⟩
  change parentCandidate (child i) (child j) k =
    conjugatePose (symmetry (inverseIndex s)) (rows r).pose
  rw [symmetry_inverse]
  calc
    parentCandidate (child i) (child j) k =
        conjugatePose (symmetry s).symm
          (conjugatePose (symmetry s) (parentCandidate (child i) (child j) k)) :=
      (conjugatePose_symm_cancel (symmetry s) _).symm
    _ = conjugatePose (symmetry s).symm (rows r).pose := by rw [hconj, hr]

#print axioms language_iff
#print axioms expandedRows_valid
#print axioms expandedRows_complete
end SparseMonotiles.CarrierHierarchy.CoarseContactCertificates5Symmetry
