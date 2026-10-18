module

public import Mathlib.Topology.Closure
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod

@[expose] public section


namespace SpectreGeometry.ReverseExistence
open Set

/-- A finite union of closed sets with empty interior still has empty interior. -/
theorem finite_closed_biUnion_interior_empty {X ι : Type*} [TopologicalSpace X]
    (s : Finset ι) (C : ι → Set X)
    (hc : ∀ i ∈ s, IsClosed (C i)) (he : ∀ i ∈ s, interior (C i) = ∅) :
    interior (⋃ i ∈ s, C i) = ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have ht : interior (⋃ j ∈ s, C j) = ∅ :=
      ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))
        (fun j hj => he j (Finset.mem_insert_of_mem hj))
    have hu : (⋃ j ∈ insert i s, C j) = C i ∪ (⋃ j ∈ s, C j) := by
      ext x
      simp
    rw [hu,interior_union_isClosed_of_interior_empty (hc i (Finset.mem_insert_self _ _)) ht]
    exact he i (Finset.mem_insert_self _ _)

theorem finite_closed_iUnion_interior_empty {X ι : Type*} [TopologicalSpace X] [Finite ι]
    (C : ι → Set X) (hc : ∀ i, IsClosed (C i)) (he : ∀ i, interior (C i) = ∅) :
    interior (⋃ i, C i) = ∅ := by
  classical
  letI := Fintype.ofFinite ι
  simpa using finite_closed_biUnion_interior_empty Finset.univ C
    (fun i _ => hc i) (fun i _ => he i)

/-- Cross-family interior disjointness survives taking finite closed unions. -/
theorem finite_closed_iUnion_interiors_disjoint {X ι κ : Type*}
    [TopologicalSpace X] [Finite ι] [Finite κ]
    (C : ι → Set X) (D : κ → Set X)
    (hc : ∀ i, IsClosed (C i)) (hd : ∀ j, IsClosed (D j))
    (h : ∀ i j, Disjoint (interior (C i)) (interior (D j))) :
    Disjoint (interior (⋃ i, C i)) (interior (⋃ j, D j)) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  have hz : interior (⋃ p : ι × κ, C p.1 ∩ D p.2) = ∅ := by
    apply finite_closed_iUnion_interior_empty
    · intro p
      exact (hc p.1).inter (hd p.2)
    · intro p
      rw [interior_inter]
      exact Set.disjoint_iff_inter_eq_empty.mp (h p.1 p.2)
  have hu : (⋃ i, C i) ∩ (⋃ j, D j) = ⋃ p : ι × κ, C p.1 ∩ D p.2 := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i,hi⟩,j,hj⟩
      exact ⟨(i,j),hi,hj⟩
    · rintro ⟨⟨i,j⟩,hi,hj⟩
      exact ⟨⟨i,hi⟩,j,hj⟩
  rw [Set.disjoint_iff_inter_eq_empty,←interior_inter,hu]
  exact hz
end SpectreGeometry.ReverseExistence
