module

public import SpectreFinite.ParentRotation

@[expose] public section


/-! A finite boundary estimate for the later hierarchy argument. A finite
block disjoint from its translate has cardinality at most translation-word
length times the cardinality of a boundary containing all one-step escapes.
Uses Init lists, without importing the larger Mathlib environment. -/
namespace SpectreFinite.HexSearch.FiniteBoundaryEstimate
open ParentOwnership

def escape (A : List Position) (v : Position) : List Position :=
  A.filter fun x => decide (addPos x v ∉ A)

theorem mem_escape (A : List Position) (v x : Position) :
    x ∈ escape A v ↔ x ∈ A ∧ addPos x v ∉ A := by simp [escape]

theorem escape_nodup (A : List Position) (ha : A.Nodup) (v : Position) :
    (escape A v).Nodup := List.Pairwise.filter _ ha

theorem escape_add_subset (A : List Position) (v w : Position) :
    escape A (addPos v w) ⊆ escape A v ++ (escape A w).map (fun x => subPos x v) := by
  intro x hx
  obtain ⟨hxA,hxout⟩ := (mem_escape A _ x).mp hx
  by_cases hnext : addPos x v ∈ A
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨addPos x v,(mem_escape A w _).mpr ⟨hnext,?_⟩,?_⟩
    · simpa only [addPos_assoc] using hxout
    · apply Prod.ext <;> simp only [subPos,addPos] <;> omega
  · exact List.mem_append_left _ ((mem_escape A v x).mpr ⟨hxA,hnext⟩)

theorem escape_add_length_le (A : List Position) (ha : A.Nodup) (v w : Position) :
    (escape A (addPos v w)).length ≤ (escape A v).length + (escape A w).length := by
  have h := (escape_nodup A ha (addPos v w)).length_le_of_subset (escape_add_subset A v w)
  simpa only [List.length_append,List.length_map] using h

def wordDisplacement : List Position → Position
  | [] => (0,0)
  | s::ss => addPos s (wordDisplacement ss)

theorem escape_word_length_le (A B : List Position) (ha : A.Nodup) (word : List Position)
    (hb : ∀ s ∈ word, escape A s ⊆ B) :
    (escape A (wordDisplacement word)).length ≤ word.length * B.length := by
  induction word with
  | nil => simp [wordDisplacement,escape,addPos]
  | cons s ss ih =>
    have hs : (escape A s).length ≤ B.length :=
      (escape_nodup A ha s).length_le_of_subset (hb s (by simp))
    have hss := ih (fun t ht => hb t (by simp [ht]))
    calc
      _ ≤ (escape A s).length + (escape A (wordDisplacement ss)).length :=
        escape_add_length_le A ha s _
      _ ≤ B.length + ss.length * B.length := Nat.add_le_add hs hss
      _ = (s::ss).length * B.length := by simp [Nat.add_mul,Nat.add_comm]

theorem escape_eq_self_of_translate_disjoint (A : List Position) (v : Position)
    (hd : ∀ x ∈ A, addPos x v ∉ A) : escape A v = A := by
  apply List.filter_eq_self.mpr
  intro x hx
  exact decide_eq_true (hd x hx)

/-- Pointwise disjointness means precisely that the finite block and its
literal translate have no shared cell. -/
theorem cardinal_le_word_boundary (A B : List Position) (ha : A.Nodup)
    (word : List Position) (hb : ∀ s ∈ word, escape A s ⊆ B)
    (hd : ∀ x ∈ A, addPos x (wordDisplacement word) ∉ A) :
    A.length ≤ word.length * B.length := by
  have h := escape_word_length_le A B ha word hb
  rwa [escape_eq_self_of_translate_disjoint A _ hd] at h

end SpectreFinite.HexSearch.FiniteBoundaryEstimate
