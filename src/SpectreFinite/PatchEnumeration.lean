module

public import Init

@[expose] public section


/-! Complete finite branching with pairwise pruning. This is a generic
finite-domain enumeration theorem, not a claim that a recovered patch list
is exhaustive or that the planar physical model has been encoded. -/
namespace SpectreFinite.Search
universe u v
variable {ι : Type u} {σ : Type v}
variable (choices : ι → List σ) (C : (ι × σ) → (ι × σ) → Prop) [DecidableRel C]

def compatibleWith (x : ι × σ) (xs : List (ι × σ)) : Bool :=
  xs.all (fun y => decide (C x y))

theorem compatibleWith_iff (x : ι × σ) (xs : List (ι × σ)) :
    compatibleWith C x xs = true ↔ ∀ y ∈ xs, C x y := by
  simp [compatibleWith, List.all_eq_true]

/-- Exhaustive finite choices, rejecting only an explicitly incompatible
pair with the already assigned suffix. -/
def enumerate : List ι → List (List (ι × σ))
  | [] => [[]]
  | i :: is => (enumerate is).flatMap (fun tail =>
      (choices i).flatMap (fun a =>
        if compatibleWith C (i,a) tail then [(i,a) :: tail] else []))

theorem mem_enumerate_cons (i : ι) (is : List ι) (p : List (ι × σ)) :
    p ∈ enumerate choices C (i :: is) ↔
      ∃ a ∈ choices i, ∃ tail ∈ enumerate choices C is,
        compatibleWith C (i,a) tail = true ∧ p = (i,a) :: tail := by
  simp only [enumerate, List.mem_flatMap]
  constructor
  · rintro ⟨tail,ht,a,ha,hp⟩
    by_cases hc : compatibleWith C (i,a) tail = true
    · simp only [hc, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hp
      exact ⟨a,ha,tail,ht,hc,hp⟩
    · simp [hc] at hp
  · rintro ⟨a,ha,tail,ht,hc,rfl⟩
    exact ⟨tail,ht,a,ha,by simp [hc]⟩

/-- Exact soundness AND completeness for this finite search. A successful
external sample list is not used as a premise. -/
theorem mem_enumerate_iff (is : List ι) (p : List (ι × σ)) :
    p ∈ enumerate choices C is ↔
      p.map Prod.fst = is ∧ p.Pairwise C ∧ ∀ x ∈ p, x.2 ∈ choices x.1 := by
  induction is generalizing p with
  | nil =>
    cases p <;> simp [enumerate]
  | cons i is ih =>
    rw [mem_enumerate_cons]
    constructor
    · rintro ⟨a,ha,tail,ht,hc,rfl⟩
      obtain ⟨hm,hpair,hchoices⟩ := (ih tail).mp ht
      refine ⟨by simpa using congrArg (List.cons i) hm, ?_, ?_⟩
      · exact List.Pairwise.cons ((compatibleWith_iff C (i,a) tail).mp hc) hpair
      · intro x hx
        rcases List.mem_cons.mp hx with he | hx
        · subst x; exact ha
        · exact hchoices x hx
    · rintro ⟨hm,hpair,hchoices⟩
      cases p with
      | nil => simp at hm
      | cons x tail =>
        rcases x with ⟨j,a⟩
        have hj : j = i := (List.cons.inj hm).1
        subst j
        have htail : tail.map Prod.fst = is := (List.cons.inj hm).2
        have hp := List.pairwise_cons.mp hpair
        refine ⟨a,hchoices (i,a) (by simp),tail,(ih tail).mpr ⟨htail,hp.2,?_⟩,
          (compatibleWith_iff C (i,a) tail).mpr hp.1,rfl⟩
        intro x hx
        exact hchoices x (List.mem_cons_of_mem _ hx)

#print axioms compatibleWith_iff
#print axioms mem_enumerate_cons
#print axioms mem_enumerate_iff
end SpectreFinite.Search
