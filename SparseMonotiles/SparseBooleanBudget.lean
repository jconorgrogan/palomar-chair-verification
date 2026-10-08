module
public import Mathlib.Data.List.Basic
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace SparseMonotiles.BooleanBudget

/-- Sum of coordinate costs. Membership theorems also require matching lengths. -/
def assignmentCost : List (Bool → ℕ) → List Bool → ℕ
  | c :: cs, b :: bs => c b + assignmentCost cs bs
  | _, _ => 0

/-- Explore only a bit whose nonnegative cost fits the remaining budget. -/
def generate : List (Bool → ℕ) → ℕ → List (List Bool)
  | [], _ => [[]]
  | c :: cs, budget =>
      (if c false ≤ budget then (generate cs (budget - c false)).map (false :: ·) else []) ++
      (if c true ≤ budget then (generate cs (budget - c true)).map (true :: ·) else [])

/-- Exact soundness and completeness, independent of the number of coordinates. -/
theorem mem_generate (cs : List (Bool → ℕ)) (bs : List Bool) (budget : ℕ) :
    bs ∈ generate cs budget ↔ bs.length = cs.length ∧ assignmentCost cs bs ≤ budget := by
  induction cs generalizing bs budget with
  | nil => cases bs <;> simp [generate, assignmentCost]
  | cons c cs ih =>
    cases bs with
    | nil => simp [generate, assignmentCost]
    | cons b bs =>
      cases b <;>
        by_cases hf : c false ≤ budget <;>
        by_cases ht : c true ≤ budget <;>
        simp [generate, hf, ht, ih, assignmentCost] <;> omega

 theorem complete {cs : List (Bool → ℕ)} {bs : List Bool} {budget : ℕ}
    (hlen : bs.length = cs.length) (hcost : assignmentCost cs bs ≤ budget) :
    bs ∈ generate cs budget := (mem_generate cs bs budget).mpr ⟨hlen, hcost⟩

 theorem sound {cs : List (Bool → ℕ)} {bs : List Bool} {budget : ℕ}
    (h : bs ∈ generate cs budget) :
    bs.length = cs.length ∧ assignmentCost cs bs ≤ budget :=
  (mem_generate cs bs budget).mp h

/-- Pointwise assignments on any coordinate list inherit exact completeness. -/
theorem assignmentCost_map {ι : Type} (coords : List ι) (cost : ι → Bool → ℕ)
    (bits : ι → Bool) :
    assignmentCost (coords.map cost) (coords.map bits) =
      (coords.map fun i => cost i (bits i)).sum := by
  induction coords with
  | nil => rfl
  | cons i coords ih => simp [assignmentCost, ih]

theorem mem_generate_map {ι : Type} (coords : List ι) (cost : ι → Bool → ℕ)
    (bits : ι → Bool) (budget : ℕ) :
    coords.map bits ∈ generate (coords.map cost) budget ↔
      (coords.map fun i => cost i (bits i)).sum ≤ budget := by
  rw [mem_generate, assignmentCost_map]
  simp

#print axioms mem_generate
#print axioms assignmentCost_map
#print axioms mem_generate_map
#print axioms complete
#print axioms sound
end SparseMonotiles.BooleanBudget
