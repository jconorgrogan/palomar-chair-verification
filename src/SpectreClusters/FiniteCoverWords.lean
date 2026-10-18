module

public import Init

@[expose] public section


/-! Complete finite branching for one tile choice at each halo cell.
Only direct pair incompatibility is pruned. -/
namespace SpectreClusters.FiniteCoverWords

universe u
variable {α : Type u}

def extend (compatible : α → α → Bool) (choices : List α)
    (tails : List (List α)) : List (List α) :=
  tails.flatMap fun tail =>
    (choices.filter (fun a => tail.all (compatible a))).map (fun a => a :: tail)

def enumerate (compatible : α → α → Bool) : List (List α) → List (List α)
  | [] => [[]]
  | choices :: more => extend compatible choices (enumerate compatible more)

def OverChoices : List α → List (List α) → Prop
  | [], [] => True
  | a :: tail, choices :: more => a ∈ choices ∧ OverChoices tail more
  | _, _ => False

theorem mem_extend_iff (compatible : α → α → Bool) (choices : List α)
    (tails : List (List α)) (word : List α) :
    word ∈ extend compatible choices tails ↔
      ∃ a ∈ choices, ∃ tail ∈ tails,
        (∀ b ∈ tail, compatible a b = true) ∧ word = a :: tail := by
  simp only [extend,List.mem_flatMap,List.mem_map,List.mem_filter,List.all_eq_true]
  constructor
  · rintro ⟨tail,ht,a,⟨ha,hc⟩,hw⟩
    exact ⟨a,ha,tail,ht,hc,hw.symm⟩
  · rintro ⟨a,ha,tail,ht,hc,rfl⟩
    exact ⟨tail,ht,a,⟨ha,hc⟩,rfl⟩

/-- Both directions: no externally supplied successful-list assumption. -/
theorem mem_enumerate_iff (compatible : α → α → Bool)
    (choices : List (List α)) (word : List α) :
    word ∈ enumerate compatible choices ↔
      OverChoices word choices ∧ word.Pairwise (fun a b => compatible a b = true) := by
  induction choices generalizing word with
  | nil => cases word <;> simp [enumerate,OverChoices]
  | cons choices more ih =>
    rw [enumerate,mem_extend_iff]
    constructor
    · rintro ⟨a,ha,tail,ht,hc,rfl⟩
      obtain ⟨hchoices,hpair⟩ := (ih tail).mp ht
      exact ⟨⟨ha,hchoices⟩,List.Pairwise.cons hc hpair⟩
    · rintro ⟨hchoices,hpair⟩
      cases word with
      | nil => exact False.elim hchoices
      | cons a tail =>
        obtain ⟨ha,ht⟩ := hchoices
        obtain ⟨hc,hpair⟩ := List.pairwise_cons.mp hpair
        exact ⟨a,ha,tail,(ih tail).mpr ⟨ht,hpair⟩,hc,rfl⟩

end SpectreClusters.FiniteCoverWords
