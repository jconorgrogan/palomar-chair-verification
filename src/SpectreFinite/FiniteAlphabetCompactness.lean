module

public import Init

@[expose] public section


/-!
Finite-alphabet prefix compactness, proved by a finite-branching argument.

Only `Init` is imported. The admissibility predicate is arbitrary but must
be closed under taking prefixes. The hypothesis supplies arbitrarily long
finite admissible words over explicit, possibly depth-dependent finite lists. The
conclusion is an infinite stream all of whose finite prefixes are admissible.
This theorem does not itself supply finite patches for any particular model.
-/
namespace SpectreFinite.FiniteAlphabetCompactness

universe u
variable {α : Type u}

/-- A decreasing sequence of predicates on a finite list has a single
persistent witness if it has a witness at every index. -/
theorem exists_mem_forall_of_downward (A : List α) (W : α → Nat → Prop)
    (downward : ∀ a n m, m ≤ n → W a n → W a m)
    (witness : ∀ n, ∃ a, a ∈ A ∧ W a n) :
    ∃ a, a ∈ A ∧ ∀ n, W a n := by
  classical
  induction A with
  | nil =>
      obtain ⟨a, ha, _⟩ := witness 0
      exact False.elim (List.not_mem_nil ha)
  | cons a A ih =>
      by_cases persistent : ∀ n, W a n
      · exact ⟨a, by simp, persistent⟩
      · obtain ⟨bound, fails⟩ := Classical.not_forall.mp persistent
        have tail_witness : ∀ n, ∃ b, b ∈ A ∧ W b n := by
          intro n
          obtain ⟨b, hb, hw⟩ := witness (n + bound)
          rcases List.mem_cons.mp hb with same | in_tail
          · subst b
            exact False.elim (fails (downward a (n + bound) bound (by omega) hw))
          · exact ⟨b, in_tail, downward b (n + bound) n (by omega) hw⟩
        obtain ⟨b, hb, hw⟩ := ih tail_witness
        exact ⟨b, by simp [hb], hw⟩

/-- Every letter in the word belongs to the listed alphabet. Repeated letters
in the list are harmless; no decidable equality on letters is needed. -/
def OverAlphabet (A : List α) (word : List α) : Prop :=
  ∀ a, a ∈ word → a ∈ A

/-- Each letter uses its own finite alphabet, starting at the given depth. -/
def OverChoices (choices : Nat → List α) : Nat → List α → Prop
  | _, [] => True
  | offset, a :: tail => a ∈ choices offset ∧ OverChoices choices (offset + 1) tail

/-- The indexed-letter formulation of `OverChoices`. -/
theorem overChoices_iff_getElem (choices : Nat → List α) (offset : Nat)
    (word : List α) :
    OverChoices choices offset word ↔
      ∀ i (hi : i < word.length), word[i] ∈ choices (offset + i) := by
  induction word generalizing offset with
  | nil => simp [OverChoices]
  | cons a word ih =>
      constructor
      · intro h i hi
        cases i with
        | zero => simpa using h.1
        | succ i =>
            have hw := (ih (offset + 1)).mp h.2 i (by simpa using hi)
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw
      · intro h
        constructor
        · simpa only [Nat.add_zero, List.getElem_cons_zero] using
            h 0 (Nat.zero_lt_succ word.length)
        · apply (ih (offset + 1)).mpr
          intro i hi
          have hw := h (i + 1) (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hw

/-- A constant family of alphabets recovers ordinary list membership. -/
theorem overChoices_const (A : List α) (offset : Nat) (word : List α) :
    OverChoices (fun _ => A) offset word ↔ OverAlphabet A word := by
  induction word generalizing offset with
  | nil => simp [OverChoices, OverAlphabet]
  | cons a word ih =>
      simp [OverChoices, OverAlphabet, ih, List.mem_cons, or_imp, forall_and]

/-- A stem is extendible if it admits arbitrarily long admissible tails,
with every tail letter in the finite alphabet at its depth. -/
def Extendible (choices : Nat → List α) (P : List α → Prop)
    (stem : List α) : Prop :=
  ∀ n, ∃ tail, P (stem ++ tail) ∧ n ≤ tail.length ∧
    OverChoices choices stem.length tail

/-- Some one-letter extension of every extendible stem is extendible. This
is the finite-branching step, not an assumption of an infinite branch. -/
theorem extendible_has_next (choices : Nat → List α) (P : List α → Prop)
    (stem : List α) (h : Extendible choices P stem) :
    ∃ a, a ∈ choices stem.length ∧ Extendible choices P (stem ++ [a]) := by
  let W : α → Nat → Prop := fun a n =>
    ∃ tail, P (stem ++ a :: tail) ∧ n ≤ tail.length ∧
      OverChoices choices (stem.length + 1) tail
  have downward : ∀ a n m, m ≤ n → W a n → W a m := by
    intro a n m hmn hw
    obtain ⟨tail, hp, hn, ha⟩ := hw
    exact ⟨tail, hp, Nat.le_trans hmn hn, ha⟩
  have witness : ∀ n, ∃ a, a ∈ choices stem.length ∧ W a n := by
    intro n
    obtain ⟨tail, hp, hn, ha⟩ := h (n + 1)
    cases tail with
    | nil => simp at hn
    | cons a tail =>
        refine ⟨a, ha.1, tail, hp, ?_, ha.2⟩
        simpa using hn
  obtain ⟨a, ha, hw⟩ := exists_mem_forall_of_downward (choices stem.length) W downward witness
  refine ⟨a, ha, ?_⟩
  intro n
  obtain ⟨tail, hp, hn, ht⟩ := hw n
  exact ⟨tail, by simpa [List.append_assoc] using hp, hn, by simpa using ht⟩

/-- Prefix-closed admissibility of all arbitrarily long extensions implies
admissibility of the stem itself. -/
theorem extendible_admissible (choices : Nat → List α) (P : List α → Prop)
    (hereditary : ∀ word n, P word → P (word.take n))
    (stem : List α) (h : Extendible choices P stem) : P stem := by
  obtain ⟨tail, hp, _, _⟩ := h 0
  have ht := hereditary (stem ++ tail) stem.length hp
  simpa using ht

/-- Kőnig's lemma for explicit finite alphabets and prefix-closed predicates.
The finite alphabet may depend on the depth. No inhabitedness hypothesis is
necessary: arbitrarily long admissible words provide the required letters. -/
theorem exists_stream (choices : Nat → List α) (P : List α → Prop)
    (hereditary : ∀ word n, P word → P (word.take n))
    (arbitrarily_long : ∀ n, ∃ word,
      P word ∧ n ≤ word.length ∧ OverChoices choices 0 word) :
    ∃ stream : Nat → α,
      (∀ n, P ((List.range n).map stream)) ∧ (∀ n, stream n ∈ choices n) := by
  classical
  have start : Extendible choices P [] := by
    intro n
    simpa using arbitrarily_long n
  let S := {stem : List α // Extendible choices P stem}
  let letter : S → α := fun s => Classical.choose (extendible_has_next choices P s.1 s.2)
  have letter_spec : ∀ s : S, letter s ∈ choices s.1.length ∧ Extendible choices P (s.1 ++ [letter s]) := by
    intro s
    exact Classical.choose_spec (extendible_has_next choices P s.1 s.2)
  let step : S → S := fun s => ⟨s.1 ++ [letter s], (letter_spec s).2⟩
  let branch : Nat → S := fun n => Nat.rec ⟨[], start⟩ (fun _ s => step s) n
  let stream : Nat → α := fun n => letter (branch n)
  have prefix_eq : ∀ n, (branch n).1 = (List.range n).map stream := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        change (branch n).1 ++ [stream n] = (List.range (n + 1)).map stream
        rw [List.range_succ, List.map_append, ← ih]
        rfl
  refine ⟨stream, ?_, ?_⟩
  · intro n
    rw [← prefix_eq n]
    exact extendible_admissible choices P hereditary (branch n).1 (branch n).2
  · intro n
    have length_eq : (branch n).1.length = n := by rw [prefix_eq n]; simp
    simpa [length_eq] using (letter_spec (branch n)).1

/-- Equivalent consumer-facing form using ordinary indexed list lookup. -/
theorem exists_stream_of_getElem (choices : Nat → List α) (P : List α → Prop)
    (hereditary : ∀ word n, P word → P (word.take n))
    (arbitrarily_long : ∀ n, ∃ word, P word ∧ n ≤ word.length ∧
      ∀ i (hi : i < word.length), word[i] ∈ choices i) :
    ∃ stream : Nat → α,
      (∀ n, P ((List.range n).map stream)) ∧ (∀ n, stream n ∈ choices n) := by
  apply exists_stream choices P hereditary
  intro n
  obtain ⟨word, hp, hn, hw⟩ := arbitrarily_long n
  refine ⟨word, hp, hn, (overChoices_iff_getElem choices 0 word).mpr ?_⟩
  simpa using hw

/-- Fixed finite alphabet specialization. -/
theorem exists_stream_fixed (A : List α) (P : List α → Prop)
    (hereditary : ∀ word n, P word → P (word.take n))
    (arbitrarily_long : ∀ n, ∃ word,
      P word ∧ n ≤ word.length ∧ OverAlphabet A word) :
    ∃ stream : Nat → α,
      (∀ n, P ((List.range n).map stream)) ∧ (∀ n, stream n ∈ A) := by
  apply exists_stream (fun _ => A) P hereditary
  intro n
  obtain ⟨word, hp, hn, hw⟩ := arbitrarily_long n
  exact ⟨word, hp, hn, (overChoices_const A 0 word).mpr hw⟩

#print axioms exists_mem_forall_of_downward
#print axioms overChoices_iff_getElem
#print axioms overChoices_const
#print axioms extendible_has_next
#print axioms extendible_admissible
#print axioms exists_stream
#print axioms exists_stream_of_getElem
#print axioms exists_stream_fixed

end SpectreFinite.FiniteAlphabetCompactness
