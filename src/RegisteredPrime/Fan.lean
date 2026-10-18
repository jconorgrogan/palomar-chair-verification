module
public import RegisteredPrime.CompletedRules
@[expose] public section
namespace RegisteredPrime
structure FanData (d : Nat) where
  incoming : Mask d → Prop
  wall : Fin d → Bool → Prop
  cover : ∀ a, Proper a → ∀ i, ¬ incoming a → wall i (a i)
  exclude : ∀ a, Proper a → NonemptyMask a → incoming a → ∀ i, ¬ wall i (a i)
theorem third_axis {d : Nat} (hd : 3 ≤ d) (j k : Fin d) :
    ∃ l : Fin d, l ≠ j ∧ l ≠ k := by
  classical
  by_cases h0 : (⟨0, by omega⟩ : Fin d) ≠ j ∧ (⟨0, by omega⟩ : Fin d) ≠ k
  · exact ⟨⟨0, by omega⟩, h0⟩
  by_cases h1 : (⟨1, by omega⟩ : Fin d) ≠ j ∧ (⟨1, by omega⟩ : Fin d) ≠ k
  · exact ⟨⟨1, by omega⟩, h1⟩
  refine ⟨⟨2, by omega⟩, ?_⟩
  simp only [Ne, Fin.ext_iff] at *
  omega
theorem FanData.propagate {d : Nat} (F : FanData d) {a b : Mask d}
    (ha : Proper a) (hna : NonemptyMask a) (hia : F.incoming a)
    (hb : Proper b) (shared : ∃ i, a i = b i) : F.incoming b := by
  classical
  obtain ⟨i, hi⟩ := shared
  apply Classical.byContradiction
  intro hn
  exact F.exclude a ha hna hia i (hi ▸ F.cover b hb i hn)
theorem FanData.complete_of_nonempty_incoming {d : Nat} (F : FanData d)
    (hd : 3 ≤ d) {a : Mask d} (ha : Proper a) (hna : NonemptyMask a)
    (hia : F.incoming a) : ∀ b, Proper b → F.incoming b := by
  classical
  intro b hb
  by_cases hs : ∃ i, a i = b i
  · exact F.propagate ha hna hia hb hs
  · obtain ⟨j, hj⟩ := hna
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hlj, hlk⟩ := third_axis hd j k
    let c : Mask d := fun i => decide (i = j ∨ i = k)
    have hc : Proper c := ⟨l, by simp [c, hlj, hlk]⟩
    have hnc : NonemptyMask c := ⟨j, by simp [c]⟩
    have hic : F.incoming c := F.propagate ⟨k, hk⟩ ⟨j, hj⟩ hia hc ⟨j, by simp [c, hj]⟩
    apply F.propagate hc hnc hic hb
    refine ⟨k, ?_⟩
    have hbk : b k = true := by
      cases he : b k
      · exact False.elim (hs ⟨k, hk.trans he.symm⟩)
      · rfl
    simp [c, hbk]
theorem FanData.incomplete_only_empty {d : Nat} (F : FanData d)
    (hd : 3 ≤ d) (incomplete : ¬ ∀ a, Proper a → F.incoming a)
    {a : Mask d} (ha : Proper a) (hia : F.incoming a) : a = fun _ => false := by
  funext i
  cases hi : a i
  · rfl
  · exact False.elim (incomplete (F.complete_of_nonempty_incoming hd ha ⟨i, hi⟩ hia))
theorem FanData.incomplete_all_walls {d : Nat} (F : FanData d)
    (hd : 3 ≤ d) (incomplete : ¬ ∀ a, Proper a → F.incoming a) :
    ∀ i b, F.wall i b := by
  classical
  intro i b
  obtain ⟨k, hki, _⟩ := third_axis hd i i
  let a : Mask d := fun j => if j = i then b else decide (j = k)
  have hna : NonemptyMask a := ⟨k, by simp [a, hki]⟩
  obtain ⟨l, hli, hlk⟩ := third_axis hd i k
  have ha : Proper a := ⟨l, by simp [a, hli, hlk]⟩
  have hn : ¬ F.incoming a := by
    intro hi
    exact incomplete (F.complete_of_nonempty_incoming hd ha hna hi)
  simpa [a] using F.cover a ha i hn
theorem FanData.prime_completion (P : Parameters) (F : FanData P.p)
    {a : Mask P.p} (ha : Proper a) (hna : NonemptyMask a) (hia : F.incoming a) :
    ∀ b, Proper b → F.incoming b :=
  F.complete_of_nonempty_incoming (P.prime.three_le P.odd) ha hna hia
end RegisteredPrime
