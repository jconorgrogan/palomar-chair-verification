module

public import SparseMonotiles.CarrierHierarchyCells

@[expose] public section

/-!
The combinatorial fan argument in the ordinary recognizability proof, proved
without a finite corona census. Its premises are local outside-cell coverage and
nonoverlap consequences which must still be obtained from the exact 284/408
contact laws. These premises are strictly local implications, not parent
existence or a hierarchy assumption.
-/
namespace SparseMonotiles.CarrierHierarchy

/-- A predecessor and a wall lie across the same root outside facet when their
role has this bit at this axis. -/
structure FanData (d : ℕ) where
  incoming : Bits d → Prop
  wall : Fin d → Bool → Prop
  cover : ∀ a, Proper a → ∀ i, ¬ incoming a → wall i (a i)
  exclude : ∀ a, Proper a → NonemptyRole a → incoming a →
    ∀ i, ¬ wall i (a i)

/-- Presence propagates across any shared bit of a nonempty predecessor. -/
theorem FanData.propagate {d : ℕ} (F : FanData d) {a b : Bits d}
    (ha : Proper a) (hna : NonemptyRole a) (hia : F.incoming a)
    (hb : Proper b) (shared : ∃ i, a i = b i) : F.incoming b := by
  classical
  obtain ⟨i, hi⟩ := shared
  by_contra hn
  exact F.exclude a ha hna hia i (hi ▸ F.cover b hb i hn)

private theorem third_axis {d : ℕ} (hd : 3 ≤ d) (j k : Fin d) :
    ∃ l : Fin d, l ≠ j ∧ l ≠ k := by
  classical
  by_contra h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {j, k} := by
    intro l _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    apply h
    exact ⟨l, fun he => hn (Or.inl he), fun he => hn (Or.inr he)⟩
  have hc := Finset.card_le_card hsub
  have hb : ({j, k} : Finset (Fin d)).card ≤ 2 := by
    exact le_trans (Finset.card_insert_le _ _) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  omega

/-- The uniform fan-completion step: one nonempty incoming role forces every
proper incoming role. Dimension three is the exact assumption used here. -/
theorem FanData.complete_of_nonempty_incoming {d : ℕ} (F : FanData d)
    (hd : 3 ≤ d) {a : Bits d} (ha : Proper a) (hna : NonemptyRole a)
    (hia : F.incoming a) : ∀ b, Proper b → F.incoming b := by
  classical
  intro b hb
  by_cases hs : ∃ i, a i = b i
  · exact F.propagate ha hna hia hb hs
  · obtain ⟨j, hj⟩ := hna
    obtain ⟨k, hk⟩ := ha
    obtain ⟨l, hlj, hlk⟩ := third_axis hd j k
    let c : Bits d := fun i => decide (i = j ∨ i = k)
    have hc : Proper c := ⟨l, by simp [c, hlj, hlk]⟩
    have hnc : NonemptyRole c := ⟨j, by simp [c]⟩
    have hic : F.incoming c :=
      F.propagate ⟨k, hk⟩ ⟨j, hj⟩ hia hc ⟨j, by simp [c, hj]⟩
    apply F.propagate hc hnc hic hb
    refine ⟨k, ?_⟩
    have hbk : b k = true := by
      cases he : b k
      · exact False.elim (hs ⟨k, hk.trans he.symm⟩)
      · rfl
    simp [c, hbk]

/-- An incomplete star has no nonempty predecessor. -/
theorem FanData.incomplete_only_empty {d : ℕ} (F : FanData d)
    (hd : 3 ≤ d) (incomplete : ¬ ∀ a, Proper a → F.incoming a)
    {a : Bits d} (ha : Proper a) (hia : F.incoming a) :
    a = fun _ => false := by
  funext i
  cases hi : a i
  · rfl
  · exact False.elim (incomplete (F.complete_of_nonempty_incoming hd ha ⟨i, hi⟩ hia))

/-- Every wall is forced when a star is incomplete. The negative wall uses a
nonempty role on another axis; omitting that case would lose the H₀ argument. -/
theorem FanData.incomplete_all_walls {d : ℕ} (F : FanData d)
    (hd : 3 ≤ d) (incomplete : ¬ ∀ a, Proper a → F.incoming a) :
    ∀ i b, F.wall i b := by
  classical
  intro i b
  obtain ⟨k, hki, _⟩ := third_axis hd i i
  let a : Bits d := fun j => if j = i then b else decide (j = k)
  have hna : NonemptyRole a := ⟨k, by simp [a, hki]⟩
  obtain ⟨l, hli, hlk⟩ := third_axis hd i k
  have ha : Proper a := ⟨l, by simp [a, hli, hlk]⟩
  have hn : ¬ F.incoming a := by
    intro hi
    exact incomplete (F.complete_of_nonempty_incoming hd ha hna hi)
  simpa [a] using F.cover a ha i hn

#print axioms FanData.complete_of_nonempty_incoming
#print axioms FanData.incomplete_all_walls
end SparseMonotiles.CarrierHierarchy
