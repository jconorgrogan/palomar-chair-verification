module

public import SpectreFinite.FiniteObservationCompactness
public import SpectreFinite.HexWordBalls

@[expose] public section


/-! Compactness for bounded word-label witnesses. All finite relations and
edge constraints are actual observations of the fixed 54-state alphabet.
No total hex system or global marked field is an assumption. -/
namespace SpectreFinite.HexSearch

theorem HexWordRel.length_le {a b : HexWord} (h : HexWordRel a b) :
    b.length ≤ a.length := by
  cases h <;> simp <;> omega

structure BoundedWordRules (L : HexWord → State) (n : Nat) : Prop where
  compatible : ∀ a b, a.length ≤ n → HexWordRel a b → L a = L b
  matching : ∀ w d, w.length + 1 ≤ n →
    facingMark (placed ((0,0),L w)) d =
      -facingMark (placed ((0,0),L (w++[d]))) (opposite d)

def WordObservationGood (p : FiniteObservations.Observation HexWord) : Prop :=
  (∀ a b, a ∈ p.map Prod.fst → b ∈ p.map Prod.fst → HexWordRel a b →
    FiniteObservations.read p a = FiniteObservations.read p b) ∧
  (∀ w d, w ∈ p.map Prod.fst → (w++[d]) ∈ p.map Prod.fst →
    facingMark (placed ((0,0),FiniteObservations.read p w)) d =
      -facingMark (placed ((0,0),FiniteObservations.read p (w++[d]))) (opposite d))

theorem restrict_wordObservationGood (L : HexWord → State) {n i : Nat}
    (h : BoundedWordRules L n) (hi : i ≤ n) :
    WordObservationGood (FiniteObservations.restrict L (wordBall i)) := by
  have domain : (FiniteObservations.restrict L (wordBall i)).map Prod.fst = wordBall i := by
    simp [FiniteObservations.restrict,List.map_map,Function.comp_def]
  constructor
  · intro a b ha hb hab
    rw [domain] at ha hb
    rw [FiniteObservations.read_restrict L _ a ha,
      FiniteObservations.read_restrict L _ b hb]
    exact h.compatible a b (Nat.le_trans ((mem_wordBall_iff i a).mp ha) hi) hab
  · intro w d hw hwd
    rw [domain] at hw hwd
    rw [FiniteObservations.read_restrict L _ w hw,
      FiniteObservations.read_restrict L _ (w++[d]) hwd]
    apply h.matching w d
    have hh := (mem_wordBall_iff i (w++[d])).mp hwd
    simp only [List.length_append,List.length_cons,List.length_nil] at hh
    omega

/-- Genuine finite-alphabet compactness assembles all contextual word
relations and edge marks from bounded witnesses at every radius. -/
theorem exists_word_labels_of_bounded
    (hfinite : ∀ n, ∃ L : HexWord → State, BoundedWordRules L n) :
    ∃ L : HexWord → State, WordLabelCompatible L ∧
      ∀ w d, facingMark (placed ((0,0),L w)) d =
        -facingMark (placed ((0,0),L (w++[d]))) (opposite d) := by
  have hf : ∀ n, ∃ L : HexWord → State, ∀ i, i ≤ n →
      WordObservationGood (FiniteObservations.restrict L (wordBall i)) := by
    intro n
    obtain ⟨L,hL⟩ := hfinite n
    exact ⟨L,fun i hi => restrict_wordObservationGood L hL hi⟩
  obtain ⟨L,hL⟩ := FiniteObservations.exists_function wordBall wordBall_nodup
    List.length (fun w => (mem_wordBall_iff w.length w).mpr (Nat.le_refl _))
    WordObservationGood hf
  have domain : ∀ n, (FiniteObservations.restrict L (wordBall n)).map Prod.fst = wordBall n := by
    intro n
    simp [FiniteObservations.restrict,List.map_map,Function.comp_def]
  refine ⟨L,?_,?_⟩
  · intro a b hab
    have ha : a ∈ wordBall a.length := (mem_wordBall_iff _ _).mpr (Nat.le_refl _)
    have hb : b ∈ wordBall a.length := (mem_wordBall_iff _ _).mpr hab.length_le
    have hh := (hL a.length).1 a b (by rw [domain]; exact ha)
      (by rw [domain]; exact hb) hab
    simpa only [FiniteObservations.read_restrict L _ a ha,
      FiniteObservations.read_restrict L _ b hb] using hh
  · intro w d
    have hw : w ∈ wordBall (w.length+1) := (mem_wordBall_iff _ _).mpr (by omega)
    have hwd : (w++[d]) ∈ wordBall (w.length+1) := (mem_wordBall_iff _ _).mpr (by simp)
    have hh := (hL (w.length+1)).2 w d (by rw [domain]; exact hw)
      (by rw [domain]; exact hwd)
    simpa only [FiniteObservations.read_restrict L _ w hw,
      FiniteObservations.read_restrict L _ (w++[d]) hwd] using hh

theorem exists_globallyLegal_of_bounded_word_labels
    (hfinite : ∀ n, ∃ L : HexWord → State, BoundedWordRules L n) :
    ∃ f : Position → State, GloballyLegal f := by
  obtain ⟨L,hL,hm⟩ := exists_word_labels_of_bounded hfinite
  exact exists_globallyLegal_of_word_labels L
    (fun u v d => hL _ _ (HexWordRel.cancel u v d))
    (fun u v d => hL _ _ (HexWordRel.triangle u v d)) hm

end SpectreFinite.HexSearch
