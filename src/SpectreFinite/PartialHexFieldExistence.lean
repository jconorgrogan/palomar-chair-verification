module

public import SpectreFinite.WordLabelCompactness
public import SpectreFinite.PartialHexWalks
public import SpectreFinite.PartialHexDepthGrowth

@[expose] public section


/-! From genuine finite partial systems to an infinite marked field. The
finite systems and their quantitative laws remain explicit inputs. -/
namespace SpectreFinite.HexSearch
namespace PartialMarkedHexSystem

theorem wordLabel_bounded (S : PartialMarkedHexSystem) (hs : S.WellFormed)
    (n : Nat) (root : S.Cell) (hroot : S.Deep n root) (fallback : State) :
    BoundedWordRules (S.wordLabel root fallback) n := by
  constructor
  · intro a b ha hab
    cases hab with
    | cancel u v d =>
        apply S.wordLabel_cancel_context hs fallback u v d
        apply Deep.mono S hroot
        simp only [List.length_append,List.length_cons,List.length_nil] at ha
        omega
    | triangle u v d =>
        apply S.wordLabel_triangle_context hs fallback u v d
        apply Deep.mono S hroot
        simp only [List.length_append,List.length_cons,List.length_nil] at ha
        omega
  · intro w d hw
    exact S.wordLabel_matching hs fallback w d (Deep.mono S hroot hw)

/-- No embedding, freeness, or total-system premise is needed: arbitrarily
deep finite complete neighborhoods supply every finite word constraint. -/
theorem exists_globallyLegal_of_deep_systems
    (hfinite : ∀ R, ∃ S : PartialMarkedHexSystem,
      S.WellFormed ∧ ∃ root : S.Cell, S.Deep R root) :
    ∃ f : Position → State, GloballyLegal f := by
  apply exists_globallyLegal_of_bounded_word_labels
  intro n
  obtain ⟨S,hs,root,hroot⟩ := hfinite n
  exact ⟨S.wordLabel root (0,0),S.wordLabel_bounded hs n root hroot (0,0)⟩

/-- Quantitative finite substitution interface. A separately constructed
family with the displayed genuine growth and preservation laws suffices. -/
theorem exists_globallyLegal_of_growing_systems
    (S : Nat → PartialMarkedHexSystem) (C : Nat)
    (hwf : ∀ n, (S n).WellFormed)
    (harea : ∀ n, 7^n ≤ (S n).cellCount)
    (hboundary : ∀ n, (S n).boundaryPorts.length ≤ C*6^n) :
    ∃ f : Position → State, GloballyLegal f := by
  apply exists_globallyLegal_of_deep_systems
  intro R
  obtain ⟨root,hroot⟩ := growing_systems_have_deep_roots S C R hwf harea hboundary
  exact ⟨S (6*(7^R*C)),hwf _,root,hroot⟩

end PartialMarkedHexSystem
end SpectreFinite.HexSearch
