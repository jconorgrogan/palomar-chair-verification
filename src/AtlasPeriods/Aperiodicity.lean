module
public import AtlasPeriods.Translation
public import RegisteredPrime.AtlasHierarchy
@[expose] public section
namespace RegisteredPrime
namespace AtlasPeriods

/-- Strong induction is uniform in the actual atlas world and the selected
coordinate. A nonzero coordinate would descend to a smaller nonzero one. -/
theorem period_coordinate_zero_by_magnitude (P : Parameters) (n : Nat) :
    ∀ (W : RegisteredWorld P.p), ArithmeticAtlasLegal P W →
    ∀ (v : Cell P.p), TranslationPeriod W v →
    ∀ (j : Fin P.p), (v j).natAbs = n → v j = 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W hl v hv j hn
    by_cases hz : v j = 0
    · exact hz
    have hpos : 0 < (v j).natAbs := Int.natAbs_pos.mpr hz
    let hr : WeakRecognition.Legal P W := ArithmeticAtlasLegal.recognition P W hl
    obtain ⟨t, ht, _⟩ := WeakRecognition.complete_parent_cover P W hr (fun _ => 0)
    let V := WeakRecognition.coarsenAt P W hr t ht
    have hV : ArithmeticAtlasLegal P V := coarsenAt_arithmetic_atlas_legal P W hl t ht
    have hvV : TranslationPeriod V (halfPeriod t v) := coarsenAt_period P W hr v hv t ht
    have he := period_inverse_linear_even P W hr v hv t ht
    have hm := halfPeriod_magnitude t v he j
    have hsmall : (halfPeriod t v (t.frame.perm j)).natAbs < n := by omega
    have hzero := ih (halfPeriod t v (t.frame.perm j)).natAbs hsmall
      V hV (halfPeriod t v) hvV (t.frame.perm j) rfl
    have habszero : (v j).natAbs = 0 := by simpa only [hzero, Int.natAbs_zero, Nat.mul_zero] using hm.symm
    exact Int.natAbs_eq_zero.mp habszero

/-- Every full registered arithmetic-atlas world has no nonzero integer
translation preserving its full signed-frame tile set. Concrete atlas closure
is a proved dependency, not a hypothesis supplied by the user. -/
theorem arithmetic_atlas_translation_aperiodic (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) (v : Cell P.p) (hv : TranslationPeriod W v) :
    v = (fun _ => 0) := by
  funext j
  exact period_coordinate_zero_by_magnitude P (v j).natAbs W hl v hv j rfl

end AtlasPeriods

/-- Registered marked translation aperiodicity for every given generated-E
legal world. This does not assert that such a world exists, or that an unframed
physical realization has the same translation symmetries. -/
theorem registered_translation_aperiodic (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (v : Cell P.p) (hv : AtlasPeriods.TranslationPeriod W v) :
    v = (fun _ => 0) :=
  AtlasPeriods.arithmetic_atlas_translation_aperiodic P W
    (arithmetic_atlas_legal_of_E P W hl) v hv

/-- Equivalent endpoint written directly with the identity-frame translation
pose, without requiring callers to unfold the period predicate. -/
theorem registered_translation_pose_aperiodic (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) (v : Cell P.p)
    (hv : ∀ q, W.tiles q ↔ W.tiles ((AtlasPeriods.translationPose v).comp q)) :
    v = (fun _ => 0) := by
  apply registered_translation_aperiodic P W hl v
  intro q
  simpa only [AtlasPeriods.translationPose_comp] using hv q

end RegisteredPrime
