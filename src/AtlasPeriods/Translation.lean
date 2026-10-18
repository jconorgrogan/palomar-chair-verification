module
public import WeakRecognition.CoarseWorld
@[expose] public section
namespace RegisteredPrime
namespace AtlasPeriods

/-- Translate a full marked pose without changing its signed frame. -/
def translate {p : Nat} (v : Cell p) (q : Pose p) : Pose p where
  frame := q.frame
  anchor := fun i => v i + q.anchor i

/-- The identity-frame translation pose. -/
def translationPose {p : Nat} (v : Cell p) : Pose p where
  frame := (identityPose p).frame
  anchor := v

theorem translationPose_comp {p : Nat} (v : Cell p) (q : Pose p) :
    (translationPose v).comp q = translate v q := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · intro i
    simp [translationPose, translate, Pose.comp, RegisteredFrame.comp, identityPose]
  · intro i
    simp [translationPose, translate, Pose.comp, RegisteredFrame.linear,
      RegisteredFrame.sign, identityPose]

theorem translate_comp {p : Nat} (v : Cell p) (q r : Pose p) :
    (translate v q).comp r = translate v (q.comp r) := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change (v i + q.anchor i) + q.frame.linear r.anchor i =
    v i + (q.anchor i + q.frame.linear r.anchor i)
  omega

/-- Equality of the full marked tile set under an integer translation. -/
def TranslationPeriod {p : Nat} (W : RegisteredWorld p) (v : Cell p) : Prop :=
  ∀ q, W.tiles q ↔ W.tiles (translate v q)

theorem period_complete_parent (P : Parameters) (W : RegisteredWorld P.p)
    (v : Cell P.p) (hv : TranslationPeriod W v) (t : Pose P.p) :
    CompleteParent P W t ↔ CompleteParent P W (translate v t) := by
  constructor
  · intro ht a
    rw [translate_comp]
    exact (hv _).mp (ht a)
  · intro ht a
    apply (hv _).mpr
    rw [← translate_comp]
    exact ht a

theorem relative_translate_anchor {p : Nat} (t : Pose p) (v : Cell p) (i : Fin p) :
    (t.relative (translate v t)).anchor i = t.frame.inv.linear v i := by
  simp only [Pose.relative, Pose.comp, Pose.inv, translate, RegisteredFrame.linear,
    RegisteredFrame.sign, RegisteredFrame.inv]
  by_cases hn : t.frame.negative (t.frame.inverse i) = true <;> simp [hn] <;> omega

/-- Global recognized-parent alignment makes the conjugated translation even. -/
theorem period_inverse_linear_even (P : Parameters) (W : RegisteredWorld P.p)
    (hl : WeakRecognition.Legal P W) (v : Cell P.p) (hv : TranslationPeriod W v)
    (t : Pose P.p) (ht : CompleteParent P W t) :
    ∀ i, t.frame.inv.linear v i % 2 = 0 := by
  have he := WeakRecognition.complete_parents_relative_even P W hl t (translate v t)
    ht ((period_complete_parent P W v hv t).mp ht)
  intro i
  simpa only [relative_translate_anchor] using he i

/-- The period in the coordinate frame and scale of an actual coarse world. -/
def halfPeriod {p : Nat} (t : Pose p) (v : Cell p) : Cell p :=
  fun i => t.frame.inv.linear v i / 2

theorem halfPeriod_double {p : Nat} (t : Pose p) (v : Cell p)
    (he : ∀ i, t.frame.inv.linear v i % 2 = 0) (i : Fin p) :
    2 * halfPeriod t v i = t.frame.inv.linear v i := by
  have hi := he i
  change 2 * (t.frame.inv.linear v i / 2) = t.frame.inv.linear v i
  omega

/-- A signed permutation only reindexes and changes signs of coordinates;
therefore the chosen coarse coordinate has exactly half the magnitude. -/
theorem halfPeriod_magnitude {p : Nat} (t : Pose p) (v : Cell p)
    (he : ∀ i, t.frame.inv.linear v i % 2 = 0) (j : Fin p) :
    2 * (halfPeriod t v (t.frame.perm j)).natAbs = (v j).natAbs := by
  have h := halfPeriod_double t v he (t.frame.perm j)
  have ha := congrArg Int.natAbs h
  simp only [RegisteredFrame.linear, RegisteredFrame.inv, RegisteredFrame.sign,
    t.frame.left_inverse] at ha
  cases hn : t.frame.negative j <;> simp [hn, Int.natAbs_mul] at ha <;> exact ha

/-- Exact conjugacy of translation with the concrete coarsening coordinates. -/
theorem halfPeriod_conjugacy {p : Nat} (t : Pose p) (v : Cell p)
    (he : ∀ i, t.frame.inv.linear v i % 2 = 0) (q : Pose p) :
    t.comp (doubleAnchor (translate (halfPeriod t v) q)) =
      translate v (t.comp (doubleAnchor q)) := by
  apply Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  have hi := halfPeriod_double t v he (t.frame.perm i)
  simp only [RegisteredFrame.linear, RegisteredFrame.inv, RegisteredFrame.sign,
    t.frame.left_inverse] at hi
  change t.anchor i + t.frame.sign i *
      (2 * (halfPeriod t v (t.frame.perm i) + q.anchor (t.frame.perm i))) =
    v i + (t.anchor i + t.frame.sign i * (2 * q.anchor (t.frame.perm i)))
  unfold RegisteredFrame.sign
  cases hn : t.frame.negative i <;> simp [hn] at hi ⊢ <;> omega

/-- A genuine fine-world period descends to a period of its actual coarse
world. No coarse legality or abstract hierarchy is assumed in this lemma. -/
theorem coarsenAt_period (P : Parameters) (W : RegisteredWorld P.p)
    (hl : WeakRecognition.Legal P W) (v : Cell P.p) (hv : TranslationPeriod W v)
    (t : Pose P.p) (ht : CompleteParent P W t) :
    TranslationPeriod (WeakRecognition.coarsenAt P W hl t ht) (halfPeriod t v) := by
  have he := period_inverse_linear_even P W hl v hv t ht
  intro q
  change CompleteParent P W (t.comp (doubleAnchor q)) ↔
    CompleteParent P W (t.comp (doubleAnchor (translate (halfPeriod t v) q)))
  rw [halfPeriod_conjugacy t v he q]
  exact period_complete_parent P W v hv _

end AtlasPeriods
end RegisteredPrime
