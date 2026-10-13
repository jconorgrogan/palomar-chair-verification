module

public import PhysicalRegistration.GenericBaseLabelMatching
public import PhysicalRegistration.PhysicalWholeCompanions

@[expose] public section

/-!
# Labelwise whole-base matching

Actual dense complementary incidences cannot differ from a whole-complex
companion: the full incident set has exactly two members. Disjoint native
tubes identify the companion site. Closure then promotes each dense labelled
base contact to containment of the entire corresponding base crease, and
reciprocal whole-complex equality gives labelwise base equality.
-/

namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- Whole-complex containment upgrades actual dense label matching to
whole-base containment and the exact opposite signed coefficient. -/
theorem PhysicalTiling.base_labels_of_creaseComplex_subset
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root other : ι) (u v : Site m) (s : Side m)
    (hne : other ≠ root)
    (hsub : f root '' creaseComplex a u ⊆ f other '' creaseComplex a v) :
    f root '' baseCrease a u s ⊆ f other '' baseCrease a v s ∧
      a.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value v : ℝ)) := by
  obtain ⟨D, hDG, hDC, hD⟩ := T.genericBaseCrease_labelled_companions hm root u s
  have hlocal : ∀ x ∈ D, x ∈ f other '' baseCrease a v s ∧
      a.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value v : ℝ)) := by
    intro x hx
    obtain ⟨j, hj, hinc, w, hw, _, hneg, hsign⟩ := hD x hx
    have hroot : x ∈ f root '' creaseComplex a u := by
      obtain ⟨y, hy, hxy⟩ := hDG hx
      exact ⟨y, baseCrease_subset_creaseComplex a u s hy.1, hxy⟩
    have hother := hsub hroot
    have hi : other ∈ incidentTiles a f x :=
      placed_creaseComplex_subset_body hm a (f other) v hother
    rw [hinc] at hi
    have hij : other = j := hi.resolve_left hne
    subst j
    have hpre : (f other).symm x ∈ creaseComplex a v := by
      obtain ⟨y, hy, hxy⟩ := hother
      simpa [← hxy] using hy
    have hprew : (f other).symm x ∈ creaseComplex a w := by
      obtain ⟨y, hy, hxy⟩ := hw
      simpa [← hxy] using baseCrease_subset_creaseComplex a w s hy.1
    have hwv : w = v := by
      by_contra hne'
      exact Set.disjoint_left.mp (creaseComplex_pairwise_disjoint hm a hne') hprew hpre
    subst w
    exact ⟨image_mono (fun _ hz => hz.1) hw, hneg, hsign⟩
  have hDne : D.Nonempty := closure_nonempty_iff.mp (by
    rw [hDC]
    exact (baseCrease_nonempty a u s).image (f root))
  obtain ⟨x, hx⟩ := hDne
  refine ⟨?_, (hlocal x hx).2⟩
  rw [← hDC]
  exact closure_minimal (fun y hy => (hlocal y hy).1)
    ((baseCrease_isCompact a v s).image (f other).continuous).isClosed

/-- An actual whole-complex companion matches every full native base-side
label and has precisely the negated coefficient. -/
theorem PhysicalTiling.whole_base_labels_of_creaseComplex_eq
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root other : ι) (u v : Site m)
    (hne : other ≠ root)
    (heq : f root '' creaseComplex a u = f other '' creaseComplex a v) :
    (∀ s : Side m, f root '' baseCrease a u s = f other '' baseCrease a v s) ∧
      a.value v = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value v : ℝ)) := by
  constructor
  · intro s
    exact subset_antisymm
      (T.base_labels_of_creaseComplex_subset hm root other u v s hne heq.subset).1
      (T.base_labels_of_creaseComplex_subset hm other root v u s (Ne.symm hne)
        heq.symm.subset).1
  · let s : Side m := (⟨0, NeZero.pos m⟩, false)
    exact (T.base_labels_of_creaseComplex_subset hm root other u v s hne heq.subset).2

/-- Every native key in an actual physical tiling has a unique other whole
crease companion, with every base label preserved and coefficient negated.
The physical-tiling endpoint supplies all contact and matching facts. -/
theorem PhysicalTiling.unique_labelled_crease_companion
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site m) :
    ∃! iv : ι × Site m, iv.1 ≠ root ∧
      f root '' creaseComplex a u = f iv.1 '' creaseComplex a iv.2 ∧
      (∀ s : Side m, f root '' baseCrease a u s = f iv.1 '' baseCrease a iv.2 s) ∧
      a.value iv.2 = -a.value u ∧
      decide (0 < (a.value u : ℝ)) ≠ decide (0 < (a.value iv.2 : ℝ)) := by
  obtain ⟨iv, hiv, huniq⟩ := T.unique_equal_crease_companion hm root u
  refine ⟨iv, ⟨hiv.1, hiv.2,
    T.whole_base_labels_of_creaseComplex_eq hm root iv.1 u iv.2 hiv.1 hiv.2⟩, ?_⟩
  intro kv hkv
  exact huniq kv ⟨hkv.1, hkv.2.1⟩

end
end PhysicalRegistration.NativeChair
