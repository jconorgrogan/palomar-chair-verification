module

public import PhysicalRegistration.KeyNormalRank
public import PhysicalRegistration.NativeBoundary

@[expose] public section

/-!
# Classification of actual key points under a two-normal transverse bound

The hypotheses refer only to the normals of the literal affine side faces
through the point, and to the carrier normal when its height is zero. The
three possible strata are derived from the actual finite lower envelope and
native normal-rank computations. No boundary inventory or angle-sector model
is assumed.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- An inactive branch lies strictly above an active native branch. -/
theorem branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (s t : Side m) (x : Space m)
    (hs : x ∈ sideFace a u s) (ht : x ∉ sideFace a u t) :
    branchProfile J u s x < branchProfile J u t x := by
  apply lt_of_le_of_ne (hs.2.2 t)
  intro heq
  apply ht
  refine ⟨hs.1, ?_, ?_⟩
  · exact heq ▸ hs.2.1
  · intro r
    exact heq ▸ hs.2.2 r

/-- Zero profile on an active native face has exactly zero normal height. -/
theorem normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
    {m J : ℕ} [NeZero m] (a : Coefficients m J) (u : Site m)
    (s : Side m) (x : Space m) (hs : x ∈ sideFace a u s)
    (hzero : branchProfile J u s x = 0) : normalCoord u x = 0 := by
  rw [hs.1.2]
  unfold siteHeight keyHeight
  rw [native_profile_eq_branch J u s x hs.2, hzero, mul_zero]

/-- Two distinct active labels on one axis force the literal common apex. -/
theorem eq_keyApex_of_mem_sideFace_same_axis {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (s t : Side m) (x : Space m)
    (hs : x ∈ sideFace a u s) (ht : x ∈ sideFace a u t)
    (hst : s ≠ t) (haxis : s.1 = t.1) : x = keyApex a u := by
  rcases s with ⟨i, b⟩
  rcases t with ⟨j, c⟩
  simp only at haxis
  subst j
  cases b <;> cases c
  · exact (hst rfl).elim
  · have hx : x ∈ sideCrease a u (i, false) (i, true) := ⟨hs, ht⟩
    simpa only [opposite_sideCrease_eq_singleton, Set.mem_singleton_iff] using hx
  · have hx : x ∈ sideCrease a u (i, false) (i, true) := ⟨ht, hs⟩
    simpa only [opposite_sideCrease_eq_singleton, Set.mem_singleton_iff] using hx
  · exact (hst rfl).elim

/-- A native key point whose incident normals lie in an arbitrary two-vector
span is on one strict side, one generic base crease, or one generic side crease
with distinct tangent axes. The vectors need not themselves be independent. -/
theorem keyGraph_transverse_stratum_classification {m J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients m J) (u : Site m) (x p q : Space m)
    (hx : x ∈ keyGraph a u)
    (hside : ∀ s : Side m, x ∈ sideFace a u s →
      sideNormal a u s ∈ Submodule.span ℝ ({p, q} : Set (Space m)))
    (hbase : normalCoord u x = 0 →
      outward u.1 ∈ Submodule.span ℝ ({p, q} : Set (Space m))) :
    (∃ s : Side m, x ∈ strictBranchRegion J u s) ∨
    (∃ s : Side m, x ∈ genericBaseCrease a u s) ∨
    (∃ s t : Side m, s.1 ≠ t.1 ∧ x ∈ genericSideCrease a u s t) := by
  classical
  let S : Finset (Side m) := Finset.univ.filter (fun s => x ∈ sideFace a u s)
  have hmem : ∀ s : Side m, s ∈ S ↔ x ∈ sideFace a u s := by
    intro s
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hnonempty : S.Nonempty := by
    obtain ⟨s, hs⟩ := exists_active_branch J u x hx.1
    exact ⟨s, (hmem s).mpr ⟨hx, hs⟩⟩
  have hcard : S.card ≤ 2 := side_labels_in_span_pair_card_le_two a u S p q
    (fun s hs => hside s ((hmem s).mp hs))
  have hapex : x ≠ keyApex a u := by
    intro heq
    have hS : S = Finset.univ := by
      ext s
      simp only [Finset.mem_univ, iff_true]
      apply (hmem s).mpr
      rw [heq]
      exact keyApex_mem_sideFace a u s
    have hsize : S.card = m * 2 := by
      rw [hS]
      simp [Side]
    rw [hsize] at hcard
    omega
  have hpositive : 0 < S.card := Finset.card_pos.mpr hnonempty
  by_cases hone : S.card = 1
  · obtain ⟨s, hS⟩ := Finset.card_eq_one.mp hone
    have hs : x ∈ sideFace a u s := (hmem s).mp (by simp [hS])
    have hstrict : ∀ t : Side m, t ≠ s →
        branchProfile J u s x < branchProfile J u t x := by
      intro t hts
      apply branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace a u s t x hs
      intro ht
      have := (hmem t).mpr ht
      simp [hS, hts] at this
    by_cases hzero : branchProfile J u s x = 0
    · right
      left
      refine ⟨s, ⟨hs, normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
        a u s x hs hzero⟩, hzero, ?_⟩
      intro t hts
      simpa only [hzero] using hstrict t hts
    · left
      refine ⟨s, lt_of_le_of_ne hs.2.1 (Ne.symm hzero), ?_⟩
      intro t
      exact hstrict t.val t.property
  · have htwo : S.card = 2 := by omega
    obtain ⟨s, t, hst, hS⟩ := Finset.card_eq_two.mp htwo
    have hs : x ∈ sideFace a u s := (hmem s).mp (by simp [hS])
    have ht : x ∈ sideFace a u t := (hmem t).mp (by simp [hS])
    have haxis : s.1 ≠ t.1 := by
      intro heq
      exact hapex (eq_keyApex_of_mem_sideFace_same_axis a u s t x hs ht hst heq)
    have hzero : branchProfile J u s x ≠ 0 := by
      intro hz
      have hn := hbase (normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
        a u s x hs hz)
      exact haxis (side_axes_eq_of_carrier_and_side_normals_mem_span_pair
        a u s t p q hn (hside s hs) (hside t ht))
    right
    right
    refine ⟨s, t, haxis, ⟨hs, ht⟩, lt_of_le_of_ne hs.2.1 (Ne.symm hzero),
      le_antisymm (hs.2.2 t) (ht.2.2 s), ?_⟩
    intro r hrs hrt
    apply branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace a u s r x hs
    intro hr
    have := (hmem r).mpr hr
    simp [hS, hrs, hrt] at this

#print axioms keyGraph_transverse_stratum_classification

end
end PhysicalRegistration.NativeChair
