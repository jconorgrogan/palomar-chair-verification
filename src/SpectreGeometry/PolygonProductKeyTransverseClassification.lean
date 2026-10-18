module

public import SpectreGeometry.PolygonProductKeyNormalRank
public import SpectreGeometry.PolygonProductKeyGenericRidgeSectors

@[expose] public section


/-!
# Actual product-key strata under a two-normal transverse bound

The active-footprint classification explicitly assumes that all six literal
branch profiles are nonnegative. The actual graph and its collar window also
contain the zero extension outside that footprint, so the unrestricted theorem
retains a negative-profile alternative. That alternative has locally zero
height. All exclusions of higher-order active strata follow from the computed
normal ranks and the actual opposite-branch profile algebra.
-/

namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration Set
open scoped InnerProductSpace
noncomputable section

/-- One positive branch strictly below each of the other five branches. -/
def strictBranchRegion (u : ProductKeySite) (s : ProductKeySide) : Set EFour :=
  {x | 0 < productKeyBranchProfile u s x ∧
    ∀ t : {t : ProductKeySide // t ≠ s},
      productKeyBranchProfile u s x < productKeyBranchProfile u t.val x}

theorem strictBranchRegion_isOpen (u : ProductKeySite) (s : ProductKeySide) :
    IsOpen (strictBranchRegion u s) := by
  unfold strictBranchRegion
  simp only [ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const (branchProfile_continuous u s)).inter
    (isOpen_iInter_of_finite fun t => isOpen_lt
      (branchProfile_continuous u s) (branchProfile_continuous u t.val))

theorem strictBranchRegion_subset (u : ProductKeySite) (s : ProductKeySide) :
    strictBranchRegion u s ⊆ productKeyBranchRegion u s := by
  intro x hx
  refine ⟨hx.1.le, ?_⟩
  intro t
  by_cases h : t = s
  · rw [h]
  · exact (hx.2 ⟨t, h⟩).le

/-- Nonnegative profiles admit an active minimum, including at zero height. -/
theorem exists_active_branch_of_profiles_nonnegative (u : ProductKeySite) (x : EFour)
    (hnonneg : ∀ s, 0 ≤ productKeyBranchProfile u s x) :
    ∃ s : ProductKeySide, x ∈ productKeyBranchRegion u s := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := ProductKeySide)) (fun s => productKeyBranchProfile u s x)
  refine ⟨s, hnonneg s, ?_⟩
  intro t
  rw [← hs]
  exact Finset.inf'_le _ (Finset.mem_univ t)

/-- An inactive branch is strictly above any active branch at a graph point. -/
theorem branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace
    (u : ProductKeySite) (s t : ProductKeySide) (x : EFour)
    (hs : x ∈ productKeySideFace u s) (ht : x ∉ productKeySideFace u t) :
    productKeyBranchProfile u s x < productKeyBranchProfile u t x := by
  apply lt_of_le_of_ne (hs.2.2 t)
  intro heq
  apply ht
  refine ⟨hs.1, ?_, ?_⟩
  · exact heq ▸ hs.2.1
  · intro r
    exact heq ▸ hs.2.2 r

/-- A zero active profile has zero normal height, for either coefficient sign. -/
theorem normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
    (u : ProductKeySite) (s : ProductKeySide) (x : EFour)
    (hs : x ∈ productKeySideFace u s) (hzero : productKeyBranchProfile u s x = 0) :
    normalCoord u x = 0 := by
  have hheight : normalCoord u x =
      (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN) *
        productKeyBranchProfile u s x :=
    hs.1.trans ((product_key_height_eq_side_height u s x hs.2).trans
      (ProductCreaseSectors.sideHeight_eq_scaled_branch u s x))
  simpa only [hzero, mul_zero] using hheight

/-- Opposite affine profiles can coincide only at their common value one. -/
theorem opposite_branchProfiles_eq_one_of_eq (u : ProductKeySite)
    (i : Fin 3) (x : EFour)
    (h : productKeyBranchProfile u (i, false) x = productKeyBranchProfile u (i, true) x) :
    productKeyBranchProfile u (i, false) x = 1 ∧
      productKeyBranchProfile u (i, true) x = 1 := by
  fin_cases i <;>
    norm_num [productKeyBranchProfile, productKeyPrime, productKeyPrimePairs,
      productKeyEta, div_eq_mul_inv] at h ⊢ <;> nlinarith

/-- If both profiles on an axis are at least one, each is exactly one. -/
theorem branchProfile_eq_one_of_opposite_ge_one (u : ProductKeySite)
    (i : Fin 3) (x : EFour)
    (hfalse : 1 ≤ productKeyBranchProfile u (i, false) x)
    (htrue : 1 ≤ productKeyBranchProfile u (i, true) x) (b : Bool) :
    productKeyBranchProfile u (i, b) x = 1 := by
  fin_cases i <;> cases b <;>
    norm_num [productKeyBranchProfile, productKeyPrime, productKeyPrimePairs,
      productKeyEta, div_eq_mul_inv] at hfalse htrue ⊢ <;> linarith

/-- Distinct active sides on one axis force every one of the six sides active.
This uses only the literal affine profile algebra, without an apex or rank
assumption. -/
theorem mem_all_sideFaces_of_mem_sideFaces_same_axis (u : ProductKeySite)
    (s t : ProductKeySide) (x : EFour)
    (hs : x ∈ productKeySideFace u s) (ht : x ∈ productKeySideFace u t)
    (hst : s ≠ t) (haxis : s.1 = t.1) :
    ∀ r : ProductKeySide, x ∈ productKeySideFace u r := by
  have hone : productKeyBranchProfile u s x = 1 := by
    rcases s with ⟨i, b⟩
    rcases t with ⟨j, c⟩
    simp only at haxis
    subst j
    cases b <;> cases c
    · exact (hst rfl).elim
    · exact (opposite_branchProfiles_eq_one_of_eq u i x
        (le_antisymm (hs.2.2 (i, true)) (ht.2.2 (i, false)))).1
    · exact (opposite_branchProfiles_eq_one_of_eq u i x
        (le_antisymm (ht.2.2 (i, true)) (hs.2.2 (i, false)))).2
    · exact (hst rfl).elim
  have hlower : ∀ r, 1 ≤ productKeyBranchProfile u r x := by
    intro r
    simpa only [hone] using hs.2.2 r
  have hall : ∀ r, productKeyBranchProfile u r x = 1 := by
    rintro ⟨i, b⟩
    exact branchProfile_eq_one_of_opposite_ge_one u i x
      (hlower (i, false)) (hlower (i, true)) b
  intro r
  refine ⟨hs.1, ?_, ?_⟩
  · rw [hall r]
    norm_num
  · intro v
    rw [hall r, hall v]

/-- The active-footprint classification: every incident side normal lies in an
arbitrary two-vector span, and the outward normal does too at zero height. The
spanning vectors need not be independent. Nonnegativity is an explicit premise,
not an inference from the larger, zero-extended graph window. -/
theorem keyGraph_transverse_stratum_classification (u : ProductKeySite)
    (x p q : EFour) (hx : x ∈ productKeyGraph u)
    (hnonneg : ∀ s, 0 ≤ productKeyBranchProfile u s x)
    (hside : ∀ s : ProductKeySide, x ∈ productKeySideFace u s →
      productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour))
    (hbase : normalCoord u x = 0 →
      productKeyOutwardNormal u ∈ Submodule.span ℝ ({p, q} : Set EFour)) :
    (∃ s : ProductKeySide, x ∈ strictBranchRegion u s) ∨
    (∃ s : ProductKeySide, x ∈ baseGeneric u s) ∨
    (∃ s t : ProductKeySide, s.1 ≠ t.1 ∧ x ∈ sideGeneric u s t) := by
  classical
  let S : Finset ProductKeySide := Finset.univ.filter (fun s => x ∈ productKeySideFace u s)
  have hmem : ∀ s : ProductKeySide, s ∈ S ↔ x ∈ productKeySideFace u s := by
    intro s
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  have hnonempty : S.Nonempty := by
    obtain ⟨s, hs⟩ := exists_active_branch_of_profiles_nonnegative u x hnonneg
    exact ⟨s, (hmem s).mpr ⟨hx, hs⟩⟩
  have hcard : S.card ≤ 2 := side_labels_in_span_pair_card_le_two u S p q
    (fun s hs => hside s ((hmem s).mp hs))
  have haxis : ∀ s t : ProductKeySide, x ∈ productKeySideFace u s →
      x ∈ productKeySideFace u t → s ≠ t → s.1 ≠ t.1 := by
    intro s t hs ht hst heq
    have hall := mem_all_sideFaces_of_mem_sideFaces_same_axis u s t x hs ht hst heq
    have hS : S = Finset.univ := by
      ext r
      simp only [Finset.mem_univ, iff_true]
      exact (hmem r).mpr (hall r)
    have hsize : S.card = 6 := by
      rw [hS]
      decide
    omega
  have hpositive : 0 < S.card := Finset.card_pos.mpr hnonempty
  by_cases hone : S.card = 1
  · obtain ⟨s, hS⟩ := Finset.card_eq_one.mp hone
    have hs : x ∈ productKeySideFace u s := (hmem s).mp (by simp [hS])
    have hstrict : ∀ t : ProductKeySide, t ≠ s →
        productKeyBranchProfile u s x < productKeyBranchProfile u t x := by
      intro t hts
      apply branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace u s t x hs
      intro ht
      have := (hmem t).mpr ht
      simp [hS, hts] at this
    by_cases hzero : productKeyBranchProfile u s x = 0
    · right
      left
      refine ⟨s, ⟨hs, normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
        u s x hs hzero⟩, ?_⟩
      intro t hts
      simpa only [hzero] using hstrict t hts
    · left
      refine ⟨s, lt_of_le_of_ne hs.2.1 (Ne.symm hzero), ?_⟩
      intro t
      exact hstrict t.val t.property
  · have htwo : S.card = 2 := by omega
    obtain ⟨s, t, hst, hS⟩ := Finset.card_eq_two.mp htwo
    have hs : x ∈ productKeySideFace u s := (hmem s).mp (by simp [hS])
    have ht : x ∈ productKeySideFace u t := (hmem t).mp (by simp [hS])
    have hstaxis : s.1 ≠ t.1 := haxis s t hs ht hst
    have hzero : productKeyBranchProfile u s x ≠ 0 := by
      intro hz
      have hn := hbase (normalCoord_eq_zero_of_mem_sideFace_of_branchProfile_eq_zero
        u s x hs hz)
      exact hstaxis (side_axes_eq_of_outward_and_side_normals_mem_span_pair
        u s t p q hn (hside s hs) (hside t ht))
    right
    right
    refine ⟨s, t, hstaxis, ⟨hs, ht⟩, lt_of_le_of_ne hs.2.1 (Ne.symm hzero), ?_⟩
    intro r hrs hrt
    apply branchProfile_lt_of_mem_sideFace_of_not_mem_sideFace u s r x hs
    intro hr
    have := (hmem r).mpr hr
    simp [hS, hrs, hrt] at this

/-- The unrestricted actual graph includes a flat zero-extension alternative
outside the footprint, in addition to the three active strata. -/
theorem keyGraph_transverse_stratum_classification_or_negative (u : ProductKeySite)
    (x p q : EFour) (hx : x ∈ productKeyGraph u)
    (hside : ∀ s : ProductKeySide, x ∈ productKeySideFace u s →
      productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour))
    (hbase : normalCoord u x = 0 →
      productKeyOutwardNormal u ∈ Submodule.span ℝ ({p, q} : Set EFour)) :
    (∃ s : ProductKeySide, productKeyBranchProfile u s x < 0) ∨
    (∃ s : ProductKeySide, x ∈ strictBranchRegion u s) ∨
    (∃ s : ProductKeySide, x ∈ baseGeneric u s) ∨
    (∃ s t : ProductKeySide, s.1 ≠ t.1 ∧ x ∈ sideGeneric u s t) := by
  by_cases hnegative : ∃ s : ProductKeySide, productKeyBranchProfile u s x < 0
  · exact Or.inl hnegative
  · right
    apply keyGraph_transverse_stratum_classification u x p q hx _ hside hbase
    intro s
    exact le_of_not_gt (fun hs => hnegative ⟨s, hs⟩)

/-- In particular, membership in the actual graph window does not remove the
negative-profile alternative. -/
theorem keyGraphWindow_transverse_stratum_classification (u : ProductKeySite)
    (x p q : EFour) (hx : x ∈ productKeyGraphWindow u)
    (hside : ∀ s : ProductKeySide, x ∈ productKeySideFace u s →
      productKeySideNormal u s ∈ Submodule.span ℝ ({p, q} : Set EFour))
    (hbase : normalCoord u x = 0 →
      productKeyOutwardNormal u ∈ Submodule.span ℝ ({p, q} : Set EFour)) :
    (∃ s : ProductKeySide, productKeyBranchProfile u s x < 0) ∨
    (∃ s : ProductKeySide, x ∈ strictBranchRegion u s) ∨
    (∃ s : ProductKeySide, x ∈ baseGeneric u s) ∨
    (∃ s t : ProductKeySide, s.1 ≠ t.1 ∧ x ∈ sideGeneric u s t) :=
  keyGraph_transverse_stratum_classification_or_negative u x p q hx.1 hside hbase

/-- Any negative branch forces the actual zero-extended height to be zero. -/
theorem height_eq_zero_of_negative_branchProfile (u : ProductKeySite)
    (s : ProductKeySide) (x : EFour) (hs : productKeyBranchProfile u s x < 0) :
    productKeyHeight u (x-productKeyCenter u) = 0 := by
  classical
  obtain ⟨t, _, ht⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := ProductKeySide)) (fun t => productKeyBranchProfile u t x)
  have hmin : ∀ r, productKeyBranchProfile u t x ≤ productKeyBranchProfile u r x := by
    intro r
    rw [← ht]
    exact Finset.inf'_le _ (Finset.mem_univ r)
  have hnegative : productKeyBranchProfile u t x < 0 := lt_of_le_of_lt (hmin s) hs
  unfold productKeyHeight keyHeight
  rw [ProductCreaseSectors.native_profile_eq_max_of_minimal u t x hmin,
    max_eq_left hnegative.le, mul_zero]

/-- A strictly negative profile persists on an open neighborhood where the
height is identically zero. The corresponding material germ can be obtained
by intersecting this neighborhood with the actual collar interior. -/
theorem locally_height_eq_zero_of_negative_branchProfile (u : ProductKeySite)
    (s : ProductKeySide) (x : EFour) (hs : productKeyBranchProfile u s x < 0) :
    ∃ U : Set EFour, IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, productKeyHeight u (y-productKeyCenter u) = 0 := by
  exact ⟨{y | productKeyBranchProfile u s y < 0},
    isOpen_lt (branchProfile_continuous u s) continuous_const, hs,
    fun y hy => height_eq_zero_of_negative_branchProfile u s y hy⟩

end
end SpectreGeometry.ProductCrease
