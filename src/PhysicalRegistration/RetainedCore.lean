module

public import PhysicalRegistration.PackingLocalFiniteness

@[expose] public section

/-! Actual retained closed cell cores and an explicit nearby core point.
The l1 estimate d*delta=1/16 is sufficient for the global radius-1/4-ball
exclusion argument, so no square-root dimension estimate is needed. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- The manuscript's literal retained closed core of an occupied unit cell. -/
def retainedCore {m : ℕ} (c : Cell m) : Set (Space m) :=
  {x | ∀ i, bit (c.val i) + delta m ≤ x i ∧ x i ≤ bit (c.val i) + 1 - delta m}

def openRetainedCore {m : ℕ} (c : Cell m) : Set (Space m) :=
  {x | ∀ i, bit (c.val i) + rho m < x i ∧ x i < bit (c.val i) + 1 - rho m}

theorem delta_pos (m : ℕ) : 0 < delta m := by unfold delta; positivity

theorem rho_lt_delta (m : ℕ) : rho m < delta m := by
  unfold rho delta
  have hm : 0 < (m : ℝ) + 1 := by positivity
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

theorem delta_lt_half (m : ℕ) : delta m < 1 / 2 := by
  unfold delta
  have hm : 0 < (m : ℝ) + 1 := by positivity
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem openRetainedCore_isOpen {m : ℕ} (c : Cell m) : IsOpen (openRetainedCore c) := by
  unfold openRetainedCore
  simp only [Set.ofPred_forall, Set.ofPred_and]
  apply isOpen_iInter_of_finite
  intro i
  apply IsOpen.inter
  · apply isOpen_lt <;> fun_prop
  · apply isOpen_lt <;> fun_prop

/-- A point with strict coordinate margin rho misses every actual tube. -/
theorem openRetainedCore_disjoint_closedTube {m J : ℕ} (c : Cell m) (u : Site m) :
    Disjoint (openRetainedCore c) (closedTube J u) := by
  apply Set.disjoint_left.mpr
  intro x hx htube
  let i := normalIndex u.1
  let b : ℤ := if c.val i then 1 else 0
  have hb : (b : ℝ) = bit (c.val i) := by dsimp [b, bit]; split <;> norm_num
  have hnear : |x i - (facetPlane u.1 : ℝ)| ≤ rho m := by
    simpa [i, siteCenter_normal] using (closedTube_mem_coordinateTube u x htube).1
  have hx' := hx i
  have hnear' := abs_le.mp hnear
  rcases le_total (facetPlane u.1) b with hlow | hhigh
  · have hr : (facetPlane u.1 : ℝ) ≤ b := by exact_mod_cast hlow
    rw [hb] at hr
    linarith [hx'.1, hnear'.2]
  · by_cases heq : facetPlane u.1 = b
    · have hr : (facetPlane u.1 : ℝ) = bit (c.val i) := by rw [heq, hb]
      rw [hr] at hnear'
      linarith [hx'.1, hnear'.2]
    · have hi : b + 1 ≤ facetPlane u.1 := by omega
      have hr : (b : ℝ) + 1 ≤ facetPlane u.1 := by exact_mod_cast hi
      rw [hb] at hr
      linarith [hx'.2, hnear'.1]

theorem openRetainedCore_subset_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (c : Cell m) : openRetainedCore c ⊆ body a := by
  intro x hx
  rw [body_eq_replaceTubes]
  apply replaceTubes_mem_of_untouched
  · refine Set.mem_iUnion.mpr ⟨c, fun i => ?_⟩
    have hi := hx i
    constructor <;> linarith [hi.1, hi.2, rho_pos m]
  · intro u hu
    exact Set.disjoint_left.mp (openRetainedCore_disjoint_closedTube c u) hx (interior_subset hu)

/-- Every retained closed core lies strictly inside the actual modified body. -/
theorem retainedCore_subset_interior_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (c : Cell m) : retainedCore c ⊆ interior (body a) := by
  have hi : openRetainedCore c ⊆ interior (body a) :=
    interior_maximal (openRetainedCore_subset_body a c) (openRetainedCore_isOpen c)
  apply Subset.trans _ hi
  intro x hx i
  have hc := hx i
  constructor <;> linarith [hc.1, hc.2, rho_lt_delta m]

/-- Coordinatewise clamping into the actual retained core. -/
def clampToCore {m : ℕ} (c : Cell m) (x : Space m) : Space m :=
  WithLp.toLp 2 (fun i => min (max (x i) (bit (c.val i) + delta m))
    (bit (c.val i) + 1 - delta m))

theorem clampToCore_mem {m : ℕ} (c : Cell m) (x : Space m) :
    clampToCore c x ∈ retainedCore c := by
  intro i
  change _ ≤ min _ _ ∧ min _ _ ≤ _
  exact ⟨le_min (le_max_right _ _) (by linarith [delta_lt_half m]), min_le_right _ _⟩

theorem clampToCore_coordinate_dist_le {m : ℕ} (c : Cell m) (x : Space m)
    (hx : x ∈ unitCell c) (i : Fin (m + 1)) :
    |clampToCore c x i - x i| ≤ delta m := by
  have hi := hx i
  have hδ := delta_pos m
  have hhalf := delta_lt_half m
  change |min (max (x i) (bit (c.val i) + delta m))
    (bit (c.val i) + 1 - delta m) - x i| ≤ delta m
  by_cases hlo : x i ≤ bit (c.val i) + delta m
  · rw [max_eq_right hlo, min_eq_left (by linarith)]
    rw [abs_of_nonneg (by linarith)]
    linarith [hi.1]
  · rw [max_eq_left (le_of_not_ge hlo)]
    by_cases hhi : x i ≤ bit (c.val i) + 1 - delta m
    · rw [min_eq_left hhi, sub_self, abs_zero]
      exact hδ.le
    · rw [min_eq_right (le_of_not_ge hhi), abs_of_nonpos (by linarith)]
      linarith [hi.2]

/-- The Euclidean norm is bounded by the sum of absolute coordinate values. -/
theorem euclidean_norm_le_sum_abs {m : ℕ} (z : Space m) :
    ‖z‖ ≤ ∑ i, |z i| := by
  have he : z = ∑ i, EuclideanSpace.single i (z i) := by
    ext j
    simp
  calc
    ‖z‖ = ‖∑ i, EuclideanSpace.single i (z i)‖ := congrArg norm he
    _ ≤ ∑ i, ‖EuclideanSpace.single i (z i)‖ := norm_sum_le _ _
    _ = ∑ i, |z i| := by simp

/-- Every point in an occupied closed cell lies within 1/16 of a retained
core point, uniformly in dimension. This is stronger than the 1/4 bound
needed to exclude a separate physical component. -/
theorem clampToCore_dist_le {m : ℕ} (c : Cell m) (x : Space m)
    (hx : x ∈ unitCell c) : dist (clampToCore c x) x ≤ 1 / 16 := by
  rw [dist_eq_norm]
  calc
    ‖clampToCore c x - x‖ ≤ ∑ i, |clampToCore c x i - x i| := by
      simpa only [PiLp.sub_apply] using euclidean_norm_le_sum_abs (clampToCore c x - x)
    _ ≤ ∑ _i : Fin (m + 1), delta m := Finset.sum_le_sum (fun i _ => clampToCore_coordinate_dist_le c x hx i)
    _ = 1 / 16 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      unfold delta
      push_cast
      field_simp

/-- Every point of an arbitrarily placed carrier is within 1/16 of an
actual interior point of its modified physical body. -/
theorem placed_carrier_near_interior_body {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : x ∈ f '' carrier m) :
    ∃ y ∈ interior (placedBody a f), dist y x ≤ 1 / 16 := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
  refine ⟨f (clampToCore c z), ?_, ?_⟩
  · apply f.toHomeomorph.isOpenMap.image_interior_subset (body a)
    exact ⟨clampToCore c z,
      retainedCore_subset_interior_body a c (clampToCore_mem c z), rfl⟩
  · rw [f.dist_eq]
    exact clampToCore_dist_le c z hc

/-- If one subfamily's actual carrier images already cover space, no other
interior-disjoint physical tile can exist. The retained ball and explicit
core-clamping bound supply the contradiction, with no component-connection
or physical-cover premise hidden in this final exclusion step. -/
theorem carrier_cover_subfamily_eq_univ {m J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients m J) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j))))
    (S : Set ι) (hcover : ∀ x : Space m, ∃ i ∈ S, x ∈ f i '' carrier m) :
    S = univ := by
  apply eq_univ_of_forall
  intro j
  by_contra hj
  obtain ⟨i, hi, hx⟩ := hcover (f j (halfPoint m))
  obtain ⟨y, hyi, hydist⟩ := placed_carrier_near_interior_body a (f i) _ hx
  have hyj : y ∈ interior (placedBody a (f j)) :=
    placedBody_retained_ball a (f j) (by
      rw [Metric.mem_ball]
      linarith)
  have hij : i ≠ j := by intro he; subst i; exact hj hi
  exact Set.disjoint_left.mp (hdisjoint hij) hyi hyj

#print axioms placed_carrier_near_interior_body
#print axioms carrier_cover_subfamily_eq_univ
#print axioms retainedCore_subset_interior_body
#print axioms clampToCore_mem
#print axioms clampToCore_coordinate_dist_le
#print axioms euclidean_norm_le_sum_abs
#print axioms clampToCore_dist_le
end
end PhysicalRegistration.NativeChair
