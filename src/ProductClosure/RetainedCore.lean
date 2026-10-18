module

public import ProductClosure.NativeCompiler
public import ProductClosure.CarrierLocal

@[expose] public section

/-! Actual retained cores of the compiled finite polycube and explicit clamps.
All geometric inclusions are proved for the literal compiler body. -/
namespace ProductClosure.NativeCompiler
open Set
noncomputable section

variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

def retainedCore (c : Polycube.Cell S) : Set (Space m) :=
  {x | ∀ i, (c.val i : ℝ) + delta m ≤ x i ∧ x i ≤ (c.val i : ℝ) + 1 - delta m}

def openRetainedCore (c : Polycube.Cell S) : Set (Space m) :=
  {x | ∀ i, (c.val i : ℝ) + rho m < x i ∧ x i < (c.val i : ℝ) + 1 - rho m}

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

theorem core_rho_lt_quarter (m : ℕ) : rho m < 1 / 4 := by
  unfold rho
  apply (div_lt_iff₀ (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem openRetainedCore_isOpen (c : Polycube.Cell S) : IsOpen (openRetainedCore c) := by
  unfold openRetainedCore
  simp only [Set.ofPred_forall, Set.ofPred_and]
  apply isOpen_iInter_of_finite
  intro i
  apply IsOpen.inter
  · apply isOpen_lt <;> fun_prop
  · apply isOpen_lt <;> fun_prop

/-- All modification tubes stay near an integer normal plane. -/
theorem closedTube_integer_plane_bound {J : ℕ} (u : Site S) (x : Space m)
    (hx : x ∈ closedTube J u) :
    |x u.1.axis - (Polycube.facetPlane u.1 : ℝ)| ≤ rho m := by
  have hn := hx.1
  rw [abs_normalCoord] at hn
  have hcenter : siteCenter u (normalIndex u.1) = (Polycube.facetPlane u.1 : ℝ) := by
    simp only [siteCenter, PiLp.add_apply, siteOffset_normal, add_zero]
    exact Polycube.facetCenter_normal u.1
  rwa [hcenter] at hn

theorem openRetainedCore_disjoint_closedTube {J : ℕ} (c : Polycube.Cell S) (u : Site S) :
    Disjoint (openRetainedCore c) (closedTube J u) := by
  apply Set.disjoint_left.mpr
  intro x hx htube
  have hnear := abs_le.mp (closedTube_integer_plane_bound u x htube)
  have hx' := hx u.1.axis
  rcases le_total (Polycube.facetPlane u.1) (c.val u.1.axis) with hlow | hhigh
  · have hr : (Polycube.facetPlane u.1 : ℝ) ≤ c.val u.1.axis := by exact_mod_cast hlow
    linarith [hx'.1, hnear.2]
  · by_cases heq : Polycube.facetPlane u.1 = c.val u.1.axis
    · have hr : (Polycube.facetPlane u.1 : ℝ) = c.val u.1.axis := by exact_mod_cast heq
      linarith [hx'.1, hnear.2]
    · have hi : c.val u.1.axis + 1 ≤ Polycube.facetPlane u.1 := by omega
      have hr : (c.val u.1.axis : ℝ) + 1 ≤ Polycube.facetPlane u.1 := by exact_mod_cast hi
      linarith [hx'.2, hnear.1]

theorem openRetainedCore_subset_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (c : Polycube.Cell S) : openRetainedCore c ⊆ body a := by
  intro x hx
  apply Or.inl
  constructor
  · apply (Polycube.mem_carrier_iff S x).mpr
    refine ⟨c.val, c.property, fun i => ?_⟩
    have hi := hx i
    constructor <;> linarith [hi.1, hi.2, rho_pos m]
  · intro hu
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hu
    exact Set.disjoint_left.mp (openRetainedCore_disjoint_closedTube c u) hx (interior_subset hu)

theorem retainedCore_subset_interior_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (c : Polycube.Cell S) : retainedCore c ⊆ interior (body a) := by
  have hi : openRetainedCore c ⊆ interior (body a) :=
    interior_maximal (openRetainedCore_subset_body a c) (openRetainedCore_isOpen c)
  apply Subset.trans _ hi
  intro x hx i
  have hc := hx i
  constructor <;> linarith [hc.1, hc.2, rho_lt_delta m]

def clampToCore (c : Polycube.Cell S) (x : Space m) : Space m :=
  WithLp.toLp 2 (fun i => min (max (x i) ((c.val i : ℝ) + delta m))
    ((c.val i : ℝ) + 1 - delta m))

theorem clampToCore_mem (c : Polycube.Cell S) (x : Space m) :
    clampToCore c x ∈ retainedCore c := by
  intro i
  change _ ≤ min _ _ ∧ min _ _ ≤ _
  exact ⟨le_min (le_max_right _ _) (by linarith [delta_lt_half m]), min_le_right _ _⟩

theorem clampToCore_coordinate_dist_le (c : Polycube.Cell S) (x : Space m)
    (hx : x ∈ Polycube.latticeCell c.val) (i : Fin (m + 1)) :
    |clampToCore c x i - x i| ≤ delta m := by
  have hi := hx i
  have hδ := delta_pos m
  have hhalf := delta_lt_half m
  change |min (max (x i) ((c.val i : ℝ) + delta m))
    ((c.val i : ℝ) + 1 - delta m) - x i| ≤ delta m
  by_cases hlo : x i ≤ (c.val i : ℝ) + delta m
  · rw [max_eq_right hlo, min_eq_left (by linarith)]
    rw [abs_of_nonneg (by linarith)]
    linarith [hi.1]
  · rw [max_eq_left (le_of_not_ge hlo)]
    by_cases hhi : x i ≤ (c.val i : ℝ) + 1 - delta m
    · rw [min_eq_left hhi, sub_self, abs_zero]
      exact hδ.le
    · rw [min_eq_right (le_of_not_ge hhi), abs_of_nonpos (by linarith)]
      linarith [hi.2]

theorem euclidean_norm_le_sum_abs (z : Space m) : ‖z‖ ≤ ∑ i, |z i| := by
  have he : z = ∑ i, EuclideanSpace.single i (z i) := by
    ext j
    simp
  calc
    ‖z‖ = ‖∑ i, EuclideanSpace.single i (z i)‖ := congrArg norm he
    _ ≤ ∑ i, ‖EuclideanSpace.single i (z i)‖ := norm_sum_le _ _
    _ = ∑ i, |z i| := by simp

theorem clampToCore_dist_le (c : Polycube.Cell S) (x : Space m)
    (hx : x ∈ Polycube.latticeCell c.val) : dist (clampToCore c x) x ≤ 1 / 16 := by
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

/-- The actual center of any occupied cell, without a privileged zero cell. -/
def cellCenter (c : Polycube.Cell S) : Space m := Polycube.latticeCenter c.val

theorem abs_coordinate_sub_lt_of_mem_ball (x y : Space m) (r : ℝ)
    (hx : x ∈ Metric.ball y r) (i : Fin (m + 1)) : |x i - y i| < r := by
  have hi := PiLp.norm_apply_le (x - y) i
  have hx' : ‖x - y‖ < r := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hi' : |x i - y i| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using hi
  exact hi'.trans_lt hx'

theorem cellCenter_ball_subset_openRetainedCore (c : Polycube.Cell S) :
    Metric.ball (cellCenter c) (1 / 4) ⊆ openRetainedCore c := by
  intro x hx i
  have hi := abs_coordinate_sub_lt_of_mem_ball x (cellCenter c) (1 / 4) hx i
  change |x i - ((c.val i : ℝ) + 1 / 2)| < (1 / 4 : ℝ) at hi
  have hi' := abs_lt.mp hi
  constructor <;> linarith [hi'.1, hi'.2, core_rho_lt_quarter m]

/-- Every occupied cell supplies its own genuine retained radius-quarter ball. -/
theorem cellCenter_ball_subset_interior_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (c : Polycube.Cell S) :
    Metric.ball (cellCenter c) (1 / 4) ⊆ interior (body a) :=
  (cellCenter_ball_subset_openRetainedCore c).trans
    (interior_maximal (openRetainedCore_subset_body a c) (openRetainedCore_isOpen c))

theorem cellCenter_mem_interior_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (c : Polycube.Cell S) : cellCenter c ∈ interior (body a) :=
  cellCenter_ball_subset_interior_body a c (Metric.mem_ball_self (by norm_num))

theorem interior_body_nonempty {J : ℕ} [NeZero m]
    (a : Coefficients S J) (hS : S.Nonempty) : (interior (body a)).Nonempty := by
  obtain ⟨z, hz⟩ := hS
  exact ⟨cellCenter ⟨z, hz⟩, cellCenter_mem_interior_body a ⟨z, hz⟩⟩

theorem placed_cellCenter_ball_subset_interior_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (c : Polycube.Cell S) (f : Space m ≃ᵢ Space m) :
    Metric.ball (f (cellCenter c)) (1 / 4) ⊆ interior (f '' body a) := by
  rw [← f.image_ball]
  exact (Set.image_mono (cellCenter_ball_subset_interior_body a c)).trans
    (f.toHomeomorph.isOpenMap.image_interior_subset (body a))

/-- Every point of a placed carrier is close to an actual interior point of
its compiled body, with no registration assumption on the placement. -/
theorem placed_carrier_near_interior_body {J : ℕ} [NeZero m]
    (a : Coefficients S J) (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : x ∈ f '' Polycube.carrier S) :
    ∃ y ∈ interior (f '' body a), dist y x ≤ 1 / 16 := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
  refine ⟨f (clampToCore c z), ?_, ?_⟩
  · apply f.toHomeomorph.isOpenMap.image_interior_subset (body a)
    exact ⟨clampToCore c z,
      retainedCore_subset_interior_body a c (clampToCore_mem c z), rfl⟩
  · rw [f.dist_eq]
    exact clampToCore_dist_le c z hc

/-- Carrier coverage by one subfamily excludes every other physical copy.
The contradiction uses the proved clamping and retained balls. -/
theorem carrier_cover_subfamily_eq_univ {J : ℕ} [NeZero m] {ι : Type*}
    (a : Coefficients S J) (hS : S.Nonempty) (f : ι → Space m ≃ᵢ Space m)
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' body a)) (interior (f j '' body a)))
    (U : Set ι) (hcover : ∀ x : Space m, ∃ i ∈ U, x ∈ f i '' Polycube.carrier S) :
    U = univ := by
  obtain ⟨z, hz⟩ := hS
  let c : Polycube.Cell S := ⟨z, hz⟩
  apply eq_univ_of_forall
  intro j
  by_contra hj
  obtain ⟨i, hi, hx⟩ := hcover (f j (cellCenter c))
  obtain ⟨y, hyi, hydist⟩ := placed_carrier_near_interior_body a (f i) _ hx
  have hyj : y ∈ interior (f j '' body a) :=
    placed_cellCenter_ball_subset_interior_body a c (f j) (by
      rw [Metric.mem_ball]
      linarith)
  have hij : i ≠ j := by intro he; subst i; exact hj hi
  exact Set.disjoint_left.mp (hdisjoint hij) hyi hyj

end
end ProductClosure.NativeCompiler
