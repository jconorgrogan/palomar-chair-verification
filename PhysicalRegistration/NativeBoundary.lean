module

public import PhysicalRegistration.KeyCreaseGeometry

@[expose] public section

/-!
# Actual native boundary and affine side neighborhoods

These statements bind the literal crease/side sets to the physical body's
boundary. The local membership equivalence is proved from native tube
separation and zero-height compatibility, rather than postulated.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

/-- Every literal key-graph point has an actual open neighborhood on which
the assembled body equals that site's full zero-extended hypograph. -/
theorem body_locally_eq_siteHypograph {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (x : Space m) (hx : x ∈ keyGraph a u) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ body a ↔ y ∈ siteHypograph a u := by
  obtain ⟨V, hVopen, hxV, hVother⟩ := exists_isolating_open_tube
    (closedTube J) (closedTube_isClosed J) (closedTube_pairwise_disjoint hm) u hx.1
  let W : Set (Space m) := {y | |normalCoord u y| < rho m}
  have hnormalcont : Continuous (normalCoord u) := by unfold normalCoord; fun_prop
  have hWopen : IsOpen W := isOpen_lt hnormalcont.abs continuous_const
  let U := V ∩ facetNeighborhood u.1 ∩ W
  have hUopen : IsOpen U := (hVopen.inter (facetNeighborhood_isOpen u.1)).inter hWopen
  have hxU : x ∈ U := by
    refine ⟨⟨hxV, closedTube_subset_facetNeighborhood u hx.1⟩, ?_⟩
    change |normalCoord u x| < rho m
    rw [hx.2]
    exact siteHeight_abs_lt_rho a u x
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  rw [body_eq_replaceTubes]
  apply replaceTubes_local_iff (carrier m) (closedTube J) (siteHypograph a) u U
  · intro v hv
    exact (hVother v hv).mono_left (fun _ hz => hz.1.1)
  · intro z hz hzTube
    exact keyed_tube_boundary_compatibility (carrier m) U
      (siteCenter u) (outward u.1) (outward_unit _) (siteAxis u) (siteAxis_unit u)
      (eta m) (rho m) (a.value u : ℝ) (denominator m J : ℝ) (eta_pos m)
      (pMinus J) (pPlus J) (pMinus_pos J) (pPlus_pos J)
      (fun w hw => by
        change w ∈ carrier m ↔ normalCoord u w ≤ 0
        rw [normalCoord_eq_facet]
        exact mem_carrier_local_halfspace u.1 w hw.1.2)
      (fun w hw => hw.2) z hz hzTube
  · exact hy

/-- A short literal normal segment crosses the physical boundary exactly at
its graph point, including crease junctions and the apex. -/
theorem keyGraph_normal_crossing {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (x : Space m) (hx : x ∈ keyGraph a u) :
    ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      (x + t • outward u.1 ∈ body a ↔ t ≤ 0) := by
  obtain ⟨U, hU, hxU, heq⟩ := body_locally_eq_siteHypograph hm a u x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  refine ⟨ε, hε, ?_⟩
  intro t ht
  have hyU : x + t • outward u.1 ∈ U := hball (by
    simpa [Metric.mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs] using ht)
  rw [heq _ hyU]
  change normalCoord u (x + t • outward u.1) ≤ siteHeight a u (x + t • outward u.1) ↔ _
  rw [siteHeight_normal_shift]
  have hn : normalCoord u (x + t • outward u.1) = normalCoord u x + t := by
    simp [normalCoord, inner_sub_right, inner_add_right, real_inner_smul_right]
    ring
  rw [hn, hx.2]
  constructor <;> intro h <;> linarith

/-- The native key graph is genuinely on the actual body's topological boundary. -/
theorem keyGraph_subset_frontier_body {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) : keyGraph a u ⊆ frontier (body a) := by
  intro x hx
  rw [frontier, (body_isClosed a).closure_eq]
  refine ⟨?_, ?_⟩
  · exact Or.inr (mem_iUnion.mpr ⟨u, hx.1, hx.2.le⟩)
  · intro hxint
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hxint
    obtain ⟨ε, hε, hcross⟩ := keyGraph_normal_crossing hm a u x hx
    let t := min r ε / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have htr : t < r := by dsimp [t]; have := min_le_left r ε; linarith
    have htε : |t| < ε := by rw [abs_of_pos ht]; dsimp [t]; have := min_le_right r ε; linarith
    have hyint : x + t • outward u.1 ∈ interior (body a) := hball (by
      simpa [Metric.mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht] using htr)
    have := (hcross t htε).mp (interior_subset hyint)
    linarith

/-- The explicitly open region where one positive branch is uniquely active. -/
def strictBranchRegion {m : ℕ} (J : ℕ) (u : Site m) (s : Side m) : Set (Space m) :=
  {x | 0 < branchProfile J u s x ∧
    ∀ t : {t : Side m // t ≠ s}, branchProfile J u s x < branchProfile J u t.val x}

theorem strictBranchRegion_isOpen {m : ℕ} (J : ℕ) (u : Site m) (s : Side m) :
    IsOpen (strictBranchRegion J u s) := by
  unfold strictBranchRegion
  simp only [ofPred_and, ofPred_forall]
  exact (isOpen_lt continuous_const (branchProfile_continuous J u s)).inter
    (isOpen_iInter_of_finite (fun t => isOpen_lt
      (branchProfile_continuous J u s) (branchProfile_continuous J u t.val)))

theorem strictBranchRegion_subset {m : ℕ} (J : ℕ) (u : Site m) (s : Side m) :
    strictBranchRegion J u s ⊆ branchRegion J u s := by
  intro x hx
  refine ⟨hx.1.le, ?_⟩
  intro t
  by_cases h : t = s
  · rw [h]
  · exact (hx.2 ⟨t, h⟩).le

/-- At a strict active side point the actual bounded body has exactly the
computed affine halfspace germ. The normal is the one used by angle separation. -/
theorem body_locally_eq_side_halfspace {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (s : Side m) (x : Space m)
    (hx : x ∈ keyGraph a u) (hxs : x ∈ strictBranchRegion J u s) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      y ∈ body a ↔ ⟪sideNormal a u s, y - siteCenter u⟫_ℝ ≤
        eta m * (a.value u : ℝ) / denominator m J := by
  obtain ⟨V, hV, hxV, heq⟩ := body_locally_eq_siteHypograph hm a u x hx
  refine ⟨V ∩ strictBranchRegion J u s, hV.inter (strictBranchRegion_isOpen J u s),
    ⟨hxV, hxs⟩, ?_⟩
  intro y hy
  rw [heq y hy.1]
  change normalCoord u y ≤ siteHeight a u y ↔ _
  rw [siteHeight_eq_sideHeight a u s y (strictBranchRegion_subset J u s hy.2)]
  simp only [sideHeight, sideNormal, inner_sub_left, real_inner_smul_left]
  change normalCoord u y ≤ _ + sideSlope a u s * tangentCoord u y s.1 ↔
    normalCoord u y - sideSlope a u s * tangentCoord u y s.1 ≤ _
  constructor <;> intro h <;> linarith

#print axioms body_locally_eq_siteHypograph
#print axioms keyGraph_normal_crossing
#print axioms keyGraph_subset_frontier_body
#print axioms body_locally_eq_side_halfspace
end
end PhysicalRegistration.NativeChair
