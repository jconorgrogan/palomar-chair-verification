module

public import PhysicalRegistration.NativeChair
public import PhysicalRegistration.NativeTubeSeparation
public import PhysicalRegistration.KeyTube

@[expose] public section


/-!
Topological facts and local chart binding for the literal finite native body.
The native contact graph and whole-key matching theorem remain separate.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

theorem unitCell_isClosed {m : ℕ} (a : Cell m) : IsClosed (unitCell a) := by
  simp only [unitCell, ofPred_forall, ofPred_and]
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (PiLp.continuous_apply 2 (fun _ : Fin (m+1) => ℝ) i)).inter
    (isClosed_le (PiLp.continuous_apply 2 (fun _ : Fin (m+1) => ℝ) i) continuous_const)

theorem unitCell_isCompact {m : ℕ} (a : Cell m) : IsCompact (unitCell a) := by
  exact unitCell_compact a

theorem carrier_isClosed (m : ℕ) : IsClosed (carrier m) :=
  isClosed_iUnion_of_finite unitCell_isClosed

theorem carrier_isCompact (m : ℕ) : IsCompact (carrier m) :=
  carrier_compact m

theorem closedTube_isClosed {m : ℕ} [NeZero m] (J : ℕ) (u : Site m) :
    IsClosed (closedTube J u) :=
  centeredKeyTube_isClosed (siteCenter u) (outward u.1) (outward_unit _)
    (siteAxis u) (siteAxis_unit u) (eta m) (rho m) (pMinus J) (pPlus J)

theorem siteHypograph_isClosed {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) : IsClosed (siteHypograph a u) := by
  have hN : 0 < (denominator m J : ℝ) := by
    exact_mod_cast (denominator_prime m J).pos
  have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg _
  have hP : 0 ≤ (pMax m J : ℝ) := Nat.cast_nonneg _
  apply centeredGraphHypograph_isClosed (siteCenter u) (outward u.1) (outward_unit _)
    (keyHeight (eta m) (a.value u : ℝ) (denominator m J : ℝ)
      (pMinus J) (pPlus J) (siteAxis u))
    ((J : ℝ) * pMax m J / denominator m J) (div_nonneg (mul_nonneg hJ hP) hN.le)
  exact keyHeight_lipschitz (eta m) (a.value u : ℝ) (denominator m J : ℝ)
    (J : ℝ) (pMax m J : ℝ) (eta_pos m) hN (a.bound u) hP
    (pMinus J) (pPlus J) (siteAxis u)
    (fun j => ⟨(pMinus_pos J j).le, pMinus_le_pMax J j⟩)
    (fun j => ⟨(pPlus_pos J j).le, pPlus_le_pMax J j⟩) (siteAxis_unit u)

theorem body_eq_replaceTubes {m J : ℕ} [NeZero m] (a : Coefficients m J) :
    body a = replaceTubes (carrier m) (closedTube J) (siteHypograph a) := rfl

theorem body_isClosed {m J : ℕ} [NeZero m] (a : Coefficients m J) :
    IsClosed (body a) := by
  rw [body_eq_replaceTubes]
  exact replaceTubes_isClosed (carrier m) (closedTube J) (siteHypograph a)
    (carrier_isClosed m) (closedTube_isClosed J) (siteHypograph_isClosed a)

theorem closedTube_isCompact {m : ℕ} [NeZero m] (J : ℕ) (u : Site m) :
    IsCompact (closedTube J u) := by
  let B : Set (Space m) := {x | ∀ k,
    x k ∈ Set.Icc (siteCenter u k - rho m) (siteCenter u k + rho m)}
  have hB : IsCompact B :=
    (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)).isCompact_preimage.mpr
      (isCompact_pi_infinite fun _ => isCompact_Icc)
  apply hB.of_isClosed_subset (closedTube_isClosed J u)
  intro x hx
  have henc := closedTube_mem_coordinateTube u x hx
  intro k
  have hk : |x k - siteCenter u k| ≤ rho m := by
    by_cases hki : k = normalIndex u.1
    · subst k
      exact henc.1
    · exact (henc.2 k hki).trans (eta_lt_rho m).le
  have hh := abs_le.mp hk
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem body_isCompact {m J : ℕ} [NeZero m] (a : Coefficients m J) :
    IsCompact (body a) :=
  ((carrier_compact m).diff (isOpen_iUnion fun _ => isOpen_interior)).union
    (isCompact_iUnion fun u : Site m => (closedTube_isCompact J u).inter_right
      (siteHypograph_isClosed a u))

def halfPoint (m : ℕ) : Space m := WithLp.toLp 2 (fun _ => 1 / 2)

theorem rho_lt_quarter (m : ℕ) : rho m < 1 / 4 := by
  unfold rho
  apply (div_lt_iff₀ (by positivity : 0 < 32 * ((m : ℝ) + 1))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

theorem halfPoint_mem_carrier (m : ℕ) : halfPoint m ∈ carrier m := by
  rw [mem_carrier_iff]
  constructor
  · intro i
    norm_num [halfPoint]
  · exact ⟨0, by norm_num [halfPoint]⟩

theorem halfPoint_not_mem_closedTube {m J : ℕ} (u : Site m) :
    halfPoint m ∉ closedTube J u := by
  intro hx
  have henc := closedTube_mem_coordinateTube u (halfPoint m) hx
  have hnear : |(1 / 2 : ℝ) - (facetPlane u.1 : ℝ)| ≤ rho m := by
    simpa [halfPoint, siteCenter_normal] using henc.1
  have hfar := native_tangent_distance_from_integer (0 : ℤ) (facetPlane u.1)
    (0 : ℝ) 0 0 (by norm_num) (by norm_num)
  have hr := rho_lt_quarter m
  norm_num at hfar
  linarith

theorem halfPoint_mem_body {m J : ℕ} [NeZero m] (a : Coefficients m J) :
    halfPoint m ∈ body a := by
  rw [body_eq_replaceTubes]
  apply replaceTubes_mem_of_untouched _ _ _ (halfPoint_mem_carrier m)
  intro u hu
  exact halfPoint_not_mem_closedTube u (interior_subset hu)

theorem body_nonempty {m J : ℕ} [NeZero m] (a : Coefficients m J) :
    (body a).Nonempty := ⟨halfPoint m, halfPoint_mem_body a⟩

/-- Local chart binding to the actual finite assembled set. All analytic
tent, prime-size, and tangent-frame hypotheses are discharged here.
The remaining neighborhood assumptions are stated explicitly. -/
def body_local_graph_on_neighborhood {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (u : Site m) (U : Set (Space m))
    (hU : IsOpen U) (x : Space m) (hxU : x ∈ U)
    (hxgraph : normalCoord u x = siteHeight a u x)
    (hother : ∀ v, v ≠ u → Disjoint U (closedTube J v))
    (hflat : ∀ y ∈ U, y ∈ carrier m ↔ normalCoord u y ≤ 0)
    (hstrip : ∀ y ∈ U, |normalCoord u y| < rho m) :
    LocalLipschitzGraphAt (body a) x ((J : ℝ) * pMax m J / denominator m J) := by
  rw [body_eq_replaceTubes]
  exact keyed_replacement_local_graph (carrier m) (closedTube J) (siteHypograph a) u
    (siteCenter u) (outward u.1) (outward_unit _) (siteAxis u)
    (siteAxis_unit u) (siteAxis_outward_inner u)
    (eta m) (rho m) (a.value u : ℝ) (denominator m J : ℝ) (J : ℝ) (pMax m J : ℝ)
    (eta_pos m) (by exact_mod_cast (denominator_prime m J).pos)
    (a.bound u) (Nat.cast_nonneg _) (pMinus J) (pPlus J)
    (fun j => ⟨pMinus_pos J j, pMinus_le_pMax J j⟩)
    (fun j => ⟨pPlus_pos J j, pPlus_le_pMax J j⟩)
    rfl rfl U hU x hxU hxgraph hother hflat hstrip

/-- Every point of a closed native key tube is inside the genuine flat
facet neighborhood, with all ambient-coordinate margins verified. -/
theorem closedTube_subset_facetNeighborhood {m J : ℕ} (u : Site m) :
    closedTube J u ⊆ facetNeighborhood u.1 := by
  intro x hx k
  have henc := closedTube_mem_coordinateTube u x hx
  have hk : |x k - siteCenter u k| ≤ rho m := by
    by_cases hki : k = normalIndex u.1
    · subst k
      exact henc.1
    · exact (henc.2 k hki).trans (eta_lt_rho m).le
  have hoff := siteOffset_coordinate_bound u k
  have hid : x k - facetCenter u.1 k =
      (x k - siteCenter u k) + siteOffset u k := by
    simp only [siteCenter, PiLp.add_apply]
    ring
  rw [hid]
  have htri := abs_add_le (x k - siteCenter u k) (siteOffset u k)
  have hr := rho_lt_quarter m
  linarith

/-- The literal bounded keyed chair has a proved local inward chart at every
point of every native key graph. Tube separation, the flat carrier chart,
normal-strip margins, and boundary compatibility are all discharged. -/
def body_key_local_graph {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (u : Site m) (x : Space m)
    (hxTube : x ∈ closedTube J u) (hxgraph : normalCoord u x = siteHeight a u x) :
    LocalLipschitzGraphAt (body a) x ((J : ℝ) * pMax m J / denominator m J) := by
  let hiso := exists_isolating_open_tube (closedTube J) (closedTube_isClosed J)
    (closedTube_pairwise_disjoint hm) u hxTube
  let V := Classical.choose hiso
  have hVopen : IsOpen V := (Classical.choose_spec hiso).1
  have hxV : x ∈ V := (Classical.choose_spec hiso).2.1
  have hVother : ∀ v, v ≠ u → Disjoint V (closedTube J v) :=
    (Classical.choose_spec hiso).2.2
  let W : Set (Space m) := {y | |normalCoord u y| < rho m}
  have hnormalcont : Continuous (normalCoord u) :=
    (unit_inner_continuous (outward u.1) (outward_unit _)).comp
      (continuous_id.sub continuous_const)
  have hWopen : IsOpen W := isOpen_lt hnormalcont.abs continuous_const
  let U := V ∩ facetNeighborhood u.1 ∩ W
  have hUopen : IsOpen U := (hVopen.inter (facetNeighborhood_isOpen u.1)).inter hWopen
  have hxU : x ∈ U := by
    refine ⟨⟨hxV, closedTube_subset_facetNeighborhood u hxTube⟩, ?_⟩
    change |normalCoord u x| < rho m
    rw [hxgraph]
    exact siteHeight_abs_lt_rho a u x
  apply body_local_graph_on_neighborhood a u U hUopen x hxU hxgraph
  · intro v hv
    exact (hVother v hv).mono_left (fun _ hy => hy.1.1)
  · intro y hy
    rw [normalCoord_eq_facet]
    exact mem_carrier_local_halfspace u.1 y hy.1.2
  · intro y hy
    exact hy.2

theorem native_slope_lt_half (m J : ℕ) (hm : 2 ≤ m) :
    0 ≤ (J : ℝ) * pMax m J / denominator m J ∧
      (J : ℝ) * pMax m J / denominator m J < 1 / 2 := by
  by_cases hJ : J = 0
  · subst J
    norm_num
  · apply chosen_slope_lt_half ((m : ℝ) + 1) (J : ℝ)
      (pMax m J : ℝ) (denominator m J : ℝ)
    · exact_mod_cast (by omega : 3 ≤ m + 1)
    · exact_mod_cast Nat.pos_of_ne_zero hJ
    · exact_mod_cast (keyPrime_prime J (2 * m - 1)).pos
    · exact_mod_cast denominator_gt m J

#print axioms carrier_isCompact
#print axioms closedTube_isClosed
#print axioms body_isClosed
#print axioms body_isCompact
#print axioms body_nonempty
#print axioms body_local_graph_on_neighborhood
#print axioms closedTube_subset_facetNeighborhood
#print axioms body_key_local_graph
#print axioms native_slope_lt_half
end
end PhysicalRegistration.NativeChair
