module

public import ProductClosure.NativeCompiler
public import ProductClosure.NativeTubeSeparation
public import PhysicalRegistration.KeyTube

@[expose] public section

/-!
Topological facts and local chart binding for the literal finite native body.
The native contact graph and whole-key matching theorem remain separate.
-/

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

theorem carrier_isClosed (S : Finset (Polycube.LatticeIndex (m + 1))) :
    IsClosed (Polycube.carrier S) := (Polycube.carrier_compact S).isClosed

def facetNeighborhood (f : Facet S) : Set (Space m) := Polycube.facetNeighborhood f

theorem facetNeighborhood_isOpen (f : Facet S) : IsOpen (facetNeighborhood f) :=
  Polycube.facetNeighborhood_isOpen f

theorem mem_carrier_local_halfspace (f : Facet S) (x : Space m)
    (hx : x ∈ facetNeighborhood f) :
    x ∈ Polycube.carrier S ↔ ⟪outward f, x - facetCenter f⟫_ℝ ≤ 0 :=
  Polycube.mem_carrier_local_halfspace f x hx

theorem closedTube_isClosed  [NeZero m] (J : ℕ) (u : Site S) :
    IsClosed (closedTube J u) :=
  centeredKeyTube_isClosed (siteCenter u) (outward u.1) (outward_unit _)
    (siteAxis u) (siteAxis_unit u) (eta m) (rho m) (pMinus J) (pPlus J)

theorem siteHypograph_isClosed {J : ℕ} [NeZero m] (a : Coefficients S J)
    (u : Site S) : IsClosed (siteHypograph a u) := by
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

theorem body_eq_replaceTubes {J : ℕ} [NeZero m] (a : Coefficients S J) :
    body a = replaceTubes (Polycube.carrier S) (closedTube J) (siteHypograph a) := rfl

theorem body_isClosed {J : ℕ} [NeZero m] (a : Coefficients S J) :
    IsClosed (body a) := by
  rw [body_eq_replaceTubes]
  exact replaceTubes_isClosed (Polycube.carrier S) (closedTube J) (siteHypograph a)
    (carrier_isClosed S) (closedTube_isClosed J) (siteHypograph_isClosed a)

theorem closedTube_isCompact  [NeZero m] (J : ℕ) (u : Site S) :
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

theorem body_isCompact {J : ℕ} [NeZero m] (a : Coefficients S J) :
    IsCompact (body a) :=
  ((Polycube.carrier_compact S).diff (isOpen_iUnion fun _ => isOpen_interior)).union
    (isCompact_iUnion fun u : Site S => (closedTube_isCompact J u).inter_right
      (siteHypograph_isClosed a u))

theorem rho_lt_quarter (m : ℕ) : rho m < 1 / 4 := by
  unfold rho
  apply (div_lt_iff₀ (by positivity : 0 < 32 * ((m : ℝ) + 1))).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- Local chart binding to the actual finite assembled set. All analytic
tent, prime-size, and tangent-frame hypotheses are discharged here.
The remaining neighborhood assumptions are stated explicitly. -/
def body_local_graph_on_neighborhood {J : ℕ} [NeZero m]
    (a : Coefficients S J) (u : Site S) (U : Set (Space m))
    (hU : IsOpen U) (x : Space m) (hxU : x ∈ U)
    (hxgraph : normalCoord u x = siteHeight a u x)
    (hother : ∀ v, v ≠ u → Disjoint U (closedTube J v))
    (hflat : ∀ y ∈ U, y ∈ Polycube.carrier S ↔ normalCoord u y ≤ 0)
    (hstrip : ∀ y ∈ U, |normalCoord u y| < rho m) :
    LocalLipschitzGraphAt (body a) x ((J : ℝ) * pMax m J / denominator m J) := by
  rw [body_eq_replaceTubes]
  exact keyed_replacement_local_graph (Polycube.carrier S) (closedTube J) (siteHypograph a) u
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
theorem closedTube_subset_facetNeighborhood {J : ℕ} (u : Site S) :
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
  change |x k - facetCenter u.1 k| < 1 / 2
  rw [hid]
  have htri := abs_add_le (x k - siteCenter u k) (siteOffset u k)
  have hr := rho_lt_quarter m
  linarith

/-- The literal bounded keyed chair has a proved local inward chart at every
point of every native key graph. Tube separation, the flat carrier chart,
normal-strip margins, and boundary compatibility are all discharged. -/
def body_key_local_graph {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients S J) (u : Site S) (x : Space m)
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


end
end ProductClosure.NativeCompiler
