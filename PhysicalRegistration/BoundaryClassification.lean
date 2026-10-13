module

public import PhysicalRegistration.NativeBoundary

@[expose] public section

/-!
# Native boundary classification

The literal assembled body's boundary inside a native tube is exactly its
key graph. Every remaining boundary point has an untouched carrier germ.
All neighborhoods are constructed from the finite separated native tubes.
-/

namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

theorem siteHeight_continuous {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (u : Site m) : Continuous (siteHeight a u) := by
  let L : NNReal := ⟨(J : ℝ) * pMax m J / denominator m J, by positivity⟩
  have hLip : LipschitzWith L (siteHeight a u) := lipschitzWith_iff_norm_sub_le.mpr
    (by
      intro x y
      change ‖siteHeight a u x - siteHeight a u y‖ ≤
        ((J : ℝ) * pMax m J / denominator m J) * ‖x - y‖
      simpa only [Real.norm_eq_abs] using siteHeight_lipschitz a u x y)
  exact hLip.continuous

/-- Local equality holds at every point of the closed native tube, including
its top and bottom faces. The latter lie strictly above or below both graphs. -/
theorem body_locally_eq_siteHypograph_of_mem_closedTube {m J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients m J) (u : Site m) (x : Space m)
    (hx : x ∈ closedTube J u) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      ∀ y ∈ U, y ∈ body a ↔ y ∈ siteHypograph a u := by
  obtain ⟨V, hVopen, hxV, hVother⟩ := exists_isolating_open_tube
    (closedTube J) (closedTube_isClosed J) (closedTube_pairwise_disjoint hm) u hx
  let W : Set (Space m) := {y | |normalCoord u y| < rho m}
  let P : Set (Space m) := {y | 0 < normalCoord u y ∧ siteHeight a u y < normalCoord u y}
  let N : Set (Space m) := {y | normalCoord u y < 0 ∧ normalCoord u y < siteHeight a u y}
  have hnormalcont : Continuous (normalCoord u) := by unfold normalCoord; fun_prop
  have hWopen : IsOpen W := isOpen_lt hnormalcont.abs continuous_const
  have hPopen : IsOpen P := (isOpen_lt continuous_const hnormalcont).inter
    (isOpen_lt (siteHeight_continuous a u) hnormalcont)
  have hNopen : IsOpen N := (isOpen_lt hnormalcont continuous_const).inter
    (isOpen_lt hnormalcont (siteHeight_continuous a u))
  let U := V ∩ facetNeighborhood u.1 ∩ (W ∪ P ∪ N)
  have hUopen : IsOpen U := (hVopen.inter (facetNeighborhood_isOpen u.1)).inter
    ((hWopen.union hPopen).union hNopen)
  have hxU : x ∈ U := by
    refine ⟨⟨hxV, closedTube_subset_facetNeighborhood u hx⟩, ?_⟩
    by_cases hstrip : |normalCoord u x| < rho m
    · exact Or.inl (Or.inl hstrip)
    · have hnabs : |normalCoord u x| = rho m := le_antisymm hx.1 (le_of_not_gt hstrip)
      have hheight := abs_lt.mp (siteHeight_abs_lt_rho a u x)
      by_cases hn : 0 ≤ normalCoord u x
      · rw [abs_of_nonneg hn] at hnabs
        exact Or.inl (Or.inr ⟨by rw [hnabs]; exact rho_pos m, by linarith⟩)
      · rw [abs_of_neg (lt_of_not_ge hn)] at hnabs
        exact Or.inr ⟨lt_of_not_ge hn, by linarith⟩
  refine ⟨U, hUopen, hxU, ?_⟩
  intro y hy
  rw [body_eq_replaceTubes]
  apply replaceTubes_local_iff (carrier m) (closedTube J) (siteHypograph a) u U
  · intro v hv
    exact (hVother v hv).mono_left (fun _ hz => hz.1.1)
  · intro z hz hzTube
    have hflat : z ∈ carrier m ↔ normalCoord u z ≤ 0 := by
      rw [normalCoord_eq_facet]
      exact mem_carrier_local_halfspace u.1 z hz.1.2
    rcases hz.2 with (hzW | hzP) | hzN
    · exact keyed_tube_boundary_compatibility (carrier m) (U ∩ W)
        (siteCenter u) (outward u.1) (outward_unit _) (siteAxis u) (siteAxis_unit u)
        (eta m) (rho m) (a.value u : ℝ) (denominator m J : ℝ) (eta_pos m)
        (pMinus J) (pPlus J) (pMinus_pos J) (pPlus_pos J)
        (fun w hw => by
          change w ∈ carrier m ↔ normalCoord u w ≤ 0
          rw [normalCoord_eq_facet]
          exact mem_carrier_local_halfspace u.1 w hw.1.1.2)
        (fun w hw => hw.2) z ⟨hz, hzW⟩ hzTube
    · change z ∈ carrier m ↔ normalCoord u z ≤ siteHeight a u z
      rw [hflat]
      exact iff_of_false (not_le.mpr hzP.1) (not_le.mpr hzP.2)
    · change z ∈ carrier m ↔ normalCoord u z ≤ siteHeight a u z
      rw [hflat]
      exact iff_of_true hzN.1.le hzN.2.le
  · exact hy

/-- No additional physical boundary is created on a native tube's sides,
top, or bottom: all actual boundary points there belong to its key graph. -/
theorem frontier_body_inter_closedTube_subset_keyGraph {m J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients m J) (u : Site m) :
    frontier (body a) ∩ closedTube J u ⊆ keyGraph a u := by
  intro x hx
  obtain ⟨U, hU, hxU, heq⟩ :=
    body_locally_eq_siteHypograph_of_mem_closedTube hm a u x hx.2
  have hxbody : x ∈ body a := (body_isClosed a).closure_eq ▸ frontier_subset_closure hx.1
  have hxheight : normalCoord u x ≤ siteHeight a u x := (heq x hxU).mp hxbody
  refine ⟨hx.2, le_antisymm hxheight ?_⟩
  by_contra h
  have hstrict : normalCoord u x < siteHeight a u x := lt_of_not_ge h
  let W : Set (Space m) := {y | normalCoord u y < siteHeight a u y}
  have hW : IsOpen W := isOpen_lt (by unfold normalCoord; fun_prop)
    (siteHeight_continuous a u)
  have hsubset : U ∩ W ⊆ body a := by
    intro y hy
    apply (heq y hy.1).mpr
    change normalCoord u y ≤ siteHeight a u y
    exact le_of_lt hy.2
  have hxint : x ∈ interior (body a) :=
    interior_maximal hsubset (hU.inter hW) ⟨hxU, hstrict⟩
  exact hx.1.2 hxint

/-- The exact tube-by-tube physical boundary inventory. -/
theorem frontier_body_inter_closedTube_eq_keyGraph {m J : ℕ} [NeZero m]
    (hm : 2 ≤ m) (a : Coefficients m J) (u : Site m) :
    frontier (body a) ∩ closedTube J u = keyGraph a u := by
  apply Subset.antisymm (frontier_body_inter_closedTube_subset_keyGraph hm a u)
  intro x hx
  exact ⟨keyGraph_subset_frontier_body hm a u hx, hx.1⟩

/-- Away from every native tube the literal finite replacement leaves the
carrier unchanged on a constructed open neighborhood. -/
theorem body_locally_eq_carrier_of_not_mem_closedTube {m J : ℕ} [NeZero m]
    (a : Coefficients m J) (x : Space m) (hx : ∀ u, x ∉ closedTube J u) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ∀ u, y ∉ closedTube J u) ∧
      ∀ y ∈ U, y ∈ body a ↔ y ∈ carrier m := by
  let U : Set (Space m) := (⋃ u, closedTube J u)ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite (closedTube_isClosed J)).isOpen_compl
  have havoid : ∀ y ∈ U, ∀ u, y ∉ closedTube J u := by
    intro y hy u hyu
    exact hy (mem_iUnion.mpr ⟨u, hyu⟩)
  refine ⟨U, hU, ?_, havoid, ?_⟩
  · intro hxUnion
    obtain ⟨u, hxu⟩ := mem_iUnion.mp hxUnion
    exact hx u hxu
  · intro y hy
    rw [body_eq_replaceTubes]
    constructor
    · intro hbody
      rcases hbody with hcarrier | hp
      · exact hcarrier.1
      · obtain ⟨u, hyu, _⟩ := mem_iUnion.mp hp
        exact (havoid y hy u hyu).elim
    · intro hcarrier
      exact replaceTubes_mem_of_untouched _ _ _ hcarrier
        (fun u h => havoid y hy u (interior_subset h))

/-- Every genuine boundary point outside all key graphs is outside every
closed native tube and has an untouched carrier neighborhood. -/
theorem frontier_body_outside_keyGraphs {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (x : Space m) (hx : x ∈ frontier (body a))
    (hkey : ∀ u, x ∉ keyGraph a u) :
    (∀ u, x ∉ closedTube J u) ∧
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, ∀ u, y ∉ closedTube J u) ∧
      ∀ y ∈ U, y ∈ body a ↔ y ∈ carrier m := by
  have houtside : ∀ u, x ∉ closedTube J u := by
    intro u hxu
    exact hkey u (frontier_body_inter_closedTube_subset_keyGraph hm a u ⟨hx, hxu⟩)
  exact ⟨houtside, body_locally_eq_carrier_of_not_mem_closedTube a x houtside⟩

/-- Outside the closed tubes, actual and carrier frontiers agree as well. -/
theorem frontier_body_iff_frontier_carrier_of_not_mem_closedTube
    {m J : ℕ} [NeZero m] (a : Coefficients m J) (x : Space m)
    (hx : ∀ u, x ∉ closedTube J u) :
    x ∈ frontier (body a) ↔ x ∈ frontier (carrier m) := by
  obtain ⟨U, hU, hxU, _, heq⟩ := body_locally_eq_carrier_of_not_mem_closedTube a x hx
  have hint : x ∈ interior (body a) ↔ x ∈ interior (carrier m) := by
    constructor
    · intro hi
      have hsub : U ∩ interior (body a) ⊆ carrier m := by
        intro y hy
        exact (heq y hy.1).mp (interior_subset hy.2)
      exact interior_maximal hsub (hU.inter isOpen_interior) ⟨hxU, hi⟩
    · intro hi
      have hsub : U ∩ interior (carrier m) ⊆ body a := by
        intro y hy
        exact (heq y hy.1).mpr (interior_subset hy.2)
      exact interior_maximal hsub (hU.inter isOpen_interior) ⟨hxU, hi⟩
  rw [frontier, frontier, (body_isClosed a).closure_eq, (carrier_isClosed m).closure_eq]
  exact and_congr (heq x hxU) (not_congr hint)

/-- A complete set-theoretic boundary decomposition into native key graphs
and unchanged carrier boundary outside every closed native tube. -/
theorem frontier_body_eq_keyGraphs_union_untouched_carrier
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J) :
    frontier (body a) = (⋃ u, keyGraph a u) ∪
      (frontier (carrier m) \ ⋃ u, closedTube J u) := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hk : ∃ u, x ∈ keyGraph a u
    · exact Or.inl (mem_iUnion.mpr hk)
    · have hkey : ∀ u, x ∉ keyGraph a u := by simpa only [not_exists] using hk
      have houtside := (frontier_body_outside_keyGraphs hm a x hx hkey).1
      refine Or.inr ⟨(frontier_body_iff_frontier_carrier_of_not_mem_closedTube a x houtside).mp hx, ?_⟩
      intro ht
      obtain ⟨u, hu⟩ := mem_iUnion.mp ht
      exact houtside u hu
  · intro hx
    rcases hx with hk | hc
    · obtain ⟨u, hu⟩ := mem_iUnion.mp hk
      exact keyGraph_subset_frontier_body hm a u hu
    · apply (frontier_body_iff_frontier_carrier_of_not_mem_closedTube a x
        (fun u hu => hc.2 (mem_iUnion.mpr ⟨u, hu⟩))).mpr hc.1

#print axioms siteHeight_continuous
#print axioms body_locally_eq_siteHypograph_of_mem_closedTube
#print axioms frontier_body_inter_closedTube_subset_keyGraph
#print axioms frontier_body_inter_closedTube_eq_keyGraph
#print axioms body_locally_eq_carrier_of_not_mem_closedTube
#print axioms frontier_body_outside_keyGraphs
#print axioms frontier_body_iff_frontier_carrier_of_not_mem_closedTube
#print axioms frontier_body_eq_keyGraphs_union_untouched_carrier
end
end PhysicalRegistration.NativeChair
