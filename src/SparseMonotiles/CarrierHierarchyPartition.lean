module

public import SparseMonotiles.CarrierHierarchyH0Frame

@[expose] public section

/-!
One-level existence and unique physical parent partition for a global registered
cell tiling obeying the explicit exact local contact language. Charts, hole
owners and the H0 cross-guard are derived from that world, not assumed as final
hierarchy conclusions. This does not yet prove coarse legality or registration
of arbitrary Euclidean physical body tilings.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem compose_left_injective {d : ℕ} (p : Pose d) : Function.Injective (compose p) := by
  intro q s h
  have hh := congrArg (compose (inversePose p)) h
  simpa only [← compose_assoc, inversePose_compose, compose_root_left] using hh

theorem normalize_reverse {d : ℕ} (p q : Pose d) :
    normalize q p = inversePose (normalize p q) := by
  apply compose_left_injective (normalize p q)
  rw [normalize_cocycle, normalize_self, compose_inversePose]

theorem inversePose_cell {d : ℕ} (p : Pose d) (c : Cell d) :
    (inversePose p).cell c = p.inverseCell c := by
  funext i
  simp only [inversePose, Pose.cell, Pose.inverseCell, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative (p.perm.symm i)) with h | h <;>
    simp [h] <;> ring

theorem hole_normalize {d : ℕ} (p q : Pose d) :
    hole (normalize p q) = p.inverseCell (hole q) := by
  change (compose (inversePose p) q).cell (fun _ => 1) = p.inverseCell (q.cell (fun _ => 1))
  rw [compose_cell, inversePose_cell]

/-- Owning the missing cell gives an actual unit-face contact. -/
theorem contact_of_owns_hole {d : ℕ} (p q : Pose d) (j : Fin d)
    (hq : Occupies q (hole p)) : CellContact p q := by
  let a : Bits d := fun i => decide (i ≠ j)
  have ha : Proper a := ⟨j, by simp [a]⟩
  have hadj : AdjacentCells (bit a) (fun _ => 1) := by
    refine ⟨j, Or.inl ?_, ?_⟩
    · simp [bit, a]
    · intro i hij
      simp [bit, a, hij]
  exact ⟨p.cell (bit a), hole p, (root_occupies_cell p _).mpr (bit_isChairCell ha),
    hq, adjacent_cell_image p hadj⟩

theorem GaugeRel.compose_left {d : ℕ} {r : Equiv.Perm (Fin d)}
    {p q : Pose d} (h : GaugeRel r p q) (G : Pose d) :
    GaugeRel r (compose G p) (compose G q) := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (compose_rightGauge r G p)

/-- A centered incoming tile is exactly an outer child of the central candidate. -/
theorem incoming_as_child {d : ℕ} (G : Pose d) (a : Bits d)
    (σ : Equiv.Perm (Fin d)) :
    compose (centralParent G) (outerPose a σ) = compose G (incomingPose a σ) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    change G.sign i * (4 * bit a (G.perm i)) + (G.shift i - G.sign i) =
      G.sign i * (4 * bit a (G.perm i) - 1) + G.shift i
    ring

/-- Complete actual chart stars produce complete global parent patches. -/
theorem RegisteredWorld.parent_of_complete_chart {d : ℕ} (W : RegisteredWorld d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)} {L : Set (Pose d)}
    (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (p : Pose d) (hp : p ∈ W.tiles)
    (hcomplete : ∀ a, Proper a → (W.chart hL hl p hp).incoming a) :
    CompleteParent σ r W.tiles (centralParent p) := by
  intro q hq
  rcases hq with hq | ⟨a, ha, hq⟩
  · rw [centralChild_parent] at hq
    subst q
    exact ⟨p, hp, Or.inl rfl⟩
  · subst q
    obtain ⟨n, ⟨s, hs, _, _, hn⟩, hg⟩ := hcomplete a ha
    subst n
    have hgg := hg.compose_left p
    rw [compose_normalize, ← incoming_as_child] at hgg
    exact ⟨s, hs, hgg⟩

theorem parent_contains_of_incoming {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (p t : Pose d) {a : Bits d} (ha : Proper a)
    (hg : GaugeRel r (incomingPose a (σ a)) (normalize p t)) :
    ParentContains σ r (centralParent p) t := by
  refine ⟨compose (centralParent p) (outerPose a (σ a)), Or.inr ⟨a, ha, rfl⟩, ?_⟩
  have hgg := hg.compose_left p
  rw [compose_normalize, ← incoming_as_child] at hgg
  exact hgg

private theorem inverse_empty_incoming {d : ℕ}
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)} {p : Pose d}
    (h : GaugeRel r (incomingPose (emptyRole d) (σ (emptyRole d))) p) :
    inversePose p = h0Transition p.perm.symm := by
  rcases h with rfl | rfl <;> apply pose_ext
  · rfl
  · funext i
    rfl
  · funext i
    simp [inversePose, incomingPose, emptyRole, bit, Pose.sign, h0Transition]
  · rfl
  · funext i
    rfl
  · funext i
    simp [inversePose, rightGauge, incomingPose, emptyRole, bit, Pose.sign, h0Transition]

/-- Every actual global tile belongs to a complete physical canonical parent.
Only the registered tiling and its exact local contact law are inputs. -/
theorem RegisteredWorld.complete_parent_exists {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (t : Pose d) (ht : t ∈ W.tiles) :
    ∃ p, CompleteParent σ r W.tiles p ∧ ParentContains σ r p t := by
  classical
  obtain ⟨c, hc, hOwn⟩ := W.covers (hole t)
  have hne : t ≠ c := by
    intro h
    subst c
    exact not_occupies_hole t hOwn
  let j : Fin d := ⟨0, by omega⟩
  have hcontact := contact_of_owns_hole t c j hOwn
  let S := W.chart hL hl t ht
  let R := W.chart hL hl c hc
  let n := normalize c t
  have hn : n ∈ R.tiles := ⟨t, ht, hne, hcontact.symm, rfl⟩
  have his : IsChairCell (hole n) := by
    rw [show n = normalize c t from rfl, hole_normalize]
    exact hOwn
  obtain ⟨ha, hg⟩ := (R.catalog n hn).2.1 his
  have hin : R.incoming n.negative := ⟨n, hn, hg⟩
  have hcontains : ParentContains σ r (centralParent c) t := parent_contains_of_incoming c t ha hg
  by_cases hnonempty : NonemptyRole n.negative
  · exact ⟨centralParent c, W.parent_of_complete_chart hL hl c hc
      (R.complete_of_nonempty_incoming hd ha hnonempty hin), hcontains⟩
  · have hempty : n.negative = emptyRole d := by
      funext i
      cases h : n.negative i
      · rfl
      · exact False.elim (hnonempty ⟨i, h⟩)
    have hgempty : GaugeRel r (incomingPose (emptyRole d) (σ (emptyRole d))) n := by
      simpa [hempty] using hg
    have hRempty : R.incoming (emptyRole d) := by simpa [hempty] using hin
    have htrans : normalize t c = h0Transition n.perm.symm :=
      (normalize_reverse c t).trans (inverse_empty_incoming hgempty)
    have hcross := W.cross_charts t c (r := r)
    rw [htrans] at hcross
    rcases h0_frame_two_corona_completion S R hd n.perm.symm hcross hRempty with hS | hR
    · refine ⟨centralParent t, W.parent_of_complete_chart hL hl t ht hS, ?_⟩
      exact ⟨t, Or.inl (centralChild_parent t).symm, Or.inl rfl⟩
    · exact ⟨centralParent c, W.parent_of_complete_chart hL hl c hc hR, hcontains⟩

/-- Unique one-level physical parent partition of every registered legal world.
This does not yet assert that the parent world is legal after coarsening. -/
theorem RegisteredWorld.unique_physical_parent {d : ℕ} (W : RegisteredWorld d)
    (hd : 3 ≤ d) {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    {L : Set (Pose d)} (hL : ∀ q ∈ L, LocalCatalogFacts σ r q) (hl : W.Legal L)
    (t : Pose d) (ht : t ∈ W.tiles) :
    ∃! P : PhysicalPose r hr, ∃ p, physicalClass r hr p = P ∧
      CompleteParent σ r W.tiles p ∧ ParentContains σ r p t := by
  obtain ⟨p, hp, hpt⟩ := W.complete_parent_exists hd hL hl t ht
  refine ⟨physicalClass r hr p, ⟨p, rfl, hp, hpt⟩, ?_⟩
  rintro P ⟨q, hqP, hq, hqt⟩
  exact hqP.symm.trans (complete_parent_unique (by omega) hr he W.tiles W.disjoint hq hp hqt hpt)

#print axioms RegisteredWorld.parent_of_complete_chart
#print axioms RegisteredWorld.complete_parent_exists
#print axioms RegisteredWorld.unique_physical_parent
end SparseMonotiles.CarrierHierarchy
