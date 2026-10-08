module

public import SparseMonotiles.CarrierHierarchyTwoStars

@[expose] public section

/-!
Actual complete-patch stability under the physical right involution, followed
by uniqueness of complete physical parents. The child covariance is an explicit
finite input already proved for both exact supplied substitutions.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem GaugeRel.symm {d : ℕ} {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    {p q : Pose d} (h : GaugeRel r p q) : GaugeRel r q p :=
  (gaugeSetoid r hr).iseqv.symm h

theorem GaugeRel.trans {d : ℕ} {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    {p q s : Pose d} (h : GaugeRel r p q) (h' : GaugeRel r q s) : GaugeRel r p s :=
  (gaugeSetoid r hr).iseqv.trans h h'

theorem rightGauge_eq_compose {d : ℕ} (r : Equiv.Perm (Fin d)) (p : Pose d) :
    rightGauge r p = compose p (unsignedPose r) := by
  apply pose_ext
  · rfl
  · funext i
    simp [rightGauge, compose, unsignedPose]
  · funext i
    simp [rightGauge, compose, unsignedPose]

theorem compose_root_right {d : ℕ} (p : Pose d) : compose p (rootPose d) = p := by
  apply pose_ext
  · ext i
    rfl
  · funext i
    simp [compose, rootPose]
  · funext i
    simp [compose, rootPose]

theorem unsignedPose_involution {d : ℕ} (r : Equiv.Perm (Fin d))
    (hr : Function.Involutive r) :
    compose (unsignedPose r) (unsignedPose r) = rootPose d := by
  apply pose_ext
  · ext i
    exact congrArg Fin.val (hr i)
  · rfl
  · rfl

theorem compose_rightGauge {d : ℕ} (r : Equiv.Perm (Fin d)) (p q : Pose d) :
    compose p (rightGauge r q) = rightGauge r (compose p q) := by
  rw [rightGauge_eq_compose, rightGauge_eq_compose, compose_assoc]

private theorem conjugated_outer {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    (he : EquivariantChildren σ r) (a : Bits d) :
    compose (unsignedPose r) (outerPose a (σ a)) =
      rightGauge r (outerPose (fun i => a (r i)) (σ (fun i => a (r i)))) := by
  have h := congrArg (fun p => compose p (unsignedPose r)) (he a)
  simp only [compose_assoc, unsignedPose_involution r hr, compose_root_right] at h
  exact h.trans (rightGauge_eq_compose r _).symm

private theorem gauge_outer_child {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    (he : EquivariantChildren σ r) (p : Pose d) (a : Bits d) :
    compose (rightGauge r p) (outerPose a (σ a)) =
      rightGauge r (compose p (outerPose (fun i => a (r i)) (σ (fun i => a (r i))))) := by
  rw [rightGauge_eq_compose, compose_assoc, conjugated_outer hr he, compose_rightGauge]

/-- Changing a parent representative permutes actual child roles and changes
only the allowed right-r representative of each child. -/
theorem children_rightGauge {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    (he : EquivariantChildren σ r) (p : Pose d) :
    ∀ q ∈ children σ (rightGauge r p), ∃ s ∈ children σ p, GaugeRel r s q := by
  intro q hq
  rcases hq with rfl | ⟨a, ha, rfl⟩
  · exact ⟨centralChild p, Or.inl rfl, Or.inr rfl⟩
  · have ha' : Proper (fun i => a (r i)) := by
      obtain ⟨i, hi⟩ := ha
      exact ⟨r.symm i, by simpa using hi⟩
    refine ⟨compose p (outerPose (fun i => a (r i)) (σ (fun i => a (r i)))),
      Or.inr ⟨_, ha', rfl⟩, Or.inr ?_⟩
    exact gauge_outer_child hr he p a

/-- Completeness is a property of the physical parent class, not a chosen
framed lift to a smaller language. -/
theorem CompleteParent.rightGauge {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    (he : EquivariantChildren σ r) {tiles : Set (Pose d)} {p : Pose d}
    (hc : CompleteParent σ r tiles p) : CompleteParent σ r tiles (rightGauge r p) := by
  intro q hq
  obtain ⟨s, hs, hsq⟩ := children_rightGauge hr he p q hq
  obtain ⟨t, ht, hst⟩ := hc s hs
  exact ⟨t, ht, (hsq.symm hr).trans hr hst⟩

theorem CompleteParent.of_gauge {d : ℕ} {σ : Bits d → Equiv.Perm (Fin d)}
    {r : Equiv.Perm (Fin d)} (hr : Function.Involutive r)
    (he : EquivariantChildren σ r) {tiles : Set (Pose d)} {p q : Pose d}
    (hc : CompleteParent σ r tiles p) (hg : GaugeRel r p q) : CompleteParent σ r tiles q := by
  rcases hg with rfl | rfl
  · exact hc
  · exact hc.rightGauge hr he

private theorem gauge_of_centers {d : ℕ} {r : Equiv.Perm (Fin d)} {p q : Pose d}
    (h : GaugeRel r (centralChild p) (centralChild q)) : GaugeRel r p q := by
  have hp := centralParent_respects_gauge r h
  simpa only [centralParent_child] using hp

/-- Two complete actual parent patches sharing a physical tile have the same
physical parent. The outer/outer case uses their actual central hole owners;
central/outer uses the proved two-star exclusion. -/
theorem complete_parent_unique {d : ℕ} (hd : 2 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {p q t : Pose d} (hp : CompleteParent σ r tiles p) (hq : CompleteParent σ r tiles q)
    (hpt : ParentContains σ r p t) (hqt : ParentContains σ r q t) :
    physicalClass r hr p = physicalClass r hr q := by
  obtain ⟨u, hu, hut⟩ := hpt
  obtain ⟨v, hv, hvt⟩ := hqt
  rcases hu with hu | ⟨a, ha, hu⟩ <;> rcases hv with hv | ⟨b, hb, hv⟩
  · subst u
    subst v
    exact Quotient.sound (gauge_of_centers (hut.trans hr (hvt.symm hr)))
  · subst u
    subst v
    have hg := centralParent_respects_gauge r (hvt.trans hr (hut.symm hr))
    simp only [centralParent_child] at hg
    have hc := hp.of_gauge hr he (hg.symm hr)
    exact False.elim (two_star_exclusion hd σ r tiles disjoint q hb ⟨hq, hc⟩)
  · subst u
    subst v
    have hg := centralParent_respects_gauge r (hut.trans hr (hvt.symm hr))
    simp only [centralParent_child] at hg
    have hc := hq.of_gauge hr he (hg.symm hr)
    exact False.elim (two_star_exclusion hd σ r tiles disjoint p ha ⟨hp, hc⟩)
  · subst u
    subst v
    have hpOwn : Occupies (centralChild p) (hole t) := by
      rw [← gauge_hole_eq hut]
      exact central_owns_child_hole p ha (σ a)
    have hqOwn : Occupies (centralChild q) (hole t) := by
      rw [← gauge_hole_eq hvt]
      exact central_owns_child_hole q hb (σ b)
    obtain ⟨s, hs, hps⟩ := hp _ (Or.inl rfl)
    obtain ⟨w, hw, hqw⟩ := hq _ (Or.inl rfl)
    have hsw := disjoint s hs w hw (hole t)
      ((gauge_occupies_iff hps _).mp hpOwn) ((gauge_occupies_iff hqw _).mp hqOwn)
    subst w
    exact Quotient.sound (gauge_of_centers (hps.trans hr (hqw.symm hr)))

/-- Distinct complete physical parents have no common physical child. -/
theorem complete_parent_patches_disjoint {d : ℕ} (hd : 2 ≤ d)
    {σ : Bits d → Equiv.Perm (Fin d)} {r : Equiv.Perm (Fin d)}
    (hr : Function.Involutive r) (he : EquivariantChildren σ r)
    (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {p q : Pose d} (hp : CompleteParent σ r tiles p) (hq : CompleteParent σ r tiles q)
    (hne : physicalClass r hr p ≠ physicalClass r hr q) :
    ¬ ∃ t, ParentContains σ r p t ∧ ParentContains σ r q t := by
  rintro ⟨t, hpt, hqt⟩
  exact hne (complete_parent_unique hd hr he tiles disjoint hp hq hpt hqt)

#print axioms children_rightGauge
#print axioms CompleteParent.of_gauge
#print axioms complete_parent_unique
#print axioms complete_parent_patches_disjoint
end SparseMonotiles.CarrierHierarchy
