module

public import SparseMonotiles.CarrierHierarchyConcrete

@[expose] public section

/-!
Geometric two-star exclusion on actual registered unit cells. The witness is
outside the common outer tile and the standard central tile. The two complete
patches would therefore supply owners of opposite anchor parity for one cell.
-/
namespace SparseMonotiles.CarrierHierarchy
open Contact

private theorem parent_inverse_outer {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (x : Cell d) (i : Fin d) :
    (centralParent (outerPose a σ)).inverseCell x (σ i) =
      if a i then 4 - x i else x i + 1 := by
  simp only [Pose.inverseCell, centralParent, outerPose, Equiv.symm_apply_apply, Pose.sign]
  rcases Bool.eq_false_or_eq_true (a i) with h | h <;> simp [bit, h] <;> omega

def twoStarCell {d : ℕ} (a : Bits d) (j k : Fin d) : Cell d :=
  fun i => if i = j then 0 else if i = k then (if a i then 1 else 2) else 2 * bit a i

private theorem twoStarCell_double {d : ℕ} (a : Bits d) (j k : Fin d) :
    DoubleCell (twoStarCell a j k) := by
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      simp [twoStarCell]
    · by_cases hik : i = k
      · subst i
        cases h : a k <;> simp [twoStarCell, bit, hij, h]
      · cases h : a i <;> simp [twoStarCell, bit, hij, hik, h]
  · exact ⟨j, by simp [twoStarCell]⟩

private theorem twoStarCell_other_double {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (j k : Fin d) (hj : a j = false) :
    DoubleCell ((centralParent (outerPose a σ)).inverseCell (twoStarCell a j k)) := by
  constructor
  · intro l
    obtain ⟨i, rfl⟩ := σ.surjective l
    rw [parent_inverse_outer]
    by_cases hij : i = j
    · subst i
      simp [twoStarCell, hj]
    · by_cases hik : i = k
      · subst i
        cases h : a k <;> simp [twoStarCell, bit, hij, h]
      · cases h : a i <;> simp [twoStarCell, bit, hij, hik, h]
  · exact ⟨σ j, by rw [parent_inverse_outer]; simp [twoStarCell, hj]⟩

private theorem twoStarCell_not_outer {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (j k : Fin d) (hkj : k ≠ j) :
    ¬ Occupies (outerPose a σ) (twoStarCell a j k) := by
  intro h
  have hk := ((occupies_outer a σ _).mp h).1 k
  cases ha : a k <;> simp [twoStarCell, bit, hkj, ha] at hk

private theorem twoStarCell_not_center {d : ℕ} (a : Bits d) (j k : Fin d) :
    ¬ Occupies (centralPose d) (twoStarCell a j k) := by
  intro h
  have hj := ((occupies_central _).mp h).1 j
  simp [twoStarCell] at hj

/-- Coverage of a transformed doubled carrier by actual composed child poses. -/
theorem parent_cell_noncentral_owner {d : ℕ}
    (σ : Bits d → Equiv.Perm (Fin d)) (p : Pose d) (x : Cell d)
    (hx : DoubleCell (p.inverseCell x)) (hn : ¬ Occupies (centralChild p) x) :
    ∃ a, Proper a ∧ Occupies (compose p (outerPose a (σ a))) x := by
  rcases (canonical_dissection σ _).mp hx with hc | ⟨a, ha, hc⟩
  · apply False.elim
    apply hn
    rw [← compose_central, ← p.cell_inverseCell x]
    exact (occupies_compose_cell p (centralPose d) _).mpr hc
  · refine ⟨a, ha, ?_⟩
    rw [← p.cell_inverseCell x]
    exact (occupies_compose_cell p _ _).mpr hc

private theorem outer_child_shift_parity {d : ℕ} (p : Pose d)
    (a : Bits d) (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (compose p (outerPose a σ)).shift i % 2 = p.shift i % 2 := by
  simp only [compose, outerPose, Pose.sign]
  rcases Bool.eq_false_or_eq_true (p.negative i) with hp | hp <;>
    rcases Bool.eq_false_or_eq_true (a (p.perm i)) with ha | ha <;>
    simp [bit, hp, ha] <;> omega

private theorem parent_outer_odd {d : ℕ} (a : Bits d)
    (σ : Equiv.Perm (Fin d)) (i : Fin d) :
    (centralParent (outerPose a σ)).shift i % 2 = 1 := by
  cases h : a i <;> simp [centralParent, outerPose, Pose.sign, bit, h]

theorem gauge_shift_eq {d : ℕ} {r : Equiv.Perm (Fin d)} {p q : Pose d}
    (h : GaugeRel r p q) : p.shift = q.shift := by
  rcases h with rfl | rfl <;> rfl

/-- Two complete physical candidate stars are geometrically incompatible.
The common outer child may have any coordinate permutation. No contact-law
hypothesis, global frame lift, or complete-parent uniqueness is assumed. -/
theorem normalized_two_star_exclusion {d : ℕ} (hd : 2 ≤ d)
    (σ : Bits d → Equiv.Perm (Fin d)) (r : Equiv.Perm (Fin d))
    (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    {a : Bits d} (ha : Proper a) :
    ¬ (CompleteParent σ r tiles (rootPose d) ∧
      CompleteParent σ r tiles (centralParent (outerPose a (σ a)))) := by
  rintro ⟨hc₁, hc₂⟩
  obtain ⟨j, hj⟩ := ha
  have hk : ∃ k : Fin d, k ≠ j := by
    let i₀ : Fin d := ⟨0, by omega⟩
    let i₁ : Fin d := ⟨1, by omega⟩
    by_cases h : j = i₀
    · refine ⟨i₁, ?_⟩
      intro hh
      have := congrArg Fin.val (hh.trans h)
      simp [i₀, i₁] at this
    · exact ⟨i₀, Ne.symm h⟩
  obtain ⟨k, hkj⟩ := hk
  let x := twoStarCell a j k
  have hd₁ : DoubleCell ((rootPose d).inverseCell x) := by
    have he : (rootPose d).inverseCell x = x := by
      funext i
      simp [Pose.inverseCell, rootPose, Pose.sign]
    rw [he]
    exact twoStarCell_double a j k
  have hn₁ : ¬ Occupies (centralChild (rootPose d)) x :=
    twoStarCell_not_center a j k
  obtain ⟨b, hb, hbx⟩ := parent_cell_noncentral_owner σ (rootPose d) x hd₁ hn₁
  obtain ⟨c, hc, hcx⟩ := parent_cell_noncentral_owner σ
    (centralParent (outerPose a (σ a))) x
    (twoStarCell_other_double a (σ a) j k hj)
    (by rw [centralChild_parent]; exact twoStarCell_not_outer a (σ a) j k hkj)
  obtain ⟨u, hu, hgu⟩ := hc₁ _ (Or.inr ⟨b, hb, rfl⟩)
  obtain ⟨v, hv, hgv⟩ := hc₂ _ (Or.inr ⟨c, hc, rfl⟩)
  have huOwn := (gauge_occupies_iff hgu x).mp hbx
  have hvOwn := (gauge_occupies_iff hgv x).mp hcx
  have huv := disjoint u hu v hv x huOwn hvOwn
  have hue : u.shift j % 2 = 0 := by
    rw [← congrFun (gauge_shift_eq hgu) j, outer_child_shift_parity]
    rfl
  have hvo : v.shift j % 2 = 1 := by
    rw [← congrFun (gauge_shift_eq hgv) j, outer_child_shift_parity, parent_outer_odd]
  rw [huv] at hue
  omega

private theorem pose_ext {d : ℕ} {p q : Pose d}
    (hp : p.perm = q.perm) (hn : p.negative = q.negative) (hs : p.shift = q.shift) : p = q := by
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem compose_assoc {d : ℕ} (p q t : Pose d) :
    compose (compose p q) t = compose p (compose q t) := by
  apply pose_ext
  · ext i
    rfl
  · funext i
    change xor (xor (p.negative i) (q.negative (p.perm i)))
        (t.negative (q.perm (p.perm i))) =
      xor (p.negative i) (xor (q.negative (p.perm i)) (t.negative (q.perm (p.perm i))))
    exact Bool.xor_assoc _ _ _
  · funext i
    change (compose p q).sign i * t.shift (q.perm (p.perm i)) +
        (p.sign i * q.shift (p.perm i) + p.shift i) =
      p.sign i * (q.sign (p.perm i) * t.shift (q.perm (p.perm i)) + q.shift (p.perm i)) + p.shift i
    rw [compose_sign]
    ring

theorem centralParent_compose {d : ℕ} (p q : Pose d) :
    centralParent (compose p q) = compose p (centralParent q) := by
  apply pose_ext
  · rfl
  · rfl
  · funext i
    change (p.sign i * q.shift (p.perm i) + p.shift i) - (compose p q).sign i =
      p.sign i * (q.shift (p.perm i) - q.sign (p.perm i)) + p.shift i
    rw [compose_sign]
    ring

private theorem compose_root_left {d : ℕ} (p : Pose d) :
    compose (rootPose d) p = p := by
  apply pose_ext
  · ext i
    rfl
  · funext i
    simp [compose, rootPose]
  · funext i
    simp [compose, rootPose, Pose.sign]

private theorem composed_odd_shift {d : ℕ} (p q : Pose d)
    (hq : ∀ i, q.shift i % 2 = 1) (i : Fin d) :
    (compose p q).shift i % 2 = (p.shift i + 1) % 2 := by
  have hi := hq (p.perm i)
  rcases Bool.eq_false_or_eq_true (p.negative i) with hp | hp <;>
    simp [compose, Pose.sign, hp] <;> omega

/-- Full covariance of two-star exclusion: the standard parent may have any
registered signed frame and integer translation. Reflection is allowed. -/
theorem two_star_exclusion {d : ℕ} (hd : 2 ≤ d)
    (σ : Bits d → Equiv.Perm (Fin d)) (r : Equiv.Perm (Fin d))
    (tiles : Set (Pose d))
    (disjoint : ∀ p ∈ tiles, ∀ q ∈ tiles, ∀ c,
      Occupies p c → Occupies q c → p = q)
    (G : Pose d) {a : Bits d} (ha : Proper a) :
    ¬ (CompleteParent σ r tiles G ∧
      CompleteParent σ r tiles (centralParent (compose G (outerPose a (σ a))))) := by
  rintro ⟨hc₁, hc₂⟩
  obtain ⟨j, hj⟩ := ha
  have hk : ∃ k : Fin d, k ≠ j := by
    let i₀ : Fin d := ⟨0, by omega⟩
    let i₁ : Fin d := ⟨1, by omega⟩
    by_cases h : j = i₀
    · refine ⟨i₁, ?_⟩
      intro hh
      have := congrArg Fin.val (hh.trans h)
      simp [i₀, i₁] at this
    · exact ⟨i₀, Ne.symm h⟩
  obtain ⟨k, hkj⟩ := hk
  let x := twoStarCell a j k
  have hd₁ : DoubleCell ((rootPose d).inverseCell x) := by
    have he : (rootPose d).inverseCell x = x := by
      funext i
      simp [Pose.inverseCell, rootPose, Pose.sign]
    rw [he]
    exact twoStarCell_double a j k
  obtain ⟨b, hb, hbx⟩ := parent_cell_noncentral_owner σ (rootPose d) x hd₁
    (twoStarCell_not_center a j k)
  rw [compose_root_left] at hbx
  obtain ⟨c, hc, hcx⟩ := parent_cell_noncentral_owner σ
    (centralParent (outerPose a (σ a))) x
    (twoStarCell_other_double a (σ a) j k hj)
    (by rw [centralChild_parent]; exact twoStarCell_not_outer a (σ a) j k hkj)
  obtain ⟨u, hu, hgu⟩ := hc₁ _ (Or.inr ⟨b, hb, rfl⟩)
  obtain ⟨v, hv, hgv⟩ := hc₂ _ (Or.inr ⟨c, hc, rfl⟩)
  have huOwn : Occupies u (G.cell x) := (gauge_occupies_iff hgu _).mp
    ((occupies_compose_cell G _ x).mpr hbx)
  have hvOwn : Occupies v (G.cell x) := by
    apply (gauge_occupies_iff hgv _).mp
    rw [centralParent_compose, compose_assoc]
    exact (occupies_compose_cell G _ x).mpr hcx
  have huv := disjoint u hu v hv _ huOwn hvOwn
  have hue : u.shift j % 2 = G.shift j % 2 := by
    rw [← congrFun (gauge_shift_eq hgu) j, outer_child_shift_parity]
  have hvo : v.shift j % 2 = (G.shift j + 1) % 2 := by
    rw [← congrFun (gauge_shift_eq hgv) j, centralParent_compose, compose_assoc]
    apply composed_odd_shift
    intro i
    rw [outer_child_shift_parity, parent_outer_odd]
  rw [huv] at hue
  omega

#print axioms parent_cell_noncentral_owner
#print axioms normalized_two_star_exclusion
#print axioms two_star_exclusion
end SparseMonotiles.CarrierHierarchy
