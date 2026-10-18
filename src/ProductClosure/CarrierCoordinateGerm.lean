module

public import ProductClosure.NativeAssembly

@[expose] public section

/-! Finite-coordinate local germs of arbitrary finite integer polycubes. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- An occupied-cell face, with redundant geometric planes deliberately retained. -/
abbrev CarrierPlaneIndex (S : Finset (Polycube.LatticeIndex (m + 1))) :=
  Polycube.Cell S × Fin (m + 1) × Bool

def carrierPlaneLevel (b : CarrierPlaneIndex S) : ℝ :=
  (b.1.val b.2.1 : ℝ) + if b.2.2 then 1 else 0

/-- Only inequalities whose endpoint planes pass through `x` remain active. -/
theorem carrier_local_coordinate_germ (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x : Space m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      (y ∈ Polycube.carrier S ↔ ∃ c : Polycube.Cell S,
        x ∈ Polycube.latticeCell c.val ∧
        ∀ i, (x i = (c.val i : ℝ) → (c.val i : ℝ) ≤ y i) ∧
          (x i = (c.val i : ℝ) + 1 → y i ≤ (c.val i : ℝ) + 1)) := by
  let U : Set (Space m) := {y | ∀ c : Polycube.Cell S, ∀ i : Fin (m + 1),
    ((c.val i : ℝ) < x i → (c.val i : ℝ) < y i) ∧
    (x i < (c.val i : ℝ) → y i < (c.val i : ℝ)) ∧
    ((c.val i : ℝ) + 1 < x i → (c.val i : ℝ) + 1 < y i) ∧
    (x i < (c.val i : ℝ) + 1 → y i < (c.val i : ℝ) + 1)}
  have hU : IsOpen U := by
    unfold U
    simp only [ofPred_forall, ofPred_and]
    apply isOpen_iInter_of_finite
    intro c
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun y : Space m => y i) := by fun_prop
    have hlo : IsOpen {y : Space m | (c.val i : ℝ) < x i → (c.val i : ℝ) < y i} := by
      by_cases h : (c.val i : ℝ) < x i
      · simpa only [h, true_implies] using isOpen_lt continuous_const hc
      · simp [h]
    have hlc : IsOpen {y : Space m | x i < (c.val i : ℝ) → y i < (c.val i : ℝ)} := by
      by_cases h : x i < (c.val i : ℝ)
      · simpa only [h, true_implies] using isOpen_lt hc continuous_const
      · simp [h]
    have huc : IsOpen {y : Space m | (c.val i : ℝ) + 1 < x i → (c.val i : ℝ) + 1 < y i} := by
      by_cases h : (c.val i : ℝ) + 1 < x i
      · simpa only [h, true_implies] using isOpen_lt continuous_const hc
      · simp [h]
    have hup : IsOpen {y : Space m | x i < (c.val i : ℝ) + 1 → y i < (c.val i : ℝ) + 1} := by
      by_cases h : x i < (c.val i : ℝ) + 1
      · simpa only [h, true_implies] using isOpen_lt hc continuous_const
      · simp [h]
    simpa only [ofPred_forall] using hlo.inter (hlc.inter (huc.inter hup))
  refine ⟨U, hU, (by intro c i; exact ⟨id, id, id, id⟩), ?_⟩
  intro y hy
  constructor
  · intro hmem
    obtain ⟨z, hz, hyz⟩ := (Polycube.mem_carrier_iff S y).mp hmem
    let c : Polycube.Cell S := ⟨z, hz⟩
    refine ⟨c, ?_, fun i => ⟨fun _ => (hyz i).1, fun _ => (hyz i).2⟩⟩
    intro i
    constructor
    · exact le_of_not_gt (fun h => (not_lt_of_ge (hyz i).1) ((hy c i).2.1 h))
    · exact le_of_not_gt (fun h => (not_lt_of_ge (hyz i).2) ((hy c i).2.2.1 h))
  · rintro ⟨c, hxc, hactive⟩
    apply (Polycube.mem_carrier_iff S y).mpr
    refine ⟨c.val, c.property, fun i => ?_⟩
    constructor
    · by_cases h : x i = (c.val i : ℝ)
      · exact (hactive i).1 h
      · exact ((hy c i).1 (lt_of_le_of_ne (hxc i).1 (Ne.symm h))).le
    · by_cases h : x i = (c.val i : ℝ) + 1
      · exact (hactive i).2 h
      · exact ((hy c i).2.2.2 (lt_of_le_of_ne (hxc i).2 h)).le

/-- Every actual carrier boundary point lies on one of the finitely many
occupied-cell coordinate planes. -/
theorem carrier_frontier_coordinate (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x : Space m) (hx : x ∈ frontier (Polycube.carrier S)) :
    ∃ c : Polycube.Cell S, ∃ i, x i = (c.val i : ℝ) ∨ x i = (c.val i : ℝ) + 1 := by
  have hxC : x ∈ Polycube.carrier S := (carrier_isClosed S).frontier_subset hx
  obtain ⟨U, hU, hxU, heq⟩ := carrier_local_coordinate_germ S x
  obtain ⟨z, hz, hxz⟩ := (Polycube.mem_carrier_iff S x).mp hxC
  let c : Polycube.Cell S := ⟨z, hz⟩
  by_contra h
  have hne (i : Fin (m + 1)) : x i ≠ (c.val i : ℝ) ∧ x i ≠ (c.val i : ℝ) + 1 := by
    constructor
    · intro hi; exact h ⟨c, i, Or.inl hi⟩
    · intro hi; exact h ⟨c, i, Or.inr hi⟩
  have hUC : U ⊆ Polycube.carrier S := by
    intro y hy
    exact (heq y hy).mpr ⟨c, hxz, fun i =>
      ⟨fun hi => ((hne i).1 hi).elim, fun hi => ((hne i).2 hi).elim⟩⟩
  exact hx.2 (interior_maximal hUC hU hxU)

/-- Active axes ignore redundant labels for coincident cell-face planes. -/
def activeCarrierAxes (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x : Space m) : Finset (Fin (m + 1)) :=
  Finset.univ.filter (fun i => ∃ c : Polycube.Cell S,
    x i = (c.val i : ℝ) ∨ x i = (c.val i : ℝ) + 1)

@[simp] theorem mem_activeCarrierAxes (x : Space m) (i : Fin (m + 1)) :
    i ∈ activeCarrierAxes S x ↔ ∃ c : Polycube.Cell S,
      x i = (c.val i : ℝ) ∨ x i = (c.val i : ℝ) + 1 := by
  simp [activeCarrierAxes]

/-- Local membership is determined by finitely many active coordinate signs. -/
theorem carrier_local_active_sign_germ (S : Finset (Polycube.LatticeIndex (m + 1)))
    (x : Space m) :
    ∃ U : Set (Space m), IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, ∀ z ∈ U,
      (∀ i ∈ activeCarrierAxes S x,
        (y i ≤ x i ↔ z i ≤ x i) ∧ (x i ≤ y i ↔ x i ≤ z i)) →
      (y ∈ Polycube.carrier S ↔ z ∈ Polycube.carrier S) := by
  obtain ⟨U, hU, hxU, heq⟩ := carrier_local_coordinate_germ S x
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy z hz hsign
  rw [heq y hy, heq z hz]
  have hlo (c : Polycube.Cell S) (i : Fin (m + 1)) (hi : x i = (c.val i : ℝ)) :
      ((c.val i : ℝ) ≤ y i ↔ (c.val i : ℝ) ≤ z i) := by
    simpa only [hi] using (hsign i (mem_activeCarrierAxes x i |>.mpr ⟨c, Or.inl hi⟩)).2
  have hup (c : Polycube.Cell S) (i : Fin (m + 1)) (hi : x i = (c.val i : ℝ) + 1) :
      (y i ≤ (c.val i : ℝ) + 1 ↔ z i ≤ (c.val i : ℝ) + 1) := by
    simpa only [hi] using (hsign i (mem_activeCarrierAxes x i |>.mpr ⟨c, Or.inr hi⟩)).1
  constructor
  · rintro ⟨c, hxc, hc⟩
    exact ⟨c, hxc, fun i => ⟨fun hi => (hlo c i hi).mp ((hc i).1 hi),
      fun hi => (hup c i hi).mp ((hc i).2 hi)⟩⟩
  · rintro ⟨c, hxc, hc⟩
    exact ⟨c, hxc, fun i => ⟨fun hi => (hlo c i hi).mpr ((hc i).1 hi),
      fun hi => (hup c i hi).mpr ((hc i).2 hi)⟩⟩

#print axioms carrier_local_coordinate_germ
#print axioms carrier_frontier_coordinate
#print axioms carrier_local_active_sign_germ
end
end ProductClosure.NativeCompiler
