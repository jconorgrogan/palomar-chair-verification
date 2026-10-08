module
public import RegisteredPrime.TwoCoronaExistence
@[expose] public section
namespace RegisteredPrime

noncomputable def centerParent (P : Parameters) (g : Pose P.p) : Pose P.p :=
  g.comp (arithmeticChild P .central).inv

@[simp] theorem centerParent_central (P : Parameters) (g : Pose P.p) :
    (centerParent P g).comp (arithmeticChild P .central) = g := by
  unfold centerParent
  rw [Pose.comp_assoc, Pose.inv_comp, Pose.comp_identity]

@[simp] theorem centerParent_standard (P : Parameters) :
    centerParent P (arithmeticChild P .central) = identityPose P.p :=
  Pose.comp_inv _

theorem central_relative_outer_incoming (P : Parameters) (A : Mask P.p) (hA : Proper A) :
    (arithmeticChild P .central).relative (arithmeticChild P (.outer A hA)) =
      incomingPose P (scalarRole P A) (scalarRole_proper P A hA) := by
  have h := seed_inverse_incoming P A hA
  change ((arithmeticChild P (.outer A hA)).relative (arithmeticChild P .central)).inv = _ at h
  rwa [Pose.relative_reverse] at h

theorem CompleteStar.child_mem (P : Parameters) (W : RegisteredWorld P.p) (g : Pose P.p)
    (hg : W.tiles g) (hs : CompleteStar P W g) (a : Role P.p) :
    W.tiles ((centerParent P g).comp (arithmeticChild P a)) := by
  cases a with
  | central => rwa [centerParent_central]
  | outer A hA =>
    unfold centerParent
    rw [Pose.comp_assoc]
    change W.tiles (g.comp ((arithmeticChild P .central).relative (arithmeticChild P (.outer A hA))))
    rw [central_relative_outer_incoming]
    exact hs _ _

/-- A complete marked star covers its actual doubled-parent carrier. -/
theorem CompleteStar.parent_cover (P : Parameters) (W : RegisteredWorld P.p) (g : Pose P.p)
    (hg : W.tiles g) (hs : CompleteStar P W g) (x : Cell P.p)
    (hx : DoubledChairCell ((centerParent P g).inv.cell x)) :
    ∃ a, W.tiles ((centerParent P g).comp (arithmeticChild P a)) ∧
      Occupies ((centerParent P g).comp (arithmeticChild P a)) x := by
  obtain ⟨a, ha⟩ := (exact_child_cover P _).mp hx
  exact ⟨a, CompleteStar.child_mem P W g hg hs a, (occupies_comp_iff _ _ _).mpr ha⟩

theorem central_inverse_anchor (P : Parameters) (i : Fin P.p) :
    (arithmeticChild P .central).inv.anchor i = -1 := by
  simp [Pose.inv, RegisteredFrame.linear, RegisteredFrame.sign, RegisteredFrame.inv]

theorem centerParent_outer_negative (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (centerParent P (arithmeticChild P (.outer A hA))).frame.negative i = A i := by
  simp [centerParent, Pose.comp, RegisteredFrame.comp, Pose.inv, RegisteredFrame.inv]

theorem centerParent_outer_anchor (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (i : Fin P.p) : (centerParent P (arithmeticChild P (.outer A hA))).anchor i = 6 * bit (A i) - 1 := by
  change (arithmeticChild P (.outer A hA)).anchor i +
    (arithmeticChild P (.outer A hA)).frame.sign i *
      (arithmeticChild P .central).inv.anchor ((arithmeticChild P (.outer A hA)).frame.perm i) = _
  rw [child_outer_anchor, central_inverse_anchor]
  simp only [RegisteredFrame.sign, child_outer_negative]
  cases h : A i <;> simp [bit, h]

theorem centered_outer_inverse_at (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (x : Cell P.p) (i : Fin P.p) :
    (centerParent P (arithmeticChild P (.outer A hA))).inv.cell x
      ((centerParent P (arithmeticChild P (.outer A hA))).frame.perm i) =
      if A i then 4 - x i else x i + 1 := by
  rw [inverse_at, centerParent_outer_negative, centerParent_outer_anchor]
  cases h : A i <;> simp [bit, h] <;> omega

theorem centered_outer_parent_contains (P : Parameters) (A : Mask P.p) (hA : Proper A)
    (x : Cell P.p)
    (hbox : ∀ i, 2 * bit (A i) - 1 ≤ x i ∧ x i ≤ 2 * bit (A i) + 2)
    (hcorner : ∃ j, A j = false ∧ x j ≤ 0) :
    DoubledChairCell ((centerParent P (arithmeticChild P (.outer A hA))).inv.cell x) := by
  let t := centerParent P (arithmeticChild P (.outer A hA))
  constructor
  · intro k
    let i := t.frame.inverse k
    have hik : t.frame.perm i = k := t.frame.right_inverse k
    rw [← hik, centered_outer_inverse_at]
    have hi := hbox i
    cases ha : A i <;> simp [bit, ha] at hi ⊢ <;> omega
  · obtain ⟨j, hj, hx⟩ := hcorner
    refine ⟨t.frame.perm j, ?_⟩
    rw [centered_outer_inverse_at]
    simp [hj]
    omega

theorem centered_outer_child_anchor_odd (P : Parameters) (A B : Mask P.p)
    (hA : Proper A) (hB : Proper B) (i : Fin P.p) :
    ((centerParent P (arithmeticChild P (.outer A hA))).comp
      (arithmeticChild P (.outer B hB))).anchor i % 2 = 1 := by
  change ((centerParent P (arithmeticChild P (.outer A hA))).anchor i +
    (centerParent P (arithmeticChild P (.outer A hA))).frame.sign i *
      (arithmeticChild P (.outer B hB)).anchor
        ((centerParent P (arithmeticChild P (.outer A hA))).frame.perm i)) % 2 = 1
  rw [centerParent_outer_anchor, child_outer_anchor]
  simp only [RegisteredFrame.sign, centerParent_outer_negative]
  by_cases ha : A i = true <;>
    by_cases hb : B ((centerParent P (arithmeticChild P (.outer A hA))).frame.perm i) = true <;>
    simp [bit, ha, hb] <;> omega

theorem CompleteStar.reframe_iff (P : Parameters) (W : RegisteredWorld P.p) (g c : Pose P.p) :
    CompleteStar P (W.reframe g) c ↔ CompleteStar P W (g.comp c) := by
  unfold CompleteStar
  constructor
  · intro h A hA
    have ht := h A hA
    change W.tiles (g.comp (c.comp (incomingPose P A hA))) at ht
    rwa [← Pose.comp_assoc] at ht
  · intro h A hA
    change W.tiles (g.comp (c.comp (incomingPose P A hA)))
    rw [← Pose.comp_assoc]
    exact h A hA

end RegisteredPrime
