module

public import SparseMonotiles.KeyLocalFormula
public import SparseMonotiles.KeyFacetOrientation

@[expose] public section

/-!
# The carrier plane is the canonical key base plane

Finite oriented-key certificates and the actual canonical pose determine the
carrier halfspace, including its different physical orientation for bumps and
dents. Removing the repeated base constraint gives an exact Boolean material
formula. Closure is retained for dents. Strict relative-base points have a
constant material germ and therefore are not points of the physical boundary.
-/
namespace SparseMonotiles

open Set Filter
open scoped Topology

namespace Contact

/-- A canonical box match identifies the normal axis, the base-plane translation,
and the signed orientation. The contact coefficient reversal is not used as a
physical orientation rule. -/
theorem Pose.basePlane_alignment {d : ℕ} {den height : ℤ}
    (hd : den ≠ 0) (hh : height ≠ 0) (p : Pose d)
    {f : Facet d} {box ref : BoxKey d} {a : Fin d}
    (hmatch : p.boxKey den ref = box)
    (hr : ∀ i, ref.radius i = 0 → i = a)
    (hc : ref.centre a = 0) (ha : ref.apex a = height)
    (ho : box.OrientedAt den height f) :
    p.perm f.axis = a ∧ p.shift f.axis = f.gridFacet.anchor f.axis ∧
      f.normal * p.sign f.axis = if box.bump then 1 else -1 := by
  have haxis : p.perm f.axis = a := by
    apply hr
    have hz := ho.1
    rw [← hmatch] at hz
    exact hz
  have hshift : p.shift f.axis = f.gridFacet.anchor f.axis := by
    have he := ho.2.1
    rw [← hmatch] at he
    change p.sign f.axis * ref.centre (p.perm f.axis) + den * p.shift f.axis = _ at he
    rw [haxis, hc, mul_zero, zero_add] at he
    exact mul_left_cancel₀ hd he
  have hapex : box.apex f.axis - box.centre f.axis = p.sign f.axis * height := by
    rw [← hmatch]
    change (p.sign f.axis * ref.apex (p.perm f.axis) + den * p.shift f.axis) -
      (p.sign f.axis * ref.centre (p.perm f.axis) + den * p.shift f.axis) = _
    rw [haxis, hc, ha]
    ring
  have hs := ho.2.2
  rw [hapex] at hs
  have hs' : (f.normal * p.sign f.axis) * height =
      (if box.bump then 1 else -1) * height := by
    rw [mul_assoc, hs]
    cases box.bump <;> simp
  exact ⟨haxis, hshift, mul_right_cancel₀ hh hs'⟩

theorem Facet.inwardSlack_eq_neg_normal_mul {d : ℕ} (f : Facet d) (x : Point d) :
    f.inwardSlack x = -(f.normal : ℝ) *
      (x f.axis - (f.gridFacet.anchor f.axis : ℝ)) := by
  cases hp : f.positive <;> simp [Facet.inwardSlack, Facet.normal, hp]

/-- Exact real signed distance coordinate after inverse canonical pose. -/
theorem Pose.inwardSlack_eq_canonical_height {d : ℕ} {den height : ℤ}
    (hd : den ≠ 0) (hh : height ≠ 0) (p : Pose d)
    {f : Facet d} {box ref : BoxKey d} {a : Fin d}
    (hmatch : p.boxKey den ref = box)
    (hr : ∀ i, ref.radius i = 0 → i = a)
    (hc : ref.centre a = 0) (ha : ref.apex a = height)
    (ho : box.OrientedAt den height f) (x : Point d) :
    f.inwardSlack x = if box.bump then -(p.euclidean.symm x) a
      else (p.euclidean.symm x) a := by
  rcases p.basePlane_alignment hd hh hmatch hr hc ha ho with ⟨haxis, hshift, hsign⟩
  obtain ⟨y, rfl⟩ := p.euclidean.surjective x
  rw [p.euclidean.symm_apply_apply, f.inwardSlack_eq_neg_normal_mul,
    p.euclidean_apply, haxis, hshift]
  have hs : (f.normal : ℝ) * (p.sign f.axis : ℝ) =
      if box.bump then 1 else -1 := by exact_mod_cast hsign
  calc
    -(f.normal : ℝ) * ((p.sign f.axis : ℝ) * y a +
        (f.gridFacet.anchor f.axis : ℝ) - (f.gridFacet.anchor f.axis : ℝ)) =
        -((f.normal : ℝ) * (p.sign f.axis : ℝ)) * y a := by ring
    _ = _ := by rw [hs]; cases box.bump <;> simp

end Contact

@[simp] theorem keyPyramidHalfspaceSlack_base {n : ℕ} (k : KeyData (n + 1))
    (x : Point (n + 1)) :
    keyPyramidHalfspaceSlack k (.inl false) x = x (Fin.last n) := by
  simp [keyPyramidHalfspaceSlack, keyPyramidHalfspaceBound,
    pyramidHalfspaceBound, keyPyramidHalfspaceNormal_apply]

namespace Canonical

@[simp] theorem referenceHalfspaceSlack5_base (x : Point 5) :
    referenceHalfspaceSlack5 (.inl false) x = x 4 :=
  keyPyramidHalfspaceSlack_base _ _

@[simp] theorem referenceHalfspaceSlack7_base (x : Point 7) :
    referenceHalfspaceSlack7 (.inl false) x = x 6 :=
  keyPyramidHalfspaceSlack_base _ _

/-- The only zero reference radius is the last coordinate. -/
theorem referenceBox5_zero_radius (b : Bool) (i : Fin 5)
    (h : (referenceBox5 b).radius i = 0) : i = 4 := by
  fin_cases i <;> simp_all [referenceBox5]

theorem referenceBox7_zero_radius (b : Bool) (i : Fin 7)
    (h : (referenceBox7 b).radius i = 0) : i = 6 := by
  fin_cases i <;> simp_all [referenceBox7]

/-- The duplicated carrier/base planes have opposite inward signs for a bump,
and the same sign for a dent. -/
theorem inwardSlack_eq_posed_base5 (p : Contact.Pose 5)
    {f : Contact.Facet 5} {box : Contact.BoxKey 5}
    (hmatch : p.boxKey 19200 (referenceBox5 (!box.bump)) = box)
    (ho : box.OrientedAt 19200 80 f) (x : Point 5) :
    f.inwardSlack x = if box.bump then -posedHalfspaceSlack5 p (.inl false) x
      else posedHalfspaceSlack5 p (.inl false) x := by
  simpa only [posedHalfspaceSlack5, referenceHalfspaceSlack5_base] using
    p.inwardSlack_eq_canonical_height (by norm_num : (19200 : ℤ) ≠ 0)
      (by norm_num : (80 : ℤ) ≠ 0) hmatch (referenceBox5_zero_radius _)
      (by rfl) (by rfl) ho x

theorem inwardSlack_eq_posed_base7 (p : Contact.Pose 7)
    {f : Contact.Facet 7} {box : Contact.BoxKey 7}
    (hmatch : p.boxKey 188160 (referenceBox7 (!box.bump)) = box)
    (ho : box.OrientedAt 188160 560 f) (x : Point 7) :
    f.inwardSlack x = if box.bump then -posedHalfspaceSlack7 p (.inl false) x
      else posedHalfspaceSlack7 p (.inl false) x := by
  simpa only [posedHalfspaceSlack7, referenceHalfspaceSlack7_base] using
    p.inwardSlack_eq_canonical_height (by norm_num : (188160 : ℤ) ≠ 0)
      (by norm_num : (560 : ℤ) ≠ 0) hmatch (referenceBox7_zero_radius _)
      (by rfl) (by rfl) ho x

end Canonical

section MergedBasePlane

variable {X ι : Type*}

/-- The remaining pyramid inequalities, after removing the base atom. -/
def nonbaseHalfspaces (slack : ι → X → ℝ) (base : ι) : Set X :=
  {x | ∀ i, i ≠ base → 0 ≤ slack i x}

/-- The exact material formula with one geometric base plane. For dents the
negation applies only to the nonbase inequalities, while the carrier base
inequality remains. -/
def mergedKeyRegion (slack : ι → X → ℝ) (base : ι) (b : Bool) : Set X :=
  if b then {x | slack base x ≤ 0 ∨ x ∈ nonbaseHalfspaces slack base}
  else {x | 0 ≤ slack base x ∧ x ∉ nonbaseHalfspaces slack base}

/-- Removing the duplicate base atom is exact before closure, including all
weak inequalities on the common plane. -/
theorem keyReplacement_eq_mergedKeyRegion
    (slack : ι → X → ℝ) (base : ι) (b : Bool) {C K : Set X}
    (hC : ∀ x, x ∈ C ↔ 0 ≤ if b then -slack base x else slack base x)
    (hK : ∀ x, x ∈ K ↔ ∀ i, 0 ≤ slack i x) :
    keyReplacement C K b = mergedKeyRegion slack base b := by
  have hsplit (x : X) : (∀ i, 0 ≤ slack i x) ↔
      0 ≤ slack base x ∧ x ∈ nonbaseHalfspaces slack base := by
    constructor
    · intro h
      exact ⟨h base, fun i _ => h i⟩
    · rintro ⟨hb, hi⟩ i
      by_cases he : i = base
      · simpa only [he] using hb
      · exact hi i he
  ext x
  cases b
  · simp only [keyReplacement, Bool.false_eq_true, if_false, Set.mem_diff,
      mergedKeyRegion, Set.mem_setOf_eq, hC, hK, hsplit]
    tauto
  · simp only [keyReplacement, if_true, Set.mem_union, mergedKeyRegion,
      Set.mem_setOf_eq, hC, hK, hsplit, neg_nonneg]
    constructor
    · rintro (hc | ⟨_, hs⟩)
      · exact Or.inl hc
      · exact Or.inr hs
    · rintro (hc | hs)
      · exact Or.inl hc
      · rcases le_total (slack base x) 0 with hc | hc
        · exact Or.inl hc
        · exact Or.inr ⟨hc, hs⟩

variable [TopologicalSpace X] [Finite ι]

/-- Strict satisfaction of every nonbase inequality makes the bump locally
solid and the dent locally empty. In particular final closure cannot recreate
an artificial base face in a dent. -/
theorem localSetEq_closure_mergedKeyRegion_of_nonbase_strict
    (slack : ι → X → ℝ) (base : ι) (b : Bool) (p : X)
    (hf : ∀ i, ContinuousAt (slack i) p)
    (hp : ∀ i, i ≠ base → 0 < slack i p) :
    LocalSetEq p (closure (mergedKeyRegion slack base b)) (if b then univ else ∅) := by
  have he : ∀ᶠ x in 𝓝 p, x ∈ nonbaseHalfspaces slack base := by
    apply (eventually_inactive_nonneg slack p hf).mono
    intro x hx i hi
    exact (hx i (ne_of_gt (hp i hi))).mpr (hp i hi).le
  have h : LocalSetEq p (mergedKeyRegion slack base b) (if b then univ else ∅) := by
    apply he.mono
    intro x hx
    cases b <;> simp [mergedKeyRegion, hx]
  have hc := h.closure
  cases b <;> simpa using hc

/-- No point satisfying the strict nonbase constraints is on the physical
boundary of the closed, merged replacement. -/
theorem not_mem_frontier_closure_mergedKeyRegion_of_nonbase_strict
    (slack : ι → X → ℝ) (base : ι) (b : Bool) (p : X)
    (hf : ∀ i, ContinuousAt (slack i) p)
    (hp : ∀ i, i ≠ base → 0 < slack i p) :
    p ∉ frontier (closure (mergedKeyRegion slack base b)) := by
  have h := (localSetEq_closure_mergedKeyRegion_of_nonbase_strict
    slack base b p hf hp).frontier.mem_iff
  cases b <;> simpa using h

/-- A proved isolated physical-body germ inherits the absence of a base face. -/
theorem not_mem_frontier_of_localSetEq_mergedKeyRegion
    (slack : ι → X → ℝ) (base : ι) (b : Bool) {p : X} {T : Set X}
    (hf : ∀ i, ContinuousAt (slack i) p)
    (hp : ∀ i, i ≠ base → 0 < slack i p)
    (hT : LocalSetEq p T (closure (mergedKeyRegion slack base b))) :
    p ∉ frontier T := by
  intro hpT
  exact not_mem_frontier_closure_mergedKeyRegion_of_nonbase_strict slack base b p hf hp
    (hT.frontier.mem_iff.mp hpT)

end MergedBasePlane

/-- Relative interior of the actual box base, given by strict tangential
coordinates and the exact last-coordinate base equation. -/
def keyBaseRelativeInterior {n : ℕ} (k : KeyData (n + 1)) : Set (Point (n + 1)) :=
  {x | x (Fin.last n) = 0 ∧ ∀ i : Fin n,
    keyPyramidLo k i < x i.castSucc ∧ x i.castSucc < keyPyramidHi k i}

/-- A genuine relative-base point makes every nonbase pyramid slack strict. -/
theorem keyPyramid_nonbase_strict_of_baseRelativeInterior {n : ℕ}
    (k : KeyData (n + 1)) (hh : 0 < keyPyramidHeight k)
    {x : Point (n + 1)} (hx : x ∈ keyBaseRelativeInterior k)
    (j : PyramidHalfspaceIndex n) (hj : j ≠ .inl false) :
    0 < keyPyramidHalfspaceSlack k j x := by
  rcases j with b | ⟨i, b⟩
  · cases b
    · exact (hj rfl).elim
    · simpa [keyPyramidHalfspaceSlack, keyPyramidHalfspaceBound,
        pyramidHalfspaceBound, keyPyramidHalfspaceNormal_apply, hx.1] using hh
  · have hi := hx.2 i
    cases b <;> simp only [keyPyramidHalfspaceSlack, keyPyramidHalfspaceBound,
      pyramidHalfspaceBound, keyPyramidHalfspaceNormal_apply, hx.1,
      mul_zero, sub_zero, zero_sub, add_zero] <;> nlinarith [hi.1, hi.2]

namespace Canonical

/-- Exact material formula for a canonically certified five-dimensional key,
with the carrier atom and pyramid base atom merged. -/
theorem keyReplacement_eq_merged5 (p : Contact.Pose 5)
    {f : Contact.Facet 5} {box : Contact.BoxKey 5}
    (hmatch : p.boxKey 19200 (referenceBox5 (!box.bump)) = box)
    (ho : box.OrientedAt 19200 80 f) :
    keyReplacement f.inwardHalfspace (keySolid (box.toKeyData 19200)) box.bump =
      mergedKeyRegion (posedHalfspaceSlack5 p) (.inl false) box.bump := by
  apply keyReplacement_eq_mergedKeyRegion
  · intro x
    rw [f.mem_inwardHalfspace_iff, inwardSlack_eq_posed_base5 p hmatch ho]
  · exact mem_keySolid5_iff_posed_halfspaces p (canonical5_of_box_match p hmatch rfl)

theorem keyReplacement_eq_merged7 (p : Contact.Pose 7)
    {f : Contact.Facet 7} {box : Contact.BoxKey 7}
    (hmatch : p.boxKey 188160 (referenceBox7 (!box.bump)) = box)
    (ho : box.OrientedAt 188160 560 f) :
    keyReplacement f.inwardHalfspace (keySolid (box.toKeyData 188160)) box.bump =
      mergedKeyRegion (posedHalfspaceSlack7 p) (.inl false) box.bump := by
  apply keyReplacement_eq_mergedKeyRegion
  · intro x
    rw [f.mem_inwardHalfspace_iff, inwardSlack_eq_posed_base7 p hmatch ho]
  · exact mem_keySolid7_iff_posed_halfspaces p (canonical7_of_box_match p hmatch rfl)

/-- An actual isolated-body germ has the pruned formula with physical closure. -/
theorem localSetEq_merged5 (p : Contact.Pose 5)
    {f : Contact.Facet 5} {box : Contact.BoxKey 5} {k : KeyData 5}
    (hmatch : p.boxKey 19200 (referenceBox5 (!box.bump)) = box)
    (hdecode : box.toKeyData 19200 = k) (ho : box.OrientedAt 19200 80 f)
    {x : Point 5} {T : Set (Point 5)}
    (hT : LocalSetEq x T (closure (keyReplacement f.inwardHalfspace (keySolid k) k.bump))) :
    LocalSetEq x T (closure (mergedKeyRegion (posedHalfspaceSlack5 p) (.inl false) k.bump)) := by
  subst k
  change LocalSetEq x T (closure (keyReplacement f.inwardHalfspace
    (keySolid (box.toKeyData 19200)) box.bump)) at hT
  rw [keyReplacement_eq_merged5 p hmatch ho] at hT
  exact hT

theorem localSetEq_merged7 (p : Contact.Pose 7)
    {f : Contact.Facet 7} {box : Contact.BoxKey 7} {k : KeyData 7}
    (hmatch : p.boxKey 188160 (referenceBox7 (!box.bump)) = box)
    (hdecode : box.toKeyData 188160 = k) (ho : box.OrientedAt 188160 560 f)
    {x : Point 7} {T : Set (Point 7)}
    (hT : LocalSetEq x T (closure (keyReplacement f.inwardHalfspace (keySolid k) k.bump))) :
    LocalSetEq x T (closure (mergedKeyRegion (posedHalfspaceSlack7 p) (.inl false) k.bump)) := by
  subst k
  change LocalSetEq x T (closure (keyReplacement f.inwardHalfspace
    (keySolid (box.toKeyData 188160)) box.bump)) at hT
  rw [keyReplacement_eq_merged7 p hmatch ho] at hT
  exact hT

/-- Relative-base interior points do not lie on the physical boundary, for
both signs. For a bump the point is interior material; for a dent it is locally
outside even the final closed replacement. -/
theorem not_mem_frontier_of_baseRelativeInterior5 (p : Contact.Pose 5)
    {f : Contact.Facet 5} {box : Contact.BoxKey 5} {k : KeyData 5}
    (hmatch : p.boxKey 19200 (referenceBox5 (!box.bump)) = box)
    (hdecode : box.toKeyData 19200 = k) (ho : box.OrientedAt 19200 80 f)
    {x : Point 5} {T : Set (Point 5)}
    (hx : p.euclidean.symm x ∈ keyBaseRelativeInterior ((referenceBox5 true).toKeyData 19200))
    (hT : LocalSetEq x T (closure (keyReplacement f.inwardHalfspace (keySolid k) k.bump))) :
    x ∉ frontier T := by
  apply not_mem_frontier_of_localSetEq_mergedKeyRegion
    (posedHalfspaceSlack5 p) (.inl false) k.bump
    (fun j => (continuous_posedHalfspaceSlack5 p j).continuousAt) ?_
    (localSetEq_merged5 p hmatch hdecode ho hT)
  intro j hj
  apply keyPyramid_nonbase_strict_of_baseRelativeInterior _ ?_ hx j hj
  change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
  rw [referenceBox5_height]
  norm_num

theorem not_mem_frontier_of_baseRelativeInterior7 (p : Contact.Pose 7)
    {f : Contact.Facet 7} {box : Contact.BoxKey 7} {k : KeyData 7}
    (hmatch : p.boxKey 188160 (referenceBox7 (!box.bump)) = box)
    (hdecode : box.toKeyData 188160 = k) (ho : box.OrientedAt 188160 560 f)
    {x : Point 7} {T : Set (Point 7)}
    (hx : p.euclidean.symm x ∈ keyBaseRelativeInterior ((referenceBox7 true).toKeyData 188160))
    (hT : LocalSetEq x T (closure (keyReplacement f.inwardHalfspace (keySolid k) k.bump))) :
    x ∉ frontier T := by
  apply not_mem_frontier_of_localSetEq_mergedKeyRegion
    (posedHalfspaceSlack7 p) (.inl false) k.bump
    (fun j => (continuous_posedHalfspaceSlack7 p j).continuousAt) ?_
    (localSetEq_merged7 p hmatch hdecode ho hT)
  intro j hj
  apply keyPyramid_nonbase_strict_of_baseRelativeInterior _ ?_ hx j hj
  change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
  rw [referenceBox7_height]
  norm_num

end Canonical

#print axioms Contact.Pose.basePlane_alignment
#print axioms Canonical.inwardSlack_eq_posed_base5
#print axioms Canonical.inwardSlack_eq_posed_base7
#print axioms keyReplacement_eq_mergedKeyRegion
#print axioms localSetEq_closure_mergedKeyRegion_of_nonbase_strict
#print axioms not_mem_frontier_of_localSetEq_mergedKeyRegion
#print axioms keyPyramid_nonbase_strict_of_baseRelativeInterior
#print axioms Canonical.keyReplacement_eq_merged5
#print axioms Canonical.keyReplacement_eq_merged7
#print axioms Canonical.not_mem_frontier_of_baseRelativeInterior5
#print axioms Canonical.not_mem_frontier_of_baseRelativeInterior7

end SparseMonotiles
