module

public import SparseMonotiles.ContactKeyCoefficient

@[expose] public section

/-!
Actual convex-hull equality recovers a full coded key signature. Tangential
apex projections are inside the base box, so the whole solid has precisely the
base's tangential coordinate extrema. Literal base corners attain those extrema.
No equality of vertex lists or profile labels is assumed.
-/
namespace SparseMonotiles.Contact

theorem BoxKey.corner_mem_decoded_base {d : ℕ} {den : ℤ} (hd : 0 < den)
    (k : BoxKey d) (hr : ∀ i, 0 ≤ k.radius i) (bits : Fin d → Bool) :
    rationalPoint (rationalVertex den (k.corner bits)) ∈ keyBase (k.toKeyData den) := by
  intro i
  change |((((k.corner bits i : ℤ) : ℚ) / (den : ℚ) : ℚ) : ℝ) -
    ((((k.centre i : ℤ) : ℚ) / (den : ℚ) : ℚ) : ℝ)| ≤
    ((((k.radius i : ℤ) : ℚ) / (den : ℚ) : ℚ) : ℝ)
  have hd' : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have hr' : (0 : ℝ) ≤ (k.radius i : ℝ) := by exact_mod_cast hr i
  cases hb : bits i <;>
    simp only [BoxKey.corner, hb, Bool.false_eq_true, if_false, if_true,
      Rat.cast_div, Rat.cast_intCast, Int.cast_sub, Int.cast_add, Int.cast_neg, sub_div, add_div, neg_div,
      add_sub_cancel_left] <;>
    simp [abs_of_nonneg (div_nonneg hr' hd'.le)]

/-- Integer coordinate bounds on any rational point of the actual hull. -/
theorem BoxKey.point_bounds_of_mem_solid {d : ℕ} {den : ℤ} (hd : 0 < den)
    {k : BoxKey d} {v : ScaledPoint d}
    (hv : rationalPoint (rationalVertex den v) ∈ keySolid (k.toKeyData den)) (i : Fin d) :
    k.lowerBound i ≤ v i ∧ v i ≤ k.upperBound i := by
  have h := ((k.mem_coordinateSupport_iff hd _).mp (keySolid_subset_coordinateSupport _ hv)) i
  have hd' : (den : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have he : rationalPoint (rationalVertex den v) i * (den : ℝ) = (v i : ℝ) := by
    change (((v i : ℚ) / (den : ℚ) : ℚ) : ℝ) * (den : ℝ) = _
    simp only [Rat.cast_div, Rat.cast_intCast]
    exact div_mul_cancel₀ _ hd'
  simp only [he] at h
  constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2

theorem KeyCoordinateCode.tangent_bounds {d : ℕ} (C : KeyCoordinateCode)
    {f : Facet d} {k : BoxKey d} (hc : C.Codes f k) (hr : C.RegularKey f k)
    {i : Fin d} (hi : i ≠ f.axis) :
    k.lowerBound i = k.centre i - k.radius i ∧
    k.upperBound i = k.centre i + k.radius i := by
  have ho := abs_lt.mp (hr.2.2.2.2 i hi)
  have ha := hc.2.2 i
  rw [if_neg hi, add_zero] at ha
  constructor
  · apply min_eq_left
    omega
  · apply max_eq_left
    omega

/-- The common base plane plus the tangential coordinate extrema determine
all centre coordinates from equality of actual solids. -/
theorem KeyCoordinateCode.centre_eq_of_regular_solid_eq {d : ℕ}
    (C : KeyCoordinateCode) {f : Facet d} {a b : BoxKey d}
    (ha : C.Codes f a) (hb : C.Codes f b)
    (ra : C.RegularKey f a) (rb : C.RegularKey f b)
    (heq : keySolid (a.toKeyData C.denominator) = keySolid (b.toKeyData C.denominator)) :
    a.centre = b.centre := by
  funext i
  by_cases hi : i = f.axis
  · subst i
    have hca := ha.1
    have hcb := hb.1
    simp only [KeyCoordinateCode.delta] at hca hcb
    omega
  · have ac (bits : Fin d → Bool) :
        rationalPoint (rationalVertex C.denominator (a.corner bits)) ∈
          keySolid (a.toKeyData C.denominator) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _
        (a.corner_mem_decoded_base ra.1 ra.2.2.2.1 bits))
    have bc (bits : Fin d → Bool) :
        rationalPoint (rationalVertex C.denominator (b.corner bits)) ∈
          keySolid (b.toKeyData C.denominator) :=
      subset_convexHull ℝ _ (Set.mem_insert_of_mem _
        (b.corner_mem_decoded_base rb.1 rb.2.2.2.1 bits))
    have h1 := BoxKey.point_bounds_of_mem_solid ra.1 (heq ▸ ac (fun _ => false)) i
    have h2 := BoxKey.point_bounds_of_mem_solid ra.1 (heq ▸ ac (fun _ => true)) i
    have h3 := BoxKey.point_bounds_of_mem_solid ra.1 (heq.symm ▸ bc (fun _ => false)) i
    have h4 := BoxKey.point_bounds_of_mem_solid ra.1 (heq.symm ▸ bc (fun _ => true)) i
    rcases C.tangent_bounds ha ra hi with ⟨hal, hau⟩
    rcases C.tangent_bounds hb rb hi with ⟨hbl, hbu⟩
    simp only [hal, hau, hbl, hbu, BoxKey.corner, Bool.false_eq_true, if_false,
      if_true] at h1 h2 h3 h4
    omega

/-- Full signature recovery, including the material coefficient, from genuine
solid equality under the explicitly stated static code/regularity conditions. -/
theorem KeyCoordinateCode.eq_of_regular_solid_eq {d : ℕ}
    (C : KeyCoordinateCode) {f : Facet d} {a b : BoxKey d}
    (ha : C.Codes f a) (hb : C.Codes f b)
    (ra : C.RegularKey f a) (rb : C.RegularKey f b)
    (heq : keySolid (a.toKeyData C.denominator) = keySolid (b.toKeyData C.denominator)) :
    a = b :=
  C.eq_of_centre_coefficient ha hb (C.centre_eq_of_regular_solid_eq ha hb ra rb heq)
    (C.coefficient_eq_of_regular_solid_eq ha hb ra rb heq)

/-- Regularity is covariant in the opposed-normal comparison convention. -/
theorem KeyCoordinateCode.regular_boxKey {d : ℕ} (C : KeyCoordinateCode)
    {p : Pose d} {a b : Facet d} (shared : Shared p a b) {k : BoxKey d}
    (hr : C.RegularKey b k) : C.RegularKey a (p.boxKey C.denominator k) := by
  refine ⟨hr.1, hr.2.1, ?_, ?_, ?_⟩
  · change k.radius (p.perm a.axis) = 0
    rw [shared.2.1]
    exact hr.2.2.1
  · intro i
    exact hr.2.2.2.1 (p.perm i)
  · intro i hi
    have hpi : p.perm i ≠ b.axis := by
      intro he
      apply hi
      apply p.perm.injective
      exact he.trans shared.2.1.symm
    rw [C.delta_boxKey shared, C.oddOffset_signed]
    have hh := hr.2.2.2.2 (p.perm i) hpi
    change |p.sign i * C.oddOffset (C.delta b k (p.perm i))| < k.radius (p.perm i)
    cases hn : p.negative i <;> simpa [Pose.sign, hn] using hh

/-- After the independent matched-solid→Shared adapter, actual solid equality
recovers precisely the full signed-pose key match used by the finite checker. -/
theorem KeyCoordinateCode.eq_boxKey_of_shared_solid_image {d : ℕ}
    (C : KeyCoordinateCode) {p : Pose d} {a b : Facet d} {root source : BoxKey d}
    (shared : Shared p a b) (hroot : C.Codes a root) (hsource : C.Codes b source)
    (rroot : C.RegularKey a root) (rsource : C.RegularKey b source)
    (heq : keySolid (root.toKeyData C.denominator) =
      p.euclidean '' keySolid (source.toKeyData C.denominator)) :
    root = p.boxKey C.denominator source := by
  exact C.eq_of_regular_solid_eq hroot (C.codes_boxKey shared hsource) rroot
    (C.regular_boxKey shared rsource)
    (heq.trans (p.boxKey_image_keySolid (ne_of_gt rroot.1) source))

#print axioms KeyCoordinateCode.centre_eq_of_regular_solid_eq
#print axioms KeyCoordinateCode.eq_of_regular_solid_eq
#print axioms KeyCoordinateCode.eq_boxKey_of_shared_solid_image
end SparseMonotiles.Contact
