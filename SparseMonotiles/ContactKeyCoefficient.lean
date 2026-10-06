module

public import SparseMonotiles.ContactKeyCodeInterface
public import SparseMonotiles.KeySupportAtlas

@[expose] public section

/-!
Material coefficient recovery from actual convex-hull solid coincidence.
The code puts every base in the facet plane and puts the apex strictly on the
side determined by its coefficient. Coordinate bounds on the whole hull then
rule out equality between the two opposite-height choices. This result is used
after registration and the collar/owner argument have established `Shared`.
-/
namespace SparseMonotiles.Contact

/-- Containment of genuine decoded solids bounds the first key's literal apex
by the second key's integer support interval. -/
theorem BoxKey.apex_bounds_of_solid_subset {d : ℕ} {den : ℤ} (hd : 0 < den)
    {a b : BoxKey d} (h : keySolid (a.toKeyData den) ⊆ keySolid (b.toKeyData den))
    (i : Fin d) : b.lowerBound i ≤ a.apex i ∧ a.apex i ≤ b.upperBound i := by
  have ha : rationalPoint (a.toKeyData den).apex ∈ keySolid (a.toKeyData den) :=
    subset_convexHull ℝ _ (Set.mem_insert _ _)
  have hb := keySolid_subset_coordinateSupport _ (h ha)
  have hi := ((b.mem_coordinateSupport_iff hd _).mp hb) i
  have hd' : (den : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have he : rationalPoint (a.toKeyData den).apex i * (den : ℝ) = (a.apex i : ℝ) := by
    change (((a.apex i : ℚ) / (den : ℚ) : ℚ) : ℝ) * (den : ℝ) = _
    simp only [Rat.cast_div, Rat.cast_intCast]
    exact div_mul_cancel₀ _ hd'
  simp only [he] at hi
  constructor
  · exact_mod_cast hi.1
  · exact_mod_cast hi.2

/-- At a common coded facet, equality of actual key solids forces equality of
material coefficients. Only the normal nondegeneracy premises are needed. -/
theorem KeyCoordinateCode.coefficient_eq_of_solid_eq {d : ℕ} (C : KeyCoordinateCode)
    {f : Facet d} {a b : BoxKey d} (hd : 0 < C.denominator) (hh : 0 < C.height)
    (ha : C.Codes f a) (hb : C.Codes f b)
    (hra : a.radius f.axis = 0) (hrb : b.radius f.axis = 0)
    (heq : keySolid (a.toKeyData C.denominator) = keySolid (b.toKeyData C.denominator)) :
    a.bump = b.bump := by
  have hca := ha.1
  have hcb := hb.1
  have hc : a.centre f.axis = b.centre f.axis := by
    simp only [KeyCoordinateCode.delta] at hca hcb
    omega
  have haa := ha.2.2 f.axis
  have hba := hb.2.2 f.axis
  simp only [ha.1, hb.1, KeyCoordinateCode.oddOffset, Int.sign_zero, zero_mul,
    add_zero, if_true] at haa hba
  have hab := BoxKey.apex_bounds_of_solid_subset hd heq.subset f.axis
  have hba' := BoxKey.apex_bounds_of_solid_subset hd heq.symm.subset f.axis
  simp only [BoxKey.lowerBound, BoxKey.upperBound, hra, hrb, sub_zero, add_zero] at hab hba'
  by_contra hne
  cases haf : a.bump <;> cases hbf : b.bump <;> cases hfp : f.positive <;>
    simp [haf, hbf, Facet.normal, hfp, KeyCoordinateCode.signedHeight] at hne haa hba <;>
    simp [haa, hba, hc, min_eq_left, max_eq_left, min_eq_right, max_eq_right,
      le_of_lt hh, le_of_lt (neg_neg_of_pos hh)] at hab hba' <;> omega

/-- Convenient form using the full explicit regularity interface. -/
theorem KeyCoordinateCode.coefficient_eq_of_regular_solid_eq {d : ℕ}
    (C : KeyCoordinateCode) {f : Facet d} {a b : BoxKey d}
    (ha : C.Codes f a) (hb : C.Codes f b)
    (hra : C.RegularKey f a) (hrb : C.RegularKey f b)
    (heq : keySolid (a.toKeyData C.denominator) = keySolid (b.toKeyData C.denominator)) :
    a.bump = b.bump :=
  C.coefficient_eq_of_solid_eq hra.1 hra.2.1 ha hb hra.2.2.1 hrb.2.2.1 heq

/-- Once the collar/owner argument gives `Shared`, actual solid coincidence
recovers the opposed material coefficients rather than assuming them. -/
theorem KeyCoordinateCode.opposite_coefficient_of_shared_solid_image {d : ℕ}
    (C : KeyCoordinateCode) {p : Pose d} {a b : Facet d} {root source : BoxKey d}
    (shared : Shared p a b) (hroot : C.Codes a root) (hsource : C.Codes b source)
    (rroot : C.RegularKey a root) (rsource : C.RegularKey b source)
    (heq : keySolid (root.toKeyData C.denominator) =
      p.euclidean '' keySolid (source.toKeyData C.denominator)) :
    root.bump = !source.bump := by
  have hm : (p.boxKey C.denominator source).radius a.axis = 0 := by
    change source.radius (p.perm a.axis) = 0
    rw [shared.2.1]
    exact rsource.2.2.1
  apply C.coefficient_eq_of_solid_eq rroot.1 rroot.2.1 hroot
    (C.codes_boxKey shared hsource) rroot.2.2.1 hm
  exact heq.trans (p.boxKey_image_keySolid (ne_of_gt rroot.1) source)

#print axioms BoxKey.apex_bounds_of_solid_subset
#print axioms KeyCoordinateCode.coefficient_eq_of_solid_eq
#print axioms KeyCoordinateCode.opposite_coefficient_of_shared_solid_image
end SparseMonotiles.Contact
