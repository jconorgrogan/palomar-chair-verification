module

public import PrimeFacetClosure.NativeStarHolonomy
public import PhysicalRegistration.RegisteredWorldBridge

@[expose] public section

/-! Actual native contact-graph walk transport and uniqueness of the complete
ambient isometry. This supplies the geometric candidate/path identification;
no equality of a candidate with a path product is assumed. -/
namespace PhysicalRegistration.NativeChair.NativeWalkTransport
noncomputable section
open scoped InnerProductSpace
open RegisteredPrime
open RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy

@[simp] theorem placedNormal_refl {m : ℕ} (x : Space m) :
    placedNormal (IsometryEquiv.refl (Space m)) x = x := by
  rw [placedNormal_eq_sub_zero]
  change x - 0 = x
  exact sub_zero x

/-- Isometry composition has the same right-to-left order as frame composition. -/
theorem placedNormal_comp {m : ℕ} (f g : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal (g.trans f) x = placedNormal f (placedNormal g x) := by
  have h := f.toRealAffineIsometryEquiv.map_vsub (g x) (g 0)
  change placedNormal f (g x - g 0) = f (g x) - f (g 0) at h
  rw [placedNormal_eq_sub_zero g, h, placedNormal_eq_sub_zero]
  rfl

@[simp] theorem placedNormal_symm_cancel {m : ℕ} (f : Space m ≃ᵢ Space m) (x : Space m) :
    placedNormal f (placedNormal f.symm x) = x := by
  rw [← placedNormal_comp]
  have he : f.symm.trans f = IsometryEquiv.refl (Space m) := by
    apply IsometryEquiv.ext
    intro y
    exact f.apply_symm_apply y
  rw [he, placedNormal_refl]

/-- Reversing a graph edge uses the actual inverse placement. -/
theorem siteTransport_symm {m : ℕ} {f : Space m ≃ᵢ Space m} {u v : Site m}
    (h : SiteTransport f u v) : SiteTransport f.symm v u := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    apply f.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    change placedNormal f (placedNormal f.symm (siteAxis u j)) = placedNormal f (siteAxis v j)
    rw [placedNormal_symm_cancel, h.1 j]
  · apply f.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    change placedNormal f (placedNormal f.symm (outward u.1)) = placedNormal f (-outward v.1)
    rw [placedNormal_symm_cancel]
    simp only [placedNormal, map_neg]
    change outward u.1 = -placedNormal f (outward v.1)
    rw [h.2.1, neg_neg]
  · apply f.injective
    simpa only [f.apply_symm_apply] using h.2.2.symm

/-- A complete native tangent frame and its normal separate all ambient
vectors. This is the free-orbit full-frame argument, with no sampled axis. -/
theorem native_frame_separates {m : ℕ} (u : Site m) {x y : Space m}
    (ht : ∀ j, ⟪siteAxis u j, x⟫_ℝ = ⟪siteAxis u j, y⟫_ℝ)
    (hn : ⟪outward u.1, x⟫_ℝ = ⟪outward u.1, y⟫_ℝ) : x = y := by
  ext i
  obtain ⟨j, rfl⟩ := (nativeFrameIndex u).surjective i
  cases j with
  | none =>
    simp only [nativeFrameIndex_none]
    rw [outward_inner_coordinate, outward_inner_coordinate] at hn
    have hs : normalSign u.1 ≠ 0 := by
      intro hz
      have h := abs_normalSign u.1
      rw [hz, abs_zero] at h
      norm_num at h
    exact mul_left_cancel₀ hs hn
  | some j =>
    simp only [nativeFrameIndex_some]
    have h := ht j
    rw [siteAxis_inner_coordinate, siteAxis_inner_coordinate] at h
    have hs : sign (u.2.2 j) ≠ 0 := by cases u.2.2 j <;> norm_num [sign]
    exact mul_left_cancel₀ hs h

/-- The full tangent frame and reversed normal determine the entire linear
map; the matched site center then determines its translation. -/
theorem siteTransport_unique {m : ℕ} {f g : Space m ≃ᵢ Space m} {u v : Site m}
    (hf : SiteTransport f u v) (hg : SiteTransport g u v) : f = g := by
  have hl (x : Space m) : placedNormal f x = placedNormal g x := by
    apply native_frame_separates u
    · intro j
      have h1 := placedNormal_inner_map_map f (siteAxis v j) x
      have h2 := placedNormal_inner_map_map g (siteAxis v j) x
      rw [hf.1 j] at h1
      rw [hg.1 j] at h2
      exact h1.trans h2.symm
    · have h1 := placedNormal_inner_map_map f (outward v.1) x
      have h2 := placedNormal_inner_map_map g (outward v.1) x
      rw [hf.2.1] at h1
      rw [hg.2.1] at h2
      simpa only [inner_neg_left, neg_inj] using h1.trans h2.symm
  have hzero : f 0 = g 0 := by
    have h := hl (siteCenter v)
    rw [placedNormal_eq_sub_zero, placedNormal_eq_sub_zero, hf.2.2, hg.2.2] at h
    exact sub_right_injective h
  ext x i
  have h := hl x
  rw [placedNormal_eq_sub_zero, placedNormal_eq_sub_zero, hzero] at h
  exact congrArg (fun z : Space m => z i) (sub_left_injective h)

/-- There exists a correctly directed generator or inverse generator on every
literal undirected native-site edge. -/
theorem exists_edge_placement {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    ∃ e : Space m ≃ᵢ Space m, SiteTransport e u v := by
  obtain ⟨g, _, h⟩ := h
  rcases h with h | h
  · exact ⟨g, h⟩
  · exact ⟨g.symm, siteTransport_symm h⟩

def edgePlacement {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) : Space m ≃ᵢ Space m :=
  (exists_edge_placement A hA h).choose

theorem edgePlacement_spec {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    SiteTransport (edgePlacement A hA h) u v :=
  (exists_edge_placement A hA h).choose_spec


/-- The chosen placement really is a generating isometry or the inverse of
one; the use of choice does not introduce additional graph generators. -/
theorem edgePlacement_generator_or_inverse {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    ∃ g ∈ A, edgePlacement A hA h = g ∨ edgePlacement A hA h = g.symm := by
  have hc := edgePlacement_spec A hA h
  obtain ⟨g, hg, ht⟩ := h
  rcases ht with ht | ht
  · exact ⟨g, hg, Or.inl (siteTransport_unique hc ht)⟩
  · exact ⟨g, hg, Or.inr (siteTransport_unique hc (siteTransport_symm ht))⟩

/-- Actual isometry product along a finite graph walk, directed from the
terminal native site into the initial site's coordinates. -/
def walkPlacement {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} : (contactGraph A hA).Walk u v → Space m ≃ᵢ Space m
  | .nil => IsometryEquiv.refl _
  | .cons h w => (walkPlacement A hA w).trans (edgePlacement A hA h)

/-- Literal path induction preserves every tangent axis and the exact center;
only the normal is reversed according to ordinary walk parity. -/
theorem walkPlacement_spec {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (w : (contactGraph A hA).Walk u v) :
    (∀ j, placedNormal (walkPlacement A hA w) (siteAxis v j) = siteAxis u j) ∧
    placedNormal (walkPlacement A hA w) (outward v.1) =
      (if StarGauge.lengthOdd w then -outward u.1 else outward u.1) ∧
    walkPlacement A hA w (siteCenter v) = siteCenter u := by
  induction w with
  | nil =>
    exact ⟨fun j => placedNormal_refl _, placedNormal_refl _, rfl⟩
  | @cons u v z h w ih =>
    have he := edgePlacement_spec A hA h
    constructor
    · intro j
      rw [walkPlacement, placedNormal_comp, ih.1 j, he.1 j]
    constructor
    · simp only [walkPlacement, placedNormal_comp, StarGauge.lengthOdd]
      rw [ih.2.1]
      by_cases hb : StarGauge.lengthOdd w = true
      · simp only [hb, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
        simp only [placedNormal, map_neg]
        change -placedNormal (edgePlacement A hA h) (outward v.1) = outward u.1
        rw [he.2.1, neg_neg]
      · have hb' : StarGauge.lengthOdd w = false := by simpa using hb
        simp only [hb', Bool.false_eq_true, ↓reduceIte, Bool.not_false]
        exact he.2.1
    · change edgePlacement A hA h (walkPlacement A hA w (siteCenter z)) = _
      rw [ih.2.2, he.2.2]


/-- The usual signed power form of the same normal-parity law. -/
theorem walkPlacement_normal_power {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (w : (contactGraph A hA).Walk u v) :
    placedNormal (walkPlacement A hA w) (outward v.1) =
      ((-1 : ℝ) ^ w.length) • outward u.1 := by
  induction w with
  | nil => simp only [walkPlacement, placedNormal_refl, SimpleGraph.Walk.length_nil, pow_zero, one_smul]
  | @cons u v z h w ih =>
    rw [walkPlacement, placedNormal_comp, ih]
    simp only [placedNormal, map_smul]
    change ((-1 : ℝ) ^ w.length) • placedNormal (edgePlacement A hA h) (outward v.1) = _
    rw [(edgePlacement_spec A hA h).2.1]
    simp only [SimpleGraph.Walk.length_cons, pow_succ, mul_smul, neg_one_smul]

/-- An odd actual graph walk has exactly the native `SiteTransport` predicate. -/
theorem odd_walk_siteTransport {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (w : (contactGraph A hA).Walk u v) (hw : w.length % 2 = 1) :
    SiteTransport (walkPlacement A hA w) u v := by
  have hh := walkPlacement_spec A hA w
  have hb := (StarGauge.lengthOdd_eq_true_iff w).mpr hw
  simpa only [SiteTransport, hb, Bool.true_eq, ↓reduceIte] using hh

/-- Candidate/path equality is proved from complete tangent, reversed-normal,
and center equations. It is not a graph-closure premise. -/
theorem odd_walk_equals_candidate {m : ℕ}
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (w : (contactGraph A hA).Walk u v) (hw : w.length % 2 = 1)
    {e : Space m ≃ᵢ Space m} (he : SiteTransport e u v) :
    walkPlacement A hA w = e :=
  siteTransport_unique (odd_walk_siteTransport A hA w hw) he

/-- Opposite actual graph coefficients identify any candidate with an actual
finite product of generating contacts and their inverses. -/
theorem opposite_coefficients_candidate_walk
    {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} {e : Space m ≃ᵢ Space m} (he : SiteTransport e u v)
    (ha : (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u) :
    ∃ w : (contactGraph A hA).Walk u v,
      w.length % 2 = 1 ∧ walkPlacement A hA w = e := by
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk A hA ha
  exact ⟨w, hw, odd_walk_equals_candidate A hA w hw he⟩

#print axioms siteTransport_unique
#print axioms edgePlacement_generator_or_inverse
#print axioms walkPlacement_normal_power
#print axioms walkPlacement_spec
#print axioms odd_walk_equals_candidate
#print axioms opposite_coefficients_candidate_walk
end
end PhysicalRegistration.NativeChair.NativeWalkTransport
