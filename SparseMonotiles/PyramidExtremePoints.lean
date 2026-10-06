module

public import SparseMonotiles.ReferenceKeyHalfspaces
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-!
# All and only the pyramid vertices

A rectangular-base pyramid is the convex hull of its apex and its finitely many
base corners. At strictly positive height these are exactly its extreme points.
The apex projection is arbitrary; no centering or interior-projection condition
is used. Nonnegative base widths suffice for the set equality, so positive
widths are a special case.
-/
namespace SparseMonotiles

/-- The actual base corners, with coincident corners identified as a set. -/
def pyramidCorners {n : ℕ} (lo hi : Fin n → ℝ) : Set (PyramidPoint n) :=
  {p | p.2 = 0 ∧ ∀ i, p.1 i = lo i ∨ p.1 i = hi i}

/-- Boolean corner enumeration, with `true` choosing the upper endpoint. -/
def pyramidCorner {n : ℕ} (lo hi : Fin n → ℝ) (b : Fin n → Bool) : PyramidPoint n :=
  (fun i => if b i then hi i else lo i, 0)

/-- `none` is the apex; `some b` is the corner indexed by `b`. -/
def pyramidVertex {n : ℕ} (lo hi o : Fin n → ℝ) (h : ℝ) :
    Option (Fin n → Bool) → PyramidPoint n
  | none => (o, h)
  | some b => pyramidCorner lo hi b

theorem range_pyramidCorner {n : ℕ} (lo hi : Fin n → ℝ) :
    Set.range (pyramidCorner lo hi) = pyramidCorners lo hi := by
  classical
  ext p
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨rfl, ?_⟩
    intro i
    simp only [pyramidCorner]
    cases b i <;> simp
  · rintro ⟨hp, hc⟩
    refine ⟨fun i => decide (p.1 i = hi i), ?_⟩
    apply Prod.ext
    · funext i
      change (if decide (p.1 i = hi i) then hi i else lo i) = p.1 i
      by_cases he : p.1 i = hi i
      · simp [he]
      · have hl : p.1 i = lo i := (hc i).resolve_right he
        simpa [he] using hl.symm
    · exact hp.symm

theorem range_pyramidVertex {n : ℕ} (lo hi o : Fin n → ℝ) (h : ℝ) :
    Set.range (pyramidVertex lo hi o h) = insert (o, h) (pyramidCorners lo hi) := by
  rw [← range_pyramidCorner lo hi]
  ext p
  constructor
  · rintro ⟨b, rfl⟩
    cases b with
    | none => exact Set.mem_insert _ _
    | some b => exact Set.mem_insert_of_mem _ ⟨b, rfl⟩
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨none, rfl⟩
    · exact ⟨some b, rfl⟩

theorem finite_pyramidVertices {n : ℕ} (lo hi o : Fin n → ℝ) (h : ℝ) :
    (insert (o, h) (pyramidCorners lo hi)).Finite := by
  rw [← range_pyramidVertex lo hi o h]
  exact Set.finite_range _

theorem pyramidCorners_subset_base {n : ℕ} (lo hi : Fin n → ℝ)
    (hw : ∀ i, lo i ≤ hi i) : pyramidCorners lo hi ⊆ pyramidBase lo hi := by
  rintro p ⟨hp, hc⟩
  refine ⟨hp, fun i => ?_⟩
  rcases hc i with hl | hh
  · rw [hl]
    exact ⟨le_rfl, hw i⟩
  · rw [hh]
    exact ⟨hw i, le_rfl⟩

/-- The box in height zero is the finite-corner convex hull. -/
theorem convexHull_pyramidCorners {n : ℕ} (lo hi : Fin n → ℝ)
    (hw : ∀ i, lo i ≤ hi i) :
    convexHull ℝ (pyramidCorners lo hi) = pyramidBase lo hi := by
  have hc : pyramidCorners lo hi =
      (Set.univ.pi (fun i => ({lo i, hi i} : Set ℝ))) ×ˢ ({0} : Set ℝ) := by
    ext p
    simp only [pyramidCorners, Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi,
      Set.mem_univ, forall_const, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact and_comm
  rw [hc, convexHull_prod, convexHull_pi, convexHull_singleton]
  simp_rw [convexHull_pair, segment_eq_Icc (hw _)]
  ext p
  simp only [pyramidBase, Set.mem_setOf_eq, Set.mem_prod, Set.mem_pi,
    Set.mem_univ, forall_const, Set.mem_Icc, Set.mem_singleton_iff]
  exact and_comm

/-- The complete solid is already the convex hull of the finite vertex set. -/
theorem pyramidSolid_eq_convexHull_vertices {n : ℕ} (lo hi o : Fin n → ℝ) (h : ℝ)
    (hw : ∀ i, lo i ≤ hi i) :
    pyramidSolid lo hi o h = convexHull ℝ (insert (o, h) (pyramidCorners lo hi)) := by
  unfold pyramidSolid
  rw [← convexHull_pyramidCorners lo hi hw]
  simpa only [Set.singleton_union] using
    convexHull_convexHull_union_right (𝕜 := ℝ) ({(o, h)} : Set (PyramidPoint n))
      (pyramidCorners lo hi)

private theorem weighted_eq_lower {a b x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : z ≤ x) (hy : z ≤ y) (he : a * x + b * y = z) : x = z := by
  have hz : (a + b) * z = z := by rw [hab, one_mul]
  have hle : a * (x - z) ≤ 0 := by
    nlinarith [mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hy)]
  have hsub : x - z ≤ 0 := by
    by_contra hs
    exact (not_lt_of_ge hle) (mul_pos ha (lt_of_not_ge hs))
  linarith

private theorem weighted_eq_upper {a b x y z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hx : x ≤ z) (hy : y ≤ z) (he : a * x + b * y = z) : x = z := by
  have hn := weighted_eq_lower ha hb hab (neg_le_neg hx) (neg_le_neg hy)
    (show a * (-x) + b * (-y) = -z by nlinarith [he])
  linarith

/-- The maximum-height point is extreme, wherever the apex projects. -/
theorem apex_mem_extremePoints_pyramidSolid {n : ℕ} (lo hi o : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) :
    (o, h) ∈ (pyramidSolid lo hi o h).extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨subset_convexHull ℝ _ (Set.mem_insert _ _), ?_⟩
  intro p hp q hq hs
  rw [pyramidSolid_eq_halfspaces lo hi o hh] at hp hq
  rcases hs with ⟨a, b, ha, hb, hab, he⟩
  have heh : a * p.2 + b * q.2 = h := congrArg Prod.snd he
  have hph := weighted_eq_upper ha hb hab hp.2.1 hq.2.1 heh
  exact eq_apex_of_mem_pyramidHalfspaces_of_height_eq lo hi o hh hp hph

/-- Every base corner remains extreme after adjoining a positive-height apex. -/
theorem pyramidCorners_subset_extremePoints {n : ℕ} (lo hi o : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) (hw : ∀ i, lo i ≤ hi i) :
    pyramidCorners lo hi ⊆ (pyramidSolid lo hi o h).extremePoints ℝ := by
  intro c hc
  apply mem_extremePoints_iff_left.mpr
  refine ⟨subset_convexHull ℝ _ (Set.mem_insert_of_mem _
    (pyramidCorners_subset_base lo hi hw hc)), ?_⟩
  intro p hp q hq hs
  rw [pyramidSolid_eq_halfspaces lo hi o hh] at hp hq
  rcases hs with ⟨a, b, ha, hb, hab, he⟩
  have heh : a * p.2 + b * q.2 = 0 := by
    have he' := congrArg Prod.snd he
    change a * p.2 + b * q.2 = c.2 at he'
    simpa only [hc.1] using he'
  have hp0 : p.2 = 0 := weighted_eq_lower ha hb hab hp.1 hq.1 heh
  have hq0 : q.2 = 0 := weighted_eq_lower hb ha (by linarith) hq.1 hp.1
    (by nlinarith [heh])
  have pb (i : Fin n) : lo i ≤ p.1 i ∧ p.1 i ≤ hi i := by
    have hi := hp.2.2 i
    simp only [hp0, sub_zero, zero_mul, add_zero] at hi
    constructor <;> nlinarith [hi.1, hi.2]
  have qb (i : Fin n) : lo i ≤ q.1 i ∧ q.1 i ≤ hi i := by
    have hi := hq.2.2 i
    simp only [hq0, sub_zero, zero_mul, add_zero] at hi
    constructor <;> nlinarith [hi.1, hi.2]
  apply Prod.ext
  · funext i
    have hei : a * p.1 i + b * q.1 i = c.1 i :=
      congrArg (fun z : PyramidPoint n => z.1 i) he
    rcases hc.2 i with hl | hu
    · rw [hl] at hei ⊢
      exact weighted_eq_lower ha hb hab (pb i).1 (qb i).1 hei
    · rw [hu] at hei ⊢
      exact weighted_eq_upper ha hb hab (pb i).2 (qb i).2 hei
  · exact hp0.trans hc.1.symm

/-- Exactly the apex and box corners are extreme; no other points occur. -/
theorem extremePoints_pyramidSolid {n : ℕ} (lo hi o : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) (hw : ∀ i, lo i ≤ hi i) :
    (pyramidSolid lo hi o h).extremePoints ℝ = insert (o, h) (pyramidCorners lo hi) := by
  apply Set.Subset.antisymm
  · rw [pyramidSolid_eq_convexHull_vertices lo hi o h hw]
    exact extremePoints_convexHull_subset
  · exact Set.insert_subset (apex_mem_extremePoints_pyramidSolid lo hi o hh)
      (pyramidCorners_subset_extremePoints lo hi o hh hw)

/-- The same endpoint in the finite Boolean-indexed vertex interface. -/
theorem extremePoints_pyramidSolid_eq_range {n : ℕ} (lo hi o : Fin n → ℝ)
    {h : ℝ} (hh : 0 < h) (hw : ∀ i, lo i ≤ hi i) :
    (pyramidSolid lo hi o h).extremePoints ℝ = Set.range (pyramidVertex lo hi o h) := by
  rw [extremePoints_pyramidSolid lo hi o hh hw, range_pyramidVertex]

/-- Exact extreme-point equality transported to the actual Euclidean key solid. -/
theorem pointPyramidEquiv_image_extremePoints_keySolid {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ i, keyPyramidLo k i ≤ keyPyramidHi k i) :
    pointPyramidEquiv n '' (keySolid k).extremePoints ℝ =
      insert (keyPyramidApex k, keyPyramidHeight k)
        (pyramidCorners (keyPyramidLo k) (keyPyramidHi k)) := by
  rw [image_extremePoints (pointPyramidEquiv n), pointPyramidEquiv_image_keySolid k hc hr]
  exact extremePoints_pyramidSolid _ _ _ hh hw

#print axioms convexHull_pyramidCorners
#print axioms pyramidSolid_eq_convexHull_vertices
#print axioms extremePoints_pyramidSolid
#print axioms pointPyramidEquiv_image_extremePoints_keySolid

end SparseMonotiles
