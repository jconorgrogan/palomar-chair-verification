module

public import SparseMonotiles.CanonicalRidgeNormals
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

@[expose] public section

/-!
# Independence of active pyramid normals

Away from the apex, coordinate injectivity of incident facets supplies actual
linear independence of their Euclidean outward normals. This is an algebraic
rank statement, independent of any tiling or transverse-section assumption.
-/
namespace SparseMonotiles

noncomputable def pyramidFacetSlopeNormal {n : ℕ} (slope : Fin n → Bool → ℝ) :
    PyramidFacetIndex n → Point (n + 1)
  | none => pyramidBaseNormal n
  | some (i, b) => pyramidSlopeNormal i b (slope i b)

/-- Any finite family with distinct base/tangential coordinates has independent
normals, provided that each tangential slope is nonzero. -/
theorem pyramidFacetSlopeNormal_linearIndependent {n : ℕ} {ι : Type*} [Fintype ι]
    (slope : Fin n → Bool → ℝ) (hs : ∀ i b, slope i b ≠ 0)
    (f : ι → PyramidFacetIndex n)
    (hf : Function.Injective (pyramidFacetCoordinate ∘ f)) :
    LinearIndependent ℝ (fun a => pyramidFacetSlopeNormal slope (f a)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  have hside (a : ι) (i : Fin n) (b : Bool) (ha : f a = some (i, b)) : g a = 0 := by
    have hoff (c : ι) (hca : c ≠ a) :
        pyramidFacetSlopeNormal slope (f c) i.castSucc = 0 := by
      cases hc : f c with
      | none => simp [pyramidFacetSlopeNormal, pyramidBaseNormal, EuclideanSpace.single_apply]
      | some u =>
          rcases u with ⟨j, d⟩
          have hij : i ≠ j := by
            intro hij
            apply hca
            apply hf
            simp [Function.comp_def, ha, hc, pyramidFacetCoordinate, hij]
          exact pyramidSlopeNormal_other i j hij d (slope j d)
    have heval : (∑ c, g c * pyramidFacetSlopeNormal slope (f c) i.castSucc) = 0 := by
      simpa using congrArg (EuclideanSpace.proj i.castSucc) hg
    have hmul : g a * (if b then slope i b else -slope i b) = 0 := by
      rw [Finset.sum_eq_single a] at heval
      · simpa [ha, pyramidFacetSlopeNormal] using heval
      · intro c _ hca
        rw [hoff c hca, mul_zero]
      · intro ha
        exact False.elim (ha (Finset.mem_univ _))
    have hne : (if b then slope i b else -slope i b) ≠ 0 := by
      cases b
      · simpa using hs i false
      · exact hs i true
    exact (mul_eq_zero.mp hmul).resolve_right hne
  intro a
  cases ha : f a with
  | some u => exact hside a u.1 u.2 ha
  | none =>
      have hoff (c : ι) (hca : c ≠ a) : g c = 0 := by
        cases hc : f c with
        | some u => exact hside c u.1 u.2 hc
        | none =>
            exact False.elim (hca (hf (by simp [Function.comp_def, ha, hc])))
      rw [Finset.sum_eq_single a] at hg
      · have heval := congrArg (EuclideanSpace.proj (Fin.last n)) hg
        simpa [ha, pyramidFacetSlopeNormal, pyramidBaseNormal,
          EuclideanSpace.single_apply] using heval
      · intro c _ hca
        rw [hoff c hca, zero_smul]
      · intro ha
        exact False.elim (ha (Finset.mem_univ _))

/-- In particular, all active facet normals below the apex are independent. -/
theorem active_pyramidFacetSlopeNormal_linearIndependent {n : ℕ}
    (lo hi o : Fin n → ℝ) {h : ℝ} {p : PyramidPoint n}
    (hwidth : ∀ i, lo i < hi i) (hph : p.2 < h)
    (slope : Fin n → Bool → ℝ) (hs : ∀ i b, slope i b ≠ 0) :
    LinearIndependent ℝ (fun a : ↥(pyramidActiveFacets lo hi o h p) =>
      pyramidFacetSlopeNormal slope a.1) := by
  apply pyramidFacetSlopeNormal_linearIndependent slope hs Subtype.val
  intro a b hab
  apply Subtype.ext
  exact pyramidFacetCoordinate_injOn_active_below_apex lo hi o hwidth hph
    a.property b.property hab

/-- The common normal equations through a point, as an affine subspace. -/
noncomputable def normalAffineIntersection {d : ℕ} {ι : Type*}
    (N : ι → Point d) (p : Point d) : AffineSubspace ℝ (Point d) :=
  AffineSubspace.mk' p (Submodule.span ℝ (Set.range N))ᗮ

theorem mem_normalAffineIntersection_iff {d : ℕ} {ι : Type*}
    (N : ι → Point d) (p x : Point d) :
    x ∈ normalAffineIntersection N p ↔
      ∀ i, inner (𝕜 := ℝ) (N i) x = inner (𝕜 := ℝ) (N i) p := by
  rw [normalAffineIntersection, AffineSubspace.mem_mk']
  change x - p ∈ (Submodule.span ℝ (Set.range N))ᗮ ↔ _
  constructor
  · intro hx i
    have hi := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self i)) hx
    exact sub_eq_zero.mp (by simpa only [inner_sub_right] using hi)
  · intro hx v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        rcases hv with ⟨i, rfl⟩
        rw [inner_sub_right, hx i, sub_self]
    | zero => simp
    | add v w hv hw hiv hiw => simp only [inner_add_left, hiv, hiw, add_zero]
    | smul r v hv hiv => simp only [inner_smul_left, hiv, mul_zero]

/-- Rank-nullity, with the normal rank premise stated explicitly. -/
theorem normalAffineIntersection_codimension {d : ℕ} {ι : Type*} [Fintype ι]
    (N : ι → Point d) (hN : LinearIndependent ℝ N) (p : Point d) :
    Module.finrank ℝ (normalAffineIntersection N p).direction + Fintype.card ι = d := by
  rw [normalAffineIntersection, AffineSubspace.direction_mk']
  have hd := (Submodule.span ℝ (Set.range N)).finrank_add_finrank_orthogonal
  rw [finrank_span_eq_card hN, finrank_euclideanSpace_fin] at hd
  omega

/-- Positive rescaling identifies equality of the actual supporting forms with
 equality of the normalized Euclidean inner products. -/
theorem key_facet_form_eq_iff_normal_inner_eq {n : ℕ} (k : KeyData (n + 1))
    (hd : ∀ i b, 0 < keySideDistance k i b) (a : PyramidFacetIndex n)
    (x y : Point (n + 1)) :
    keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex a) x =
        keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex a) y ↔
      inner (𝕜 := ℝ) (pyramidFacetSlopeNormal (keySideSlope k) a) x =
        inner (𝕜 := ℝ) (pyramidFacetSlopeNormal (keySideSlope k) a) y := by
  cases a with
  | none =>
      change -x (Fin.last n) = -y (Fin.last n) ↔ _
      rw [show pyramidFacetSlopeNormal (keySideSlope k) none = pyramidBaseNormal n from rfl,
        inner_pyramidBaseNormal, inner_pyramidBaseNormal]
  | some u =>
      rcases u with ⟨i, b⟩
      change keyPyramidHalfspaceNormal k (.inr (i, b)) x =
        keyPyramidHalfspaceNormal k (.inr (i, b)) y ↔ _
      rw [key_side_form_eq_distance_mul_inner k i b (hd i b),
        key_side_form_eq_distance_mul_inner k i b (hd i b)]
      exact mul_right_inj' (ne_of_gt (hd i b))

/-- Three distinct incident planes of an actual key, away from its apex, have a
common affine intersection of codimension exactly three. No rank hypothesis is
assumed: nonzero slopes and active-coordinate injectivity establish it. -/
theorem active_key_triple_codimension_three {n : ℕ} (k : KeyData (n + 1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hwidth : ∀ i, keyPyramidLo k i < keyPyramidHi k i)
    (hd : ∀ i b, 0 < keySideDistance k i b)
    {p : Point (n + 1)} (hp : p ∈ keySolid k) (hne : p ≠ rationalPoint k.apex)
    (f : Fin 3 → PyramidFacetIndex n) (hf : Function.Injective f)
    (hactive : ∀ i, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f i)) p = 0) :
    ∃ L : AffineSubspace ℝ (Point (n + 1)),
      Module.finrank ℝ L.direction + 3 = n + 1 ∧
      ∀ x, x ∈ L ↔ ∀ i, keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex (f i)) x = 0 := by
  have hph := key_height_lt_of_ne_apex k hc hr hh hp hne
  have hmem (i : Fin 3) : pointPyramidEquiv n p ∈
      pyramidFacetPlane (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k)
        (keyPyramidHeight k) (f i) := by
    rw [mem_pyramidFacetPlane_iff]
    exact (sub_eq_zero.mp (hactive i)).symm
  have hinj : Function.Injective (pyramidFacetCoordinate ∘ f) := by
    intro i j hij
    apply hf
    exact pyramidFacetCoordinate_injOn_active_below_apex
      (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) hwidth hph
      ((mem_pyramidActiveFacets _ _ _ _ _ _).mpr (hmem i))
      ((mem_pyramidActiveFacets _ _ _ _ _ _).mpr (hmem j)) hij
  let N := fun i => pyramidFacetSlopeNormal (keySideSlope k) (f i)
  have hN : LinearIndependent ℝ N := pyramidFacetSlopeNormal_linearIndependent
    (keySideSlope k) (fun i b => div_ne_zero (ne_of_gt hh) (ne_of_gt (hd i b))) f hinj
  refine ⟨normalAffineIntersection N p, ?_, ?_⟩
  · simpa using normalAffineIntersection_codimension N hN p
  · intro x
    rw [mem_normalAffineIntersection_iff]
    apply forall_congr'
    intro i
    rw [← key_facet_form_eq_iff_normal_inner_eq k hd (f i) x p]
    have hpi := (sub_eq_zero.mp (hactive i)).symm
    rw [hpi]
    simp only [keyPyramidHalfspaceSlack, sub_eq_zero]
    exact eq_comm

#print axioms pyramidFacetSlopeNormal_linearIndependent
#print axioms active_pyramidFacetSlopeNormal_linearIndependent
#print axioms mem_normalAffineIntersection_iff
#print axioms normalAffineIntersection_codimension
#print axioms key_facet_form_eq_iff_normal_inner_eq
#print axioms active_key_triple_codimension_three

end SparseMonotiles
