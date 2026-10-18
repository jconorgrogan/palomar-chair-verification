module

public import SpectreGeometry.HalfplaneCertificateReal
public import SpectreGeometry.ConvexQuadrilateral
public import SpectreClusters.BodyBSPData

@[expose] public section


/-! Closed convex polygons in literal integer coordinates, identified with the
exact facet predicates used by the checked subdivision certificates. -/
namespace SpectreGeometry
noncomputable section
open Set HalfplaneCertificate
open SpectreClusters SpectreClusters.BodyBSP

def integerPoint (p : SpectreClusters.Point) : RealPoint := ((p.1 : ℝ),(p.2 : ℝ))
def integerHull (vs : List SpectreClusters.Point) : Set RealPoint :=
  convexHull ℝ (integerPoint '' {p | p ∈ vs})

theorem edgeFacet_eval (a b : SpectreClusters.Point) (x : RealPoint) :
    evalConstraint (edgeFacet a b) x = side (integerPoint a) (integerPoint b) x := by
  simp only [edgeFacet,evalConstraint,side,RealPoint.det,RealPoint.sub,integerPoint,
    Int.cast_sub,Int.cast_neg,Int.cast_mul]
  ring

theorem edgeValue_real (line : Constraint) (p : SpectreClusters.Point) :
    evalConstraint line (integerPoint p) = (edgeValue line p : ℝ) := by
  simp [evalConstraint,integerPoint,edgeValue]

theorem facetBinding_sound (vs : List SpectreClusters.Point) (fs : List Constraint)
    (scales : List Nat) (hc : facetBindingB vs fs scales = true) (x : RealPoint) :
    Satisfies fs x ↔ Satisfies (polygonFacets vs) x := by
  have hc' : fs.length=scales.length ∧ (∀ n ∈ scales, 0<n) ∧
      List.zipWith scaleConstraint scales fs=polygonFacets vs := by
    simpa only [facetBindingB,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
      beq_iff_eq,and_assoc] using hc
  rw [←hc'.2.2]
  have hn := hc'.2.1
  have hl := hc'.1
  clear hc hc'
  induction fs generalizing scales with
  | nil => cases scales <;> simp_all [Satisfies]
  | cons f fs ih =>
    cases scales with
    | nil => simp at hl
    | cons n ns =>
      have hlen : fs.length=ns.length := by simpa using hl
      have hpos : (0:ℝ)<n := by exact_mod_cast hn n (by simp)
      have hind := ih ns (fun m hm => hn m (by simp [hm])) hlen
      simp only [Satisfies,List.mem_cons,forall_eq_or_imp,List.zipWith_cons_cons]
      rw [eval_scale]
      constructor
      · intro h
        exact ⟨mul_nonneg hpos.le h.1,hind.mp h.2⟩
      · intro h
        exact ⟨nonneg_of_mul_nonneg_right h.1 hpos,hind.mpr h.2⟩

theorem integerHull_three (a b c : SpectreClusters.Point) :
    integerHull [a,b,c] = convexHull ℝ {integerPoint a,integerPoint b,integerPoint c} := by
  unfold integerHull
  congr 1
  ext p
  simp only [Set.mem_image,Set.mem_setOf_eq,List.mem_cons,List.not_mem_nil,or_false,
    Set.mem_insert_iff,Set.mem_singleton_iff]
  aesop

theorem integerHull_four (a b c d : SpectreClusters.Point) :
    integerHull [a,b,c,d] = convexHull ℝ {integerPoint a,integerPoint b,integerPoint c,integerPoint d} := by
  unfold integerHull
  congr 1
  ext p
  simp only [Set.mem_image,Set.mem_setOf_eq,List.mem_cons,List.not_mem_nil,or_false,
    Set.mem_insert_iff,Set.mem_singleton_iff]
  aesop

theorem triangle_polygon_facets (a b c : SpectreClusters.Point) (x : RealPoint)
    (hp : polygonPositiveB [a,b,c] = true) :
    x ∈ integerHull [a,b,c] ↔ Satisfies (polygonFacets [a,b,c]) x := by
  have hd : 0 < edgeValue (edgeFacet a b) c := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp 0 (by simp))
  have hd' : 0 < side (integerPoint a) (integerPoint b) (integerPoint c) := by
    rw [←edgeFacet_eval,edgeValue_real]
    exact_mod_cast hd
  rw [integerHull_three,triangle_mem_iff _ _ _ _ hd']
  simp [Satisfies,polygonFacets,cycleEdges,edgeFacet_eval,and_assoc]

theorem quad_polygon_facets (a b c d : SpectreClusters.Point) (x : RealPoint)
    (hp : polygonPositiveB [a,b,c,d] = true) :
    x ∈ integerHull [a,b,c,d] ↔ Satisfies (polygonFacets [a,b,c,d]) x := by
  have h0 : 0 < edgeValue (edgeFacet a b) c := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp 0 (by simp))
  have h1 : 0 < edgeValue (edgeFacet b c) d := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp 1 (by simp))
  have h2 : 0 < edgeValue (edgeFacet c d) a := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp 2 (by simp))
  have h3 : 0 < edgeValue (edgeFacet d a) b := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp 3 (by simp))
  have hd (a b c : SpectreClusters.Point) (h : 0 < edgeValue (edgeFacet a b) c) :
      0 < side (integerPoint a) (integerPoint b) (integerPoint c) := by
    rw [←edgeFacet_eval,edgeValue_real]; exact_mod_cast h
  have habc := hd a b c h0
  have hbcd := hd b c d h1
  have hacd : 0 < side (integerPoint a) (integerPoint c) (integerPoint d) := by
    rw [side_cyclic]; exact hd c d a h2
  have habd : 0 < side (integerPoint a) (integerPoint b) (integerPoint d) := by
    rw [←side_cyclic]; exact hd d a b h3
  rw [integerHull_four,convex_quad_hull_mem_iff _ _ _ _ _ habc hacd habd hbcd]
  simp [Satisfies,polygonFacets,cycleEdges,edgeFacet_eval,and_assoc]

theorem integerHull_facets_three (vs : List SpectreClusters.Point) (x : RealPoint)
    (hl : vs.length = 3) (hp : polygonPositiveB vs = true) :
    x ∈ integerHull vs ↔ Satisfies (polygonFacets vs) x := by
  rcases vs with _ | ⟨a,vs⟩ <;> simp at hl
  rcases vs with _ | ⟨b,vs⟩ <;> simp at hl
  rcases vs with _ | ⟨c,vs⟩ <;> simp at hl
  have hnil : vs=[] := by simpa using hl
  subst vs
  exact triangle_polygon_facets a b c x hp

theorem integerHull_facets_four (vs : List SpectreClusters.Point) (x : RealPoint)
    (hl : vs.length = 4) (hp : polygonPositiveB vs = true) :
    x ∈ integerHull vs ↔ Satisfies (polygonFacets vs) x := by
  rcases vs with _ | ⟨a,vs⟩ <;> simp at hl
  rcases vs with _ | ⟨b,vs⟩ <;> simp at hl
  rcases vs with _ | ⟨c,vs⟩ <;> simp at hl
  rcases vs with _ | ⟨d,vs⟩ <;> simp at hl
  have hnil : vs=[] := by simpa using hl
  subst vs
  exact quad_polygon_facets a b c d x hp

theorem canonicalTriangle_mem_iff (kind : HTKind) (i : Fin 12) (x : RealPoint) :
    x ∈ integerHull ((targetVertexLists kind).getD i.val []) ↔
      Satisfies ((targetFacets kind).getD i.val []) x := by
  rw [facetBinding_sound _ _ _ (target_facets_bound kind i)]
  exact integerHull_facets_three _ x (by cases kind <;> revert i <;> decide)
    (target_triangles_positive kind i)

theorem canonicalKite_mem_iff (kind : HTKind) (i : Fin (htCells kind).length) (x : RealPoint) :
    x ∈ integerHull ((kiteVertexLists kind).getD i.val []) ↔
      Satisfies ((kiteFacets kind).getD i.val []) x := by
  rw [facetBinding_sound _ _ _ (kite_facets_bound kind i)]
  exact integerHull_facets_four _ x (by cases kind <;> revert i <;> decide)
    (kite_convex_positive kind i)

end
end SpectreGeometry
