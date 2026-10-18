module

public import SpectreGeometry.ReverseFinitePLGluing
public import SpectreGeometry.ReverseFinitePLTriangle

@[expose] public section


/-! A finite indexed pair of conforming, nondegenerate triangular meshes has
an explicit PL homeomorphism. The common-face conditions occur on both sides;
no injectivity of the assembled piecewise map is postulated. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set

structure TriangleMeshPair (V ι : Type*) where
  index : ι → Fin 3 → V
  sourceVertex : V → Plane
  targetVertex : V → Plane
  source_injective : Function.Injective sourceVertex
  target_injective : Function.Injective targetVertex
  source_nondegenerate : ∀ i, triangleDet (sourceVertex ∘ index i) ≠ 0
  target_nondegenerate : ∀ i, triangleDet (targetVertex ∘ index i) ≠ 0
  source_faces : ∀ i j,
    triangleHull (sourceVertex ∘ index i) ∩ triangleHull (sourceVertex ∘ index j) =
      convexHull ℝ (range (sourceVertex ∘ index i) ∩ range (sourceVertex ∘ index j))
  target_faces : ∀ i j,
    triangleHull (targetVertex ∘ index i) ∩ triangleHull (targetVertex ∘ index j) =
      convexHull ℝ (range (targetVertex ∘ index i) ∩ range (targetVertex ∘ index j))

namespace TriangleMeshPair
variable {V ι : Type*} (D : TriangleMeshPair V ι)

def affineChart (i : ι) : Plane ≃ᵃ[ℝ] Plane :=
  triangleEquiv (D.sourceVertex ∘ D.index i) (D.targetVertex ∘ D.index i)
    (D.source_nondegenerate i) (D.target_nondegenerate i)

@[simp] theorem affineChart_vertex (i : ι) (v : Fin 3) :
    D.affineChart i (D.sourceVertex (D.index i v)) = D.targetVertex (D.index i v) :=
  triangleEquiv_vertex _ _ _ _ v

@[simp] theorem affineChart_symm_vertex (i : ι) (v : Fin 3) :
    (D.affineChart i).symm (D.targetVertex (D.index i v)) = D.sourceVertex (D.index i v) :=
  triangleEquiv_symm_vertex _ _ _ _ v

theorem affineChart_agree (i j : ι) (x : Plane)
    (hi : x ∈ triangleHull (D.sourceVertex ∘ D.index i))
    (hj : x ∈ triangleHull (D.sourceVertex ∘ D.index j)) :
    D.affineChart i x = D.affineChart j x := by
  have hface : x ∈ convexHull ℝ (range (D.sourceVertex ∘ D.index i) ∩
      range (D.sourceVertex ∘ D.index j)) := by
    rw [←D.source_faces]
    exact ⟨hi,hj⟩
  have hv : EqOn (D.affineChart i).toAffineMap (D.affineChart j).toAffineMap
      (range (D.sourceVertex ∘ D.index i) ∩ range (D.sourceVertex ∘ D.index j)) := by
    rintro y ⟨⟨v,hv⟩,⟨w,hw⟩⟩
    have he : D.index i v = D.index j w := D.source_injective (hv.trans hw.symm)
    change D.affineChart i y = D.affineChart j y
    calc
      D.affineChart i y = D.targetVertex (D.index i v) := by rw [←hv]; exact D.affineChart_vertex i v
      _ = D.targetVertex (D.index j w) := congrArg D.targetVertex he
      _ = D.affineChart j y := by rw [←hw]; exact (D.affineChart_vertex j w).symm
  exact AffineMap.eqOn_affineSpan hv (convexHull_subset_affineSpan _ hface)

theorem affineChart_symm_agree (i j : ι) (y : Plane)
    (hi : y ∈ triangleHull (D.targetVertex ∘ D.index i))
    (hj : y ∈ triangleHull (D.targetVertex ∘ D.index j)) :
    (D.affineChart i).symm y = (D.affineChart j).symm y := by
  have hface : y ∈ convexHull ℝ (range (D.targetVertex ∘ D.index i) ∩
      range (D.targetVertex ∘ D.index j)) := by
    rw [←D.target_faces]
    exact ⟨hi,hj⟩
  have hv : EqOn (D.affineChart i).symm.toAffineMap (D.affineChart j).symm.toAffineMap
      (range (D.targetVertex ∘ D.index i) ∩ range (D.targetVertex ∘ D.index j)) := by
    rintro x ⟨⟨v,hv⟩,⟨w,hw⟩⟩
    have he : D.index i v = D.index j w := D.target_injective (hv.trans hw.symm)
    change (D.affineChart i).symm x = (D.affineChart j).symm x
    calc
      (D.affineChart i).symm x = D.sourceVertex (D.index i v) := by
        rw [←hv]; exact D.affineChart_symm_vertex i v
      _ = D.sourceVertex (D.index j w) := congrArg D.sourceVertex he
      _ = (D.affineChart j).symm x := by rw [←hw]; exact (D.affineChart_symm_vertex j w).symm
  exact AffineMap.eqOn_affineSpan hv (convexHull_subset_affineSpan _ hface)

def closedCharts : ClosedChartFamily Plane Plane ι where
  source i := triangleHull (D.sourceVertex ∘ D.index i)
  target i := triangleHull (D.targetVertex ∘ D.index i)
  chart i := (D.affineChart i).toHomeomorphOfFiniteDimensional
  source_closed i := triangleHull_closed _
  target_closed i := triangleHull_closed _
  image_source i := triangleEquiv_image_hull _ _ _ _
  forward_agree := D.affineChart_agree
  inverse_agree := D.affineChart_symm_agree

/-- Homeomorphism between the complete finite triangular carriers. -/
def homeomorph [Finite ι] : D.closedCharts.sourceCarrier ≃ₜ D.closedCharts.targetCarrier :=
  D.closedCharts.homeomorph

@[simp] theorem homeomorph_on [Finite ι] (i : ι) (x : D.closedCharts.sourceCarrier)
    (hx : x.val ∈ triangleHull (D.sourceVertex ∘ D.index i)) :
    (D.homeomorph x).val = D.affineChart i x.val := D.closedCharts.homeomorph_on i x hx

/-- The PL map has the prescribed linear parametrization on every mesh edge. -/
theorem homeomorph_lineMap [Finite ι] (i : ι) (v w : Fin 3) (t : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (x : D.closedCharts.sourceCarrier)
    (hx : x.val = AffineMap.lineMap (D.sourceVertex (D.index i v))
      (D.sourceVertex (D.index i w)) t) :
    (D.homeomorph x).val = AffineMap.lineMap (D.targetVertex (D.index i v))
      (D.targetVertex (D.index i w)) t := by
  have hv : D.sourceVertex (D.index i v) ∈ triangleHull (D.sourceVertex ∘ D.index i) :=
    subset_convexHull ℝ _ ⟨v,rfl⟩
  have hw : D.sourceVertex (D.index i w) ∈ triangleHull (D.sourceVertex ∘ D.index i) :=
    subset_convexHull ℝ _ ⟨w,rfl⟩
  have hm : x.val ∈ triangleHull (D.sourceVertex ∘ D.index i) := by
    rw [hx]
    exact (convex_convexHull ℝ _).lineMap_mem hv hw ht
  rw [D.homeomorph_on i x hm,hx,AffineEquiv.apply_lineMap,
    D.affineChart_vertex,D.affineChart_vertex]

end TriangleMeshPair
end
end SpectreGeometry.ReverseFinitePL
