module

public import SpectreGeometry.DeformationHomeomorphismAffine
public import SpectreGeometry.DeformationTriangulationCover
public import SpectreGeometry.DeformationTriangulationFaces
public import SpectreGeometry.DeformationBoundaryOwnershipData

@[expose] public section


/-! The actual piecewise-affine map on a source tile. Common-face equality,
coverage, vertex values, and full carrier images are proved explicitly. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

def rotationLinearMap (k : Fin 12) : RealPoint →ₗ[ℝ] RealPoint where
  toFun := rotate k
  map_add' x y := by
    apply Prod.ext <;> simp only [rotate,complexMulReal,Prod.fst_add,Prod.snd_add] <;> ring
  map_smul' c x := by
    apply Prod.ext <;> simp only [rotate,complexMulReal,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      RingHom.id_apply] <;> ring

def sourceAffine (k i : Fin 12) : RealPoint →ᵃ[ℝ] RealPoint :=
  (triangleAffine k i).comp (rotationLinearMap k).toAffineMap

@[simp] theorem sourceAffine_apply (k i : Fin 12) (p : RealPoint) :
    sourceAffine k i p = triangleAffine k i (rotate k p) := rfl

theorem sourceAffine_vertex (k i : Fin 12) (v : Fin 3) :
    sourceAffine k i (realVertex (triangleIndex i v)) = realDeformedVertex k (triangleIndex i v) := by
  fin_cases v
  · exact triangleAffine_first k i
  · exact triangleAffine_other k i false
  · exact triangleAffine_other k i true

theorem sourceAffine_agree (k i j : Fin 12) (p : RealPoint)
    (hi : p ∈ sourceTriangle i) (hj : p ∈ sourceTriangle j) :
    sourceAffine k i p = sourceAffine k j p := by
  have hface : p ∈ convexHull ℝ (sourceVertices i ∩ sourceVertices j) := by
    rw [←sourceTriangles_common_face]
    exact ⟨hi,hj⟩
  have hvertices : Set.EqOn (sourceAffine k i) (sourceAffine k j) (sourceVertices i ∩ sourceVertices j) := by
    rintro q ⟨⟨v,hv⟩,⟨w,hw⟩⟩
    have he := real_vertices_distinct _ _ (hv.trans hw.symm)
    calc
      sourceAffine k i q = realDeformedVertex k (triangleIndex i v) := by
        rw [←hv,sourceAffine_vertex]
      _ = realDeformedVertex k (triangleIndex j w) := congrArg (realDeformedVertex k) he
      _ = sourceAffine k j q := by rw [←hw,sourceAffine_vertex]
  exact AffineMap.eqOn_affineSpan hvertices (convexHull_subset_affineSpan _ hface)

def selectedTriangle (p : RealPoint) : Fin 12 := by
  classical
  exact if h : ∃ i, p ∈ sourceTriangle i then Classical.choose h else 0

theorem selectedTriangle_mem (p : RealPoint) (h : ∃ i, p ∈ sourceTriangle i) :
    p ∈ sourceTriangle (selectedTriangle p) := by
  simp only [selectedTriangle,dif_pos h]
  exact Classical.choose_spec h

def tilePLMap (k : Fin 12) (p : RealPoint) : RealPoint := sourceAffine k (selectedTriangle p) p

theorem tilePLMap_on_triangle (k i : Fin 12) (p : RealPoint) (hi : p ∈ sourceTriangle i) :
    tilePLMap k p = sourceAffine k i p :=
  sourceAffine_agree k (selectedTriangle p) i p (selectedTriangle_mem p ⟨i,hi⟩) hi

theorem sourceTriangle_vertex_mem (i : Fin 12) (v : Fin 3) :
    realVertex (triangleIndex i v) ∈ sourceTriangle i := by
  rw [sourceTriangle_eq_hull]
  exact subset_convexHull ℝ _ ⟨v,rfl⟩

theorem interpolate_eq_lineMap (a b : RealPoint) (t : ℝ) :
    interpolate a b t = AffineMap.lineMap a b t := by
  apply Prod.ext <;> simp only [interpolate,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem affine_interpolate (f : RealPoint →ᵃ[ℝ] RealPoint) (a b : RealPoint) (t : ℝ) :
    f (interpolate a b t) = interpolate (f a) (f b) t := by
  rw [interpolate_eq_lineMap,interpolate_eq_lineMap,f.apply_lineMap]

theorem tilePLMap_boundary (k : Fin 12) (e : Fin 14) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    tilePLMap k (interpolate (realVertex e) (realVertex (next e)) t) =
      interpolate (realDeformedVertex k e) (realDeformedVertex k (next e)) t := by
  obtain ⟨i,v,hv,hw⟩ := boundary_edge_owners e
  have he : realVertex e ∈ sourceTriangle i := hv ▸ sourceTriangle_vertex_mem i v
  have hn : realVertex (next e) ∈ sourceTriangle i := hw ▸ sourceTriangle_vertex_mem i (triangleNext v)
  have hx : interpolate (realVertex e) (realVertex (next e)) t ∈ sourceTriangle i := by
    rw [interpolate_eq_lineMap]
    exact (convex_convexHull ℝ _).lineMap_mem he hn ⟨ht,ht'⟩
  rw [tilePLMap_on_triangle k i _ hx,affine_interpolate,←hw,←hv,sourceAffine_vertex,sourceAffine_vertex]

theorem tilePLMap_vertex (k : Fin 12) (e : Fin 14) :
    tilePLMap k (realVertex e) = realDeformedVertex k e := by
  simpa using tilePLMap_boundary k e 0 (by norm_num) (by norm_num)

def targetTriangle (k i : Fin 12) : Set RealPoint :=
  convexHull ℝ (Set.range (fun v : Fin 3 => realDeformedVertex k (triangleIndex i v)))

def targetBody (k : Fin 12) : Set RealPoint := ⋃ i : Fin 12, targetTriangle k i

theorem tilePLMap_image_triangle (k i : Fin 12) :
    tilePLMap k '' sourceTriangle i = targetTriangle k i := by
  rw [Set.image_congr (fun p hp => tilePLMap_on_triangle k i p hp),sourceTriangle_eq_hull,
    (sourceAffine k i).image_convexHull]
  congr 1
  ext q
  constructor
  · rintro ⟨p,⟨v,rfl⟩,rfl⟩
    exact ⟨v,(sourceAffine_vertex k i v).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨realVertex (triangleIndex i v),⟨v,rfl⟩,sourceAffine_vertex k i v⟩

theorem tilePLMap_image_body (k : Fin 12) : tilePLMap k '' polygonBody = targetBody k := by
  rw [sourceTriangles_cover_polygonBody,Set.image_iUnion]
  exact congrArg (fun s : Fin 12 → Set RealPoint => ⋃ i, s i)
    (funext fun i => tilePLMap_image_triangle k i)

end
end SpectreGeometry.Deformation
