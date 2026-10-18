module

public import SpectreGeometry.ReverseLocalStarInclusion
public import SpectreGeometry.ReverseFinitePLMarkedClusterCore

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation ReverseExistence

def placedTriangleVertices (r : Fin 6) (anchor : RealPoint) (scale : ℝ)
    (v : Fin 3 → Plane) : Fin 3 → Plane :=
  fun i => anchor+gridRotation r (scale • v i)

def placedTriangleAffine (r : Fin 6) (anchor : RealPoint) (scale : ℝ) :
    Plane →ᵃ[ℝ] Plane := (gridMotion r anchor).comp (scalarLinear scale).toAffineMap

@[simp] theorem placedTriangleAffine_apply (r : Fin 6) (anchor p : RealPoint) (scale : ℝ) :
    placedTriangleAffine r anchor scale p = anchor+gridRotation r (scale • p) := rfl

theorem triangleDet_placed (r : Fin 6) (anchor : RealPoint) (scale : ℝ)
    (v : Fin 3 → Plane) :
    triangleDet (placedTriangleVertices r anchor scale v) = scale^2 * triangleDet v := by
  fin_cases r <;>
    norm_num [placedTriangleVertices,triangleDet,gridRotation,Prod.fst_add,Prod.snd_add,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

theorem triangleDet_placed_ne_zero (r : Fin 6) (anchor : RealPoint) (scale : ℝ)
    (hs : scale ≠ 0) (v : Fin 3 → Plane) (hv : triangleDet v ≠ 0) :
    triangleDet (placedTriangleVertices r anchor scale v) ≠ 0 := by
  rw [triangleDet_placed]
  exact mul_ne_zero (pow_ne_zero 2 hs) hv

theorem triangleHull_placed (r : Fin 6) (anchor : RealPoint) (scale : ℝ)
    (v : Fin 3 → Plane) :
    triangleHull (placedTriangleVertices r anchor scale v) =
      placedTriangleAffine r anchor scale '' triangleHull v := by
  unfold triangleHull
  rw [AffineMap.image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨v i,⟨i,rfl⟩,rfl⟩
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

/-- Each placed normalized target triangle lies in the literal placed cluster. -/
theorem placed_target_triangle_subset_carrier (k : Fin 9) (r : Fin 6) (anchor : RealPoint)
    (i : Fin (meshTriangles k).length) :
    triangleHull (placedTriangleVertices r anchor (1/6)
      (codeTriangle (targetVertices k) ((meshTriangles k).get i))) ⊆
        placedClusterCarrier r anchor (SpectreClusters.ReverseExistence.clusterOfMark k) := by
  rw [triangleHull_placed,codeTriangle_hull]
  rintro x ⟨y,hy,rfl⟩
  have hget : (meshTriangles k).getD i.val (0,0,0) = (meshTriangles k).get i := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,
      Option.getD_some,List.get_eq_getElem]
  have hy' : y ∈ familyBody (targetFamily k) := by
    apply ReverseLocalStarOccurrences.target_triangle_hull_subset_family k i.val i.isLt
    rwa [hget]
  have hnorm : (1/6:ℝ) • y ∈ rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) := by
    rw [←all_normalized_target_carriers_exact k]
    exact ⟨y,hy',rfl⟩
  exact ⟨(1/6:ℝ) • y,hnorm,rfl⟩

end
end SpectreGeometry.ReverseFinitePL
