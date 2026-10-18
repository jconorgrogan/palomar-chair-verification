module

public import SpectreGeometry.LiteralKiteBody
public import SpectreGeometry.GridAffineGeometry
public import SpectreGeometry.DeformationHomeomorphismTile

@[expose] public section


/-! Binding the actual physical twelve-triangle image to the literal raw H/T
closed-kite carriers. All twelve orientations use one common reflection. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP SpectreClusters.DeformedLiteralBinding
open SpectreGeometry.Deformation

def gridEmbeddingLinear : RealPoint →ₗ[ℝ] RealPoint where
  toFun p := (Real.sqrt 3*p.1/2,p.1/2+p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

def gridReflectionLinear : RealPoint →ₗ[ℝ] RealPoint where
  toFun p := (p.1,-p.1-p.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring

theorem gridReflection_integerPoint (p : SpectreClusters.Point) :
    gridReflectionLinear (integerPoint p) = integerPoint (reflectPoint p) := by
  ext <;> simp [gridReflectionLinear,integerPoint,reflectPoint]

theorem gridEmbedding_integerPoint (p : SpectreClusters.Point) :
    gridEmbeddingLinear (integerPoint p) = kiteCoordinateEmbedding (rationalKitePoint p) := by
  ext <;> simp [gridEmbeddingLinear,integerPoint,kiteCoordinateEmbedding,rationalKitePoint]

def literalTargetAffine (k : Fin 12) : RealPoint →ᵃ[ℝ] RealPoint :=
  gridEmbeddingLinear.toAffineMap.comp (gridReflectionLinear.toAffineMap.comp
    (gridMotion (literalTurn k) (integerPoint (reflectPoint (deformedOffset k)))))

theorem canonicalVertex_eq (k : Fin 12) (e : Fin 14) :
    canonicalVertex (literalKind k) e = literalVertex (literalKind k) (literalIndex k e) := by
  revert k e
  decide

theorem literalTargetAffine_vertex (k : Fin 12) (e : Fin 14) :
    literalTargetAffine k (integerPoint (canonicalVertex (literalKind k) e)) = realDeformedVertex k e := by
  have hd := congrArg reflectPoint (developed_vertex_literal k e)
  rw [reflectPoint_involutive] at hd
  rw [canonicalVertex_eq]
  change gridEmbeddingLinear (gridReflectionLinear
    (integerPoint (reflectPoint (deformedOffset k))+
      gridRotation (literalTurn k) (integerPoint (literalVertex (literalKind k) (literalIndex k e))))) = _
  rw [←integerPoint_rotate,←integerPoint_add,gridReflection_integerPoint]
  change gridEmbeddingLinear (integerPoint (reflectPoint (literalPlacedVertex k (literalIndex k e)))) = _
  rw [←hd,gridEmbedding_integerPoint]
  rfl

theorem targetVertexLists_get (kind : HTKind) (i : Fin 12) :
    (targetVertexLists kind).getD i.val [] = canonicalTriangle kind i := by
  cases kind <;> revert i <;> decide

theorem canonicalTriangle_hull (kind : HTKind) (i : Fin 12) :
    integerHull ((targetVertexLists kind).getD i.val []) =
      convexHull ℝ (range (fun v : Fin 3 => integerPoint (canonicalVertex kind (triangleIndex i v)))) := by
  rw [targetVertexLists_get,canonicalTriangle,integerHull_three]
  congr 1
  ext p
  simp only [mem_insert_iff,mem_singleton_iff,mem_range]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨1,rfl⟩
  · rintro ⟨v,rfl⟩
    fin_cases v <;> simp

theorem literalTargetAffine_image_triangle (k i : Fin 12) :
    literalTargetAffine k '' integerHull ((targetVertexLists (literalKind k)).getD i.val []) =
      targetTriangle k i := by
  rw [canonicalTriangle_hull,(literalTargetAffine k).image_convexHull,targetTriangle]
  congr 1
  ext p
  constructor
  · rintro ⟨q,⟨v,rfl⟩,rfl⟩
    exact ⟨v,(literalTargetAffine_vertex k (triangleIndex i v)).symm⟩
  · rintro ⟨v,rfl⟩
    exact ⟨_,⟨v,rfl⟩,literalTargetAffine_vertex k (triangleIndex i v)⟩

/-- The developed physical carrier is literally a transformed union of the
source's eight or ten closed kites, not merely a polygon with equal boundary. -/
theorem targetBody_eq_literalKiteBody (k : Fin 12) :
    targetBody k = literalTargetAffine k '' literalKiteBody (literalKind k) := by
  rw [←canonicalTargetBody_eq_literalKiteBody,canonicalTargetBody,Set.image_iUnion]
  exact congrArg (fun s : Fin 12 → Set RealPoint => ⋃ i, s i)
    (funext fun i => (literalTargetAffine_image_triangle k i).symm)

end
end SpectreGeometry
