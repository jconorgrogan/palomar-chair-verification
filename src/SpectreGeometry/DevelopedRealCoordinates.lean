module

public import SpectreGeometry.QuadraticDevelopment

@[expose] public section


/-! The physical real-plane realization of the globally consistent developed
vertex values. This does not extend the development continuously between
vertices or assert a new tiling. -/
namespace SpectreGeometry
noncomputable section

def kiteCoordinateEmbedding (p : ℚ × ℚ) : RealPoint :=
  (Real.sqrt 3*(p.1 : ℝ)/2,(p.1 : ℝ)/2+(p.2 : ℝ))

def realDeformedVertex (k : Fin 12) (e : Fin 14) : RealPoint :=
  kiteCoordinateEmbedding (rationalKitePoint (deformedVertex k e))

theorem kiteCoordinateEmbedding_add (p q : ℚ × ℚ) :
    kiteCoordinateEmbedding (p+q) = kiteCoordinateEmbedding p+kiteCoordinateEmbedding q := by
  apply Prod.ext <;> simp only [kiteCoordinateEmbedding,Prod.fst_add,Prod.snd_add,Rat.cast_add] <;> ring

theorem kiteCoordinateEmbedding_sub (p q : ℚ × ℚ) :
    kiteCoordinateEmbedding (p-q) = kiteCoordinateEmbedding p-kiteCoordinateEmbedding q := by
  apply Prod.ext <;> simp only [kiteCoordinateEmbedding,Prod.fst_sub,Prod.snd_sub,Rat.cast_sub] <;> ring

/-- An arbitrary total extension, used only at proved registered vertices. -/
def physicalVertexDevelopment (root : EPlane ≃ᵢ EPlane) (x : EPlane) : RealPoint := by
  classical
  exact if h : sourcePoint root x ∈ quadraticPlane then
    kiteCoordinateEmbedding (quadraticDevelopment ⟨sourcePoint root x,h⟩) else 0

theorem physicalVertexDevelopment_registered (root : EPlane ≃ᵢ EPlane) (x : EPlane)
    (h : sourcePoint root x ∈ quadraticPlane) :
    physicalVertexDevelopment root x = kiteCoordinateEmbedding (quadraticDevelopment ⟨sourcePoint root x,h⟩) := by
  simp only [physicalVertexDevelopment,dite_eq_left h]

theorem physicalVertexDevelopment_formula (root f : EPlane ≃ᵢ EPlane) (k : Fin 12)
    (hframe : ∀ q : RealPoint, coordinateAction f q = coordinateAction root (rotate k q))
    (horigin : sourcePoint root (f 0) ∈ quadraticPlane) (e : Fin 14) :
    physicalVertexDevelopment root (f (euclideanVertex e)) =
      kiteCoordinateEmbedding (quadraticDevelopment ⟨sourcePoint root (f 0),horigin⟩)+
        realDeformedVertex k e := by
  rw [physicalVertexDevelopment_registered root _
    (relative_vertex_mem_quadraticPlane root f k hframe horigin e),
    physical_vertex_development_formula root f k hframe horigin e,kiteCoordinateEmbedding_add]
  rfl

/-- The total extension is used here only where registration has been derived
from an actual physical tiling. -/
theorem homochiral_vertex_development_formula {ι : Type*}
    (f : ι → EPlane ≃ᵢ EPlane) (hdirect : ∀ i, DirectPlacement (f i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (f i '' euclideanBody)) (interior (f j '' euclideanBody)))
    (hcover : ∀ x, ∃ i, x ∈ f i '' euclideanBody) (root i : ι)
    (k : Fin 12)
    (hk : ∀ q : RealPoint, coordinateAction (f i) q = coordinateAction (f root) (rotate k q))
    (e : Fin 14) :
    physicalVertexDevelopment (f root) (f i (euclideanVertex e)) =
      kiteCoordinateEmbedding (quadraticDevelopment ⟨sourcePoint (f root) (f i 0),
        homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i⟩)+
        realDeformedVertex k e :=
  physicalVertexDevelopment_formula (f root) (f i) k hk
    (homochiral_origin_mem_quadraticPlane f hdirect hdisjoint hcover root i) e

end
end SpectreGeometry
