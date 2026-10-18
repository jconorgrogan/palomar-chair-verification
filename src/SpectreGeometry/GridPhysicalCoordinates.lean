module

public import SpectreGeometry.DevelopedLiteralBody
public import SpectreGeometry.DevelopedCenterLattice

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.DeformedLiteralBinding

def gridEmbeddingHomeomorph : RealPoint ≃ₜ RealPoint where
  toFun := gridEmbeddingLinear
  invFun x := (2*x.1/Real.sqrt 3,x.2-x.1/Real.sqrt 3)
  left_inv x := by
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    ext <;> simp [gridEmbeddingLinear] <;> field_simp <;> ring
  right_inv x := by
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
    ext <;> simp [gridEmbeddingLinear] <;> field_simp <;> ring
  continuous_toFun := by change Continuous (fun x : RealPoint => (Real.sqrt 3*x.1/2,x.1/2+x.2)); fun_prop
  continuous_invFun := by fun_prop

def gridReflectionHomeomorph : RealPoint ≃ₜ RealPoint where
  toFun := gridReflectionLinear
  invFun := gridReflectionLinear
  left_inv x := by ext <;> simp [gridReflectionLinear]
  right_inv x := by ext <;> simp [gridReflectionLinear]
  continuous_toFun := by change Continuous (fun x : RealPoint => (x.1,-x.1-x.2)); fun_prop
  continuous_invFun := by change Continuous (fun x : RealPoint => (x.1,-x.1-x.2)); fun_prop

def gridPhysicalHomeomorph (a : RealPoint) : RealPoint ≃ₜ EPlane :=
  gridReflectionHomeomorph.trans (gridEmbeddingHomeomorph.trans
    ((Homeomorph.addLeft a).trans euclideanCoordinates))

@[simp] theorem gridPhysicalHomeomorph_apply (a p : RealPoint) :
    gridPhysicalHomeomorph a p = euclideanCoordinates (a+gridEmbeddingLinear (gridReflectionLinear p)) := rfl

theorem gridReflection_reflectCenter (p : SpectreClusters.Point) :
    gridReflectionLinear (integerPoint (lattice (reflectCenter p))) = integerPoint (lattice p) := by
  rw [gridReflection_integerPoint,←reflectPoint_lattice]
  rw [reflectPoint_involutive]

theorem gridEmbedding_rational_add (p q : ℚ × ℚ) :
    kiteCoordinateEmbedding (p+q) = kiteCoordinateEmbedding p+kiteCoordinateEmbedding q :=
  kiteCoordinateEmbedding_add p q

theorem gridEmbedding_centerMap (p : SpectreClusters.Point) :
    kiteCoordinateEmbedding (kiteCenterMap p) = gridEmbeddingLinear (integerPoint (lattice p)) := by
  rw [gridEmbedding_integerPoint]
  congr 1
  ext <;> simp [kiteCenterMap,rationalKitePoint,lattice]

end
end SpectreGeometry
