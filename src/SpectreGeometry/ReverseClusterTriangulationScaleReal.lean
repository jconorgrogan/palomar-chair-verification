module

public import SpectreGeometry.ReverseClusterTriangulationCarrierReal
public import SpectreGeometry.ReverseClusterTriangulationData

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters

def rawClusterBody (kind : ClusterKind) : Set RealPoint :=
  ⋃ c ∈ clusterCells kind, gridKiteBody c

def scalarLinear (a : ℝ) : RealPoint →ₗ[ℝ] RealPoint := a • LinearMap.id

@[simp] theorem scalarLinear_apply (a : ℝ) (x : RealPoint) : scalarLinear a x = a • x := rfl

theorem integerPoint_scale (n : Int) (p : Point) :
    integerPoint (scalePoint n p) = (n : ℝ) • integerPoint p := by
  apply Prod.ext <;> simp [integerPoint,scalePoint,smul_eq_mul]

theorem integerHull_scale (n : Int) (vs : List Point) :
    integerHull (vs.map (scalePoint n)) = (fun x : RealPoint => (n : ℝ) • x) '' integerHull vs := by
  change convexHull ℝ (integerPoint '' {p | p ∈ vs.map (scalePoint n)}) =
    scalarLinear (n : ℝ) '' convexHull ℝ (integerPoint '' {p | p ∈ vs})
  rw [(scalarLinear (n : ℝ)).image_convexHull]
  congr 1
  ext x
  constructor
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact ⟨integerPoint q,⟨q,hq,rfl⟩,(integerPoint_scale n q).symm⟩
  · rintro ⟨p,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨scalePoint n q,List.mem_map.mpr ⟨q,hq,rfl⟩,integerPoint_scale n q⟩

theorem scaledGridKiteBody_eq_image (n : Int) (c : Cell) :
    scaledGridKiteBody n c = (fun x : RealPoint => (n : ℝ) • x) '' gridKiteBody c :=
  integerHull_scale n (cellVertices c)

theorem scaledClusterBody_eq_image (n : Int) (kind : ClusterKind) :
    scaledClusterBody n kind = (fun x : RealPoint => (n : ℝ) • x) '' rawClusterBody kind := by
  simp only [scaledClusterBody,rawClusterBody,Set.image_iUnion,scaledGridKiteBody_eq_image]

theorem normalize_scaledClusterBody (kind : ClusterKind) :
    (fun x : RealPoint => (1/6 : ℝ) • x) '' scaledClusterBody 6 kind = rawClusterBody kind := by
  rw [scaledClusterBody_eq_image,Set.image_image]
  simp only [Int.cast_ofNat,smul_smul,show (1/6 : ℝ)*6=1 by norm_num,one_smul,Set.image_id']

end
end SpectreGeometry.ReverseClusterTriangulation
