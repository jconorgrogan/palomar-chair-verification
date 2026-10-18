module

public import SpectreGeometry.RealPolygonFacets
public import SpectreClusters.GridMotions

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set
open SpectreClusters

theorem integerPoint_add (a b : SpectreClusters.Point) :
    integerPoint (SpectreClusters.add a b) = integerPoint a+integerPoint b := by
  ext <;> simp [integerPoint,SpectreClusters.add]

def gridRotation (k : Turn) (p : RealPoint) : RealPoint :=
  match k.val with
  | 0 => p
  | 1 => (-p.2,p.1+p.2)
  | 2 => (-p.1-p.2,p.1)
  | 3 => (-p.1,-p.2)
  | 4 => (p.2,-p.1-p.2)
  | _ => (p.1+p.2,-p.1)

def gridRotationLinear (k : Turn) : RealPoint →ₗ[ℝ] RealPoint where
  toFun := gridRotation k
  map_add' p q := by fin_cases k <;> ext <;> simp [gridRotation] <;> ring
  map_smul' c p := by fin_cases k <;> ext <;> simp [gridRotation] <;> ring

theorem integerPoint_rotate (k : Turn) (p : SpectreClusters.Point) :
    integerPoint (SpectreClusters.rotate k p) = gridRotation k (integerPoint p) := by
  fin_cases k <;> ext <;> simp [integerPoint,SpectreClusters.rotate,gridRotation]

def gridMotion (k : Turn) (t : RealPoint) : RealPoint →ᵃ[ℝ] RealPoint :=
  (AffineEquiv.constVAdd ℝ RealPoint t).toAffineMap.comp (gridRotationLinear k).toAffineMap

@[simp] theorem gridMotion_apply (k : Turn) (t p : RealPoint) :
    gridMotion k t p = t+gridRotation k p := by rfl

theorem cellVertices_moved (k : Turn) (t : SpectreClusters.Point) (c : Cell) :
    cellVertices (moveCell k t c) =
      (cellVertices c).map (fun p => SpectreClusters.add (lattice t) (SpectreClusters.rotate k p)) := by
  simp only [cellVertices,localVertices,moveCell,translateCell,rotateCell,List.map_map]
  apply List.map_congr_left
  intro p hp
  simp only [Function.comp_apply,lattice_add,lattice_rotate,SpectreClusters.rotate_add,
    rotate_compose,SpectreClusters.add_assoc]

theorem integerHull_image_motion (k : Turn) (t : SpectreClusters.Point)
    (vs : List SpectreClusters.Point) :
    integerHull (vs.map (fun p => SpectreClusters.add (lattice t) (SpectreClusters.rotate k p))) =
      gridMotion k (integerPoint (lattice t)) '' integerHull vs := by
  rw [integerHull,integerHull,(gridMotion k (integerPoint (lattice t))).image_convexHull]
  congr 1
  ext p
  simp only [Set.mem_image,Set.mem_setOf_eq,List.mem_map]
  constructor
  · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨integerPoint v,⟨v,hv,rfl⟩,by simp [integerPoint_add,integerPoint_rotate]⟩
  · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
    exact ⟨_,⟨v,hv,rfl⟩,by simp [integerPoint_add,integerPoint_rotate]⟩

end
end SpectreGeometry
