module

public import SpectreGeometry.DeformationHomeomorphismData
public import SpectreGeometry.PolygonFanData

@[expose] public section


/-! Exact ear-removal and common-face certificates for the boundary-only
triangulation. These data are not a substitute for real coverage proofs. -/
namespace SpectreGeometry.Deformation

def ears : List TriangleIndices :=
  [(13,0,1),(2,3,4),(1,2,4),(4,5,6),(6,7,8),(4,6,8),
    (1,4,8),(8,9,10),(10,11,12),(10,12,13),(8,10,13)]
def ear (i : Fin 11) : TriangleIndices := ears.getD i.val (0,0,0)
def exactSide (a b c : ExactPoint) : Quad3 :=
  ExactPoint.det (ExactPoint.sub b a) (ExactPoint.sub c a)
def EarCertificate (i : Fin 11) : Prop :=
  let t := ear i
  Quad3.positive (exactSide fanCenter (vertex t.1) (vertex t.2.1)) ∧
  Quad3.positive (exactSide fanCenter (vertex t.2.1) (vertex t.2.2)) ∧
  Quad3.positive (exactSide fanCenter (vertex t.1) (vertex t.2.2)) ∧
  Quad3.positive (exactSide (vertex t.1) (vertex t.2.1) (vertex t.2.2))
instance (i : Fin 11) : Decidable (EarCertificate i) := inferInstanceAs (Decidable (_ ∧ _))

theorem all_ear_certificates : ∀ i : Fin 11, EarCertificate i := by decide

theorem final_center_inside :
    Quad3.positive (exactSide (vertex 1) (vertex 8) fanCenter) ∧
    Quad3.positive (exactSide (vertex 8) (vertex 13) fanCenter) ∧
    Quad3.positive (exactSide (vertex 13) (vertex 1) fanCenter) := by decide

def triangleIndex (i : Fin 12) (v : Fin 3) : Fin 14 :=
  let t := triangle i
  if v.val=0 then t.1 else if v.val=1 then t.2.1 else t.2.2

theorem all_triangle_orientations : ∀ i : Fin 12,
    Quad3.positive (exactSide (vertex (triangleIndex i 0)) (vertex (triangleIndex i 1))
      (vertex (triangleIndex i 2))) := by decide

def CommonFaceSupport (i j : Fin 12) (e : Fin 3) : Prop :=
  ∀ v : Fin 3,
    let d := exactSide (vertex (triangleIndex i e)) (vertex (triangleIndex i (triangleNext e)))
      (vertex (triangleIndex j v))
    Quad3.nonpositive d ∧
      (d=(0,0) → triangleIndex j v=triangleIndex i e ∨
        triangleIndex j v=triangleIndex i (triangleNext e))
instance (i j : Fin 12) (e : Fin 3) : Decidable (CommonFaceSupport i j e) :=
  inferInstanceAs (Decidable (∀ v : Fin 3, _))
def CommonFacePair (i j : Fin 12) : Prop :=
  (∃ e : Fin 3, CommonFaceSupport i j e) ∨ (∃ e : Fin 3, CommonFaceSupport j i e)
instance (i j : Fin 12) : Decidable (CommonFacePair i j) := inferInstanceAs (Decidable (_ ∨ _))

theorem all_common_faces : ∀ i j : Fin 12, i ≠ j → CommonFacePair i j := by decide

end SpectreGeometry.Deformation
