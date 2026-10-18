module

public import SpectreGeometry.ReverseFinitePLMesh
public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal
public import Mathlib.Data.List.Nodup

@[expose] public section


/-! Adapter from finite integer vertex and triangle tables to the genuine
PL carrier homeomorphism. Its hypotheses are the exact local checks emitted
by the common-mesh certificate modules. -/
namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP
open ReverseClusterTriangulation

def codeIndex (t : TriangleCode) : Fin 3 → Nat := ![t.1,t.2.1,t.2.2]

theorem codeIndex_mem (t : TriangleCode) (i : Fin 3) : codeIndex t i ∈ triangleIndices t := by
  fin_cases i <;> simp [codeIndex,triangleIndices]

theorem mem_triangleIndices (t : TriangleCode) (n : Nat) :
    n ∈ triangleIndices t ↔ ∃ i : Fin 3, codeIndex t i = n := by
  simp only [triangleIndices,List.mem_cons,List.not_mem_nil,or_false,
    Fin.exists_fin_succ,Fin.exists_fin_zero,or_false]
  simp only [codeIndex,Matrix.cons_val_zero,Matrix.cons_val_succ]
  tauto

def codeTriangle (vs : List Point) (t : TriangleCode) : Fin 3 → Plane :=
  fun i => integerPoint (vs.getD (codeIndex t i) (0,0))

theorem codeTriangle_range (vs : List Point) (t : TriangleCode) :
    range (codeTriangle vs t) = integerVertexSet (triangleVertexList vs t) := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,List.mem_map.mpr ⟨codeIndex t i,codeIndex_mem t i,rfl⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hp
    obtain ⟨i,rfl⟩ := (mem_triangleIndices t n).mp hn
    exact ⟨i,rfl⟩

theorem codeTriangle_hull (vs : List Point) (t : TriangleCode) :
    triangleHull (codeTriangle vs t) = integerHull (triangleVertexList vs t) := by
  unfold triangleHull
  rw [codeTriangle_range]
  rfl

theorem codeTriangle_nondegenerate (vs : List Point) (t : TriangleCode)
    (hp : polygonPositiveB (triangleVertexList vs t) = true) :
    triangleDet (codeTriangle vs t) ≠ 0 := by
  let a := vs.getD t.1 (0,0)
  let b := vs.getD t.2.1 (0,0)
  let c := vs.getD t.2.2 (0,0)
  have hp' : polygonPositiveB [a,b,c] = true := hp
  have hd : 0 < edgeValue (edgeFacet a b) c := by
    simpa [polygonPositiveB] using (List.all_eq_true.mp hp' 0 (by simp))
  have he : triangleDet (codeTriangle vs t) = (edgeValue (edgeFacet a b) c : ℝ) := by
    simp only [triangleDet,codeTriangle,codeIndex,Matrix.cons_val_zero,Matrix.cons_val_succ,
      integerPoint,edgeValue,edgeFacet,Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_neg]
    dsimp [a,b,c]
    ring
  rw [he]
  exact ne_of_gt (by exact_mod_cast hd)

theorem integerPoint_injective : Function.Injective integerPoint := by
  intro a b h
  apply Prod.ext
  · have hh : (a.1 : ℝ) = (b.1 : ℝ) := congrArg Prod.fst h
    exact_mod_cast hh
  · have hh : (a.2 : ℝ) = (b.2 : ℝ) := congrArg Prod.snd h
    exact_mod_cast hh

theorem integerListVertex_injective (vs : List Point) (hn : vs.Nodup) :
    Function.Injective (fun i : Fin vs.length => integerPoint (vs.getD i.val (0,0))) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  apply hn.injective_get
  have he := integerPoint_injective h
  simpa [List.getD_eq_getElem?_getD,hi,hj] using he

structure IntegerMeshPair where
  source : List Point
  target : List Point
  triangles : List TriangleCode
  length_eq : source.length = target.length
  source_distinct : source.Nodup
  target_distinct : target.Nodup
  index_bound : ∀ t ∈ triangles, ∀ n ∈ triangleIndices t, n < source.length
  source_positive : ∀ t ∈ triangles, polygonPositiveB (triangleVertexList source t) = true
  target_positive : ∀ t ∈ triangles, polygonPositiveB (triangleVertexList target t) = true
  source_faces : ∀ i j : Fin triangles.length,
    integerHull (triangleVertexList source (triangles.get i)) ∩
        integerHull (triangleVertexList source (triangles.get j)) =
      convexHull ℝ (integerVertexSet (triangleVertexList source (triangles.get i)) ∩
        integerVertexSet (triangleVertexList source (triangles.get j)))
  target_faces : ∀ i j : Fin triangles.length,
    integerHull (triangleVertexList target (triangles.get i)) ∩
        integerHull (triangleVertexList target (triangles.get j)) =
      convexHull ℝ (integerVertexSet (triangleVertexList target (triangles.get i)) ∩
        integerVertexSet (triangleVertexList target (triangles.get j)))

namespace IntegerMeshPair
variable (D : IntegerMeshPair)

def meshIndex (i : Fin D.triangles.length) (v : Fin 3) : Fin D.source.length :=
  ⟨codeIndex (D.triangles.get i) v,
    D.index_bound _ (List.get_mem D.triangles i) _ (codeIndex_mem _ v)⟩

def sourceVertex (i : Fin D.source.length) : Plane := integerPoint (D.source.getD i.val (0,0))
def targetVertex (i : Fin D.source.length) : Plane := integerPoint (D.target.getD i.val (0,0))

theorem source_injective : Function.Injective D.sourceVertex :=
  integerListVertex_injective D.source D.source_distinct

theorem target_injective : Function.Injective D.targetVertex := by
  intro i j h
  have hi : i.val < D.target.length := D.length_eq ▸ i.isLt
  have hj : j.val < D.target.length := D.length_eq ▸ j.isLt
  have he := integerListVertex_injective D.target D.target_distinct
    (a₁ := ⟨i.val,hi⟩) (a₂ := ⟨j.val,hj⟩) h
  exact Fin.ext (congrArg (fun z : Fin D.target.length => z.val) he)

def meshPair : TriangleMeshPair (Fin D.source.length) (Fin D.triangles.length) where
  index := D.meshIndex
  sourceVertex := D.sourceVertex
  targetVertex := D.targetVertex
  source_injective := D.source_injective
  target_injective := D.target_injective
  source_nondegenerate i := codeTriangle_nondegenerate D.source _
    (D.source_positive _ (List.get_mem D.triangles i))
  target_nondegenerate i := codeTriangle_nondegenerate D.target _
    (D.target_positive _ (List.get_mem D.triangles i))
  source_faces i j := by
    change triangleHull (codeTriangle D.source (D.triangles.get i)) ∩
      triangleHull (codeTriangle D.source (D.triangles.get j)) = _
    rw [codeTriangle_hull,codeTriangle_hull]
    change _ = convexHull ℝ (range (codeTriangle D.source (D.triangles.get i)) ∩
      range (codeTriangle D.source (D.triangles.get j)))
    rw [codeTriangle_range,codeTriangle_range]
    exact D.source_faces i j
  target_faces i j := by
    change triangleHull (codeTriangle D.target (D.triangles.get i)) ∩
      triangleHull (codeTriangle D.target (D.triangles.get j)) = _
    rw [codeTriangle_hull,codeTriangle_hull]
    change _ = convexHull ℝ (range (codeTriangle D.target (D.triangles.get i)) ∩
      range (codeTriangle D.target (D.triangles.get j)))
    rw [codeTriangle_range,codeTriangle_range]
    exact D.target_faces i j

theorem sourceCarrier_eq : D.meshPair.closedCharts.sourceCarrier =
    ⋃ i : Fin D.triangles.length, integerHull (triangleVertexList D.source (D.triangles.get i)) := by
  change (⋃ i : Fin D.triangles.length, triangleHull (codeTriangle D.source (D.triangles.get i))) = _
  simp only [codeTriangle_hull]

theorem targetCarrier_eq : D.meshPair.closedCharts.targetCarrier =
    ⋃ i : Fin D.triangles.length, integerHull (triangleVertexList D.target (D.triangles.get i)) := by
  change (⋃ i : Fin D.triangles.length, triangleHull (codeTriangle D.target (D.triangles.get i))) = _
  simp only [codeTriangle_hull]

/-- The finite integer certificates give an actual full-carrier homeomorphism. -/
def homeomorph : D.meshPair.closedCharts.sourceCarrier ≃ₜ D.meshPair.closedCharts.targetCarrier :=
  D.meshPair.homeomorph

end IntegerMeshPair
end
end SpectreGeometry.ReverseFinitePL
