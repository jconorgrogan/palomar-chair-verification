module

public import SpectreGeometry.ReversePhysicalClusterData
public import SpectreGeometry.DeformationHomeomorphismAffine

@[expose] public section


/-! Real-coordinate soundness of the exact direct-P cluster poses. These
lemmas identify vertex values; they assert no coverage or disjoint interiors. -/
namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section
open SpectreClusters Deformation

def quarterPoint (p : ExactPoint) : RealPoint := (1/4:ℝ) • ExactPoint.eval p

theorem quarterPoint_add (p q : ExactPoint) :
    quarterPoint (ExactPoint.add p q) = quarterPoint p+quarterPoint q := by
  ext <;> simp only [quarterPoint,ExactPoint.add,ExactPoint.eval,Quad3.eval_add,
    Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,smul_eq_mul] <;> ring

theorem quarterPoint_sub (p q : ExactPoint) :
    quarterPoint (ExactPoint.sub p q) = quarterPoint p-quarterPoint q := by
  ext <;> simp only [quarterPoint,ExactPoint.sub,ExactPoint.eval,Quad3.eval_sub,
    Prod.smul_fst,Prod.smul_snd,Prod.fst_sub,Prod.snd_sub,smul_eq_mul] <;> ring

theorem quarterPoint_sourceVertex4 (k : Fin 12) (e : Fin 14) :
    quarterPoint (sourceVertex4 k e) = SpectreGeometry.rotate k (realVertex e) := by
  rw [quarterPoint,sourceVertex4_eval,smul_smul]
  norm_num

def physicalOrigin (big : Bool) (n : Nat) : RealPoint :=
  quarterPoint ((origins big).getD n ((0,0),(0,0)))

theorem physicalPlacedVertex_real (big : Bool) (n : Nat) (j : Fin 14) :
    quarterPoint (physicalPlacedVertex4 big n j) =
      physicalOrigin big n+SpectreGeometry.rotate
        (physicalTurn ((pieces big).getD n ⟨.turtle,0,(0,0)⟩))
        (realVertex (physicalIndex ((pieces big).getD n ⟨.turtle,0,(0,0)⟩).kind j)) := by
  rw [physicalPlacedVertex4,quarterPoint_add,quarterPoint_sourceVertex4]
  rfl

/-- Each literal raw piece vertex is sent to the stated translated, properly
rotated vertex of the original P polygon. -/
theorem literal_piece_vertex_real (big : Bool) (n : Fin 9)
    (hn : n.val < (pieces big).length) (j : Fin 14) :
    quarterPoint (vertexImage4 big
      (rawPlacedVertex ((pieces big).getD n.val ⟨.turtle,0,(0,0)⟩) j)) =
      physicalOrigin big n.val+SpectreGeometry.rotate
        (physicalTurn ((pieces big).getD n.val ⟨.turtle,0,(0,0)⟩))
        (realVertex (physicalIndex ((pieces big).getD n.val ⟨.turtle,0,(0,0)⟩).kind j)) := by
  rw [all_piece_vertex_values big n hn,physicalPlacedVertex_real]

end
end SpectreGeometry.ReversePhysicalCluster
