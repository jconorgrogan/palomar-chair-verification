module

public import SpectreGeometry.ReverseFinitePLEdges
public import SpectreGeometry.ReverseFinitePLScaling

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set
namespace IntegerMeshPair
variable (D : IntegerMeshPair)

def scaledHomeomorph (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((fun x : Plane => a • x) '' D.meshPair.closedCharts.sourceCarrier) ≃ₜ
      ((fun x : Plane => b • x) '' D.meshPair.closedCharts.targetCarrier) :=
  ((scalarHomeomorph a ha).image D.meshPair.closedCharts.sourceCarrier).symm.trans
    (D.homeomorph.trans ((scalarHomeomorph b hb).image D.meshPair.closedCharts.targetCarrier))

private theorem smul_lineMap (a : ℝ) (p q : Plane) (t : ℝ) :
    a • AffineMap.lineMap p q t = AffineMap.lineMap (a • p) (a • q) t := by
  ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    smul_eq_mul] <;> ring

/-- Exact edge values remain valid after independent source and target
normalizations, with no carrier coercion assumption left to the caller. -/
theorem scaledHomeomorph_edge (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (j : Fin D.triangles.length) (n m : Fin D.source.length)
    (hn : n.val ∈ SpectreGeometry.ReverseClusterTriangulation.triangleIndices (D.triangles.get j))
    (hm : m.val ∈ SpectreGeometry.ReverseClusterTriangulation.triangleIndices (D.triangles.get j))
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1)
    (x : ((fun p : Plane => a • p) '' D.meshPair.closedCharts.sourceCarrier))
    (hx : x.val = AffineMap.lineMap (a • D.sourceVertex n) (a • D.sourceVertex m) t) :
    (D.scaledHomeomorph a b ha hb x).val =
      AffineMap.lineMap (b • D.targetVertex n) (b • D.targetVertex m) t := by
  let e := (scalarHomeomorph a ha).image D.meshPair.closedCharts.sourceCarrier
  let y := e.symm x
  have hy : y.val = AffineMap.lineMap (D.sourceVertex n) (D.sourceVertex m) t := by
    apply (scalarHomeomorph a ha).injective
    change a • y.val = a • AffineMap.lineMap (D.sourceVertex n) (D.sourceVertex m) t
    have he : a • y.val = x.val := congrArg Subtype.val (e.apply_symm_apply x)
    rw [he,hx,smul_lineMap]
  have he := D.homeomorph_edge j n m hn hm t ht y hy
  change b • (D.homeomorph y).val = _
  rw [he,smul_lineMap]

end IntegerMeshPair
end
end SpectreGeometry.ReverseFinitePL
