module

public import SpectreGeometry.ReverseFinitePLScaledMesh
public import SpectreGeometry.ReverseFinitePLInteriorCases

@[expose] public section


namespace SpectreGeometry.ReverseFinitePL
noncomputable section
open Set
namespace IntegerMeshPair
variable (D : IntegerMeshPair)

private theorem scaled_lineMap (a : ℝ) (p q : Plane) (t : ℝ) :
    a • AffineMap.lineMap p q t = AffineMap.lineMap (a • p) (a • q) t := by
  ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    smul_eq_mul] <;> ring

/-- The finite mesh point classification remains valid after source and target
normalization. Only normalized vertex and open-edge neighborhoods are required. -/
theorem scaledHomeomorph_mem_interior_of_boundary
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : ((fun p : Plane => a • p) '' D.meshPair.closedCharts.sourceCarrier))
    (T : Set Plane)
    (hT : ((fun p : Plane => b • p) '' D.meshPair.closedCharts.targetCarrier) ⊆ T)
    (hv : ∀ i v, x.val = a • D.sourceVertex (D.meshIndex i v) →
      b • D.targetVertex (D.meshIndex i v) ∈ interior T)
    (he : ∀ i v w, v ≠ w → ∀ t ∈ Ioo (0:ℝ) 1,
      x.val = AffineMap.lineMap (a • D.sourceVertex (D.meshIndex i v))
        (a • D.sourceVertex (D.meshIndex i w)) t →
      AffineMap.lineMap (b • D.targetVertex (D.meshIndex i v))
        (b • D.targetVertex (D.meshIndex i w)) t ∈ interior T) :
    (D.scaledHomeomorph a b ha hb x).val ∈ interior T := by
  let H := (scalarHomeomorph a ha).image D.meshPair.closedCharts.sourceCarrier
  let y := H.symm x
  let K := scalarHomeomorph b hb
  have hxy : a • y.val = x.val := congrArg Subtype.val (H.apply_symm_apply x)
  have hi : (D.meshPair.homeomorph y).val ∈ interior (K ⁻¹' T) := by
    apply D.meshPair.homeomorph_mem_interior_of_boundary y (K ⁻¹' T)
    · intro z hz
      exact hT ⟨z,hz,rfl⟩
    · intro i v hy
      rw [←K.preimage_interior]
      exact hv i v (hxy.symm.trans (congrArg (fun p : Plane => a • p) hy))
    · intro i v w hvw t ht hy
      rw [←K.preimage_interior]
      have hx : x.val = AffineMap.lineMap (a • D.sourceVertex (D.meshIndex i v))
          (a • D.sourceVertex (D.meshIndex i w)) t := by
        rw [←scaled_lineMap]
        exact hxy.symm.trans (congrArg (fun p : Plane => a • p) hy)
      change b • AffineMap.lineMap _ _ t ∈ interior T
      rw [scaled_lineMap]
      exact he i v w hvw t ht hx
  rw [←K.preimage_interior] at hi
  change b • (D.homeomorph y).val ∈ interior T
  exact hi

end IntegerMeshPair
end
end SpectreGeometry.ReverseFinitePL
