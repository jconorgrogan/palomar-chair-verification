module

public import SpectreGeometry.ReverseMeshEdgeIncidenceData
public import SpectreGeometry.ReverseSourceHexBoundary

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set ReverseClusterTriangulation ReverseFinitePL ReverseMeshEdgeIncidence

private theorem lineMap_subdivision (a b : ℝ × ℝ) (u v t : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap a b u) (AffineMap.lineMap a b v) t =
      AffineMap.lineMap a b ((1-t)*u+t*v) := by
  ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
    Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring

private theorem boundary_edge_forward_not_interior
    (hcert : ∀ k i, BoundaryEdgeCertificate k i) (k : Fin 9) (n : Nat)
    (hn : n < boundarySize (k.val != 0)) (t : ℝ) :
    AffineMap.lineMap
      ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k n))
      ((1/(3*(sourceScale k:ℝ))) • integerPoint
        (sourceVertex k ((n+1)%boundarySize (k.val != 0)))) t ∉
      interior (sourceHexCarrier (0,0)) := by
  have hc := hcert k n hn
  dsimp only at hc
  obtain ⟨hd,hj,ha,hb⟩ := hc
  have h0 := normalized_boundary_vertex k _ _ (Nat.lt_of_succ_lt hj)
  have h1 := normalized_boundary_vertex k _ _ hj
  rw [ha] at h0
  rw [hb] at h1
  rw [h0,h1,lineMap_subdivision]
  exact sourceHex_side_line_not_interior _ _

/-- With the explicit finite boundary-edge certificate, either orientation of
an actual consecutive mesh boundary edge lies on a supporting line. -/
theorem mesh_boundary_edge_not_interior
    (hcert : ∀ k i, BoundaryEdgeCertificate k i) (k : Fin 9) (n m : Nat)
    (hn : n < boundarySize (k.val != 0)) (hm : m < boundarySize (k.val != 0))
    (hadj : (n+1)%boundarySize (k.val != 0)=m ∨
      (m+1)%boundarySize (k.val != 0)=n) (t : ℝ) :
    AffineMap.lineMap
      ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k n))
      ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k m)) t ∉
      interior (sourceHexCarrier (0,0)) := by
  rcases hadj with h | h
  · rw [←h]
    exact boundary_edge_forward_not_interior hcert k n hn t
  · have he : AffineMap.lineMap
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k n))
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k m)) t =
      AffineMap.lineMap
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k m))
        ((1/(3*(sourceScale k:ℝ))) • integerPoint (sourceVertex k n)) (1-t) := by
      ext <;> simp only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,
        Prod.fst_add,Prod.snd_add,Prod.fst_sub,Prod.snd_sub,
        Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
    rw [he,←h]
    exact boundary_edge_forward_not_interior hcert k m hm (1-t)

end
end SpectreGeometry.ReverseExistence
