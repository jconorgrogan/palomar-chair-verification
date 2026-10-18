module

public import SpectreGeometry.ReverseRawChartCoverage
public import SpectreGeometry.ReversePlacedClusterPieces

@[expose] public section


namespace SpectreGeometry.ReversePhysicalClusterCharts
noncomputable section
open Set SpectreClusters Deformation ReverseExistence ReversePhysicalCluster
open ReverseClusterTriangulation

/-- All raw inverse-chart hulls together are exactly the literal cluster carrier. -/
theorem chartFamily_covers_rawCluster
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (big : Bool) :
    rawClusterBody (if big then .t8h else .t7h) =
      ⋃ z : Fin (chartFamily big).length,
        integerHull ((chartFamily big).getD z.val default).vertices := by
  have hp (n : Fin (pieces big).length) :
      placementKiteBody ((pieces big).get n) =
        ⋃ i : Fin 12, integerHull (rawChartVertices big n.val i) := by
    have h := raw_piece_covered_by_chart_triangles big n.val
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem n.isLt,
      Option.getD_some,List.get_eq_getElem] using h
  have hc : rawClusterBody (if big then .t8h else .t7h) =
      ⋃ n : Fin (pieces big).length, placementKiteBody ((pieces big).get n) :=
    rawClusterBody_eq_indexed_pieces _
  rw [hc]
  simp_rw [hp]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨n,i,hx⟩
    have hz : 12*n.val+i.val < (chartFamily big).length := by
      rw [chartFamily_length]
      omega
    refine ⟨⟨12*n.val+i.val,hz⟩,?_⟩
    rw [(hbinding big _ hz).2]
    have hd : (12*n.val+i.val)/12=n.val := by omega
    have hm : (⟨(12*n.val+i.val)%12,Nat.mod_lt _ (by decide)⟩ : Fin 12)=i := by
      apply Fin.ext
      change (12*n.val+i.val)%12=i.val
      omega
    simpa only [hd,hm] using hx
  · rintro ⟨z,hx⟩
    have hn : z.val/12 < (pieces big).length := by
      have hz := lt_of_lt_of_eq z.isLt (chartFamily_length big)
      omega
    rw [(hbinding big _ z.isLt).2] at hx
    exact ⟨⟨z.val/12,hn⟩,⟨z.val%12,Nat.mod_lt _ (by decide)⟩,hx⟩

theorem chartFamily_covers_markedCluster
    (hbinding : ∀ big z, z < (chartFamily big).length → ChartPacketBinding big z)
    (k : Fin 9) :
    rawClusterBody (SpectreClusters.ReverseExistence.clusterOfMark k) =
      ⋃ z : Fin (chartFamily (k.val != 0)).length,
        integerHull ((chartFamily (k.val != 0)).getD z.val default).vertices := by
  have h := chartFamily_covers_rawCluster hbinding (k.val != 0)
  simpa only [SpectreClusters.ReverseExistence.clusterOfMark,bne_iff_ne,ne_eq,
    ite_not] using h

end
end SpectreGeometry.ReversePhysicalClusterCharts
