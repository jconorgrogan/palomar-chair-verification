module

public import SpectreGeometry.GridKiteContactBounds

@[expose] public section


/-! Real soundness of a finite closed-kite contact certificate. The concrete
certificate is supplied by the separately checked sector modules. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate GridKiteContact

structure ClosedKiteContactCertificate where
  contact_or_separated : ∀ s t : Turn, ∀ q r : Fin 5,
    let a : Cell := ⟨(0,0),s⟩
    let b : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),t⟩
    cellContactB a b || separatedB (cellVertices a) (cellVertices b) = true
  facets_nonnegative : ∀ s : Turn, ∀ q r : Fin 5,
    let a : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),s⟩
    ∀ line ∈ polygonFacets (cellVertices a), ∀ p ∈ cellVertices a,
      0 ≤ edgeValue line p

/-- Closed real grid kites meet exactly when their finite vertex lists meet. -/
theorem cellContact_iff_gridKiteBody_inter_of_certificate
    (certificate : ClosedKiteContactCertificate) (a b : Cell) :
    CellContact a b ↔ (gridKiteBody a ∩ gridKiteBody b).Nonempty := by
  constructor
  · rintro ⟨v,hva,hvb⟩
    exact ⟨integerPoint v,subset_convexHull ℝ _ ⟨v,hva,rfl⟩,
      subset_convexHull ℝ _ ⟨v,hvb,rfl⟩⟩
  · rintro ⟨x,ha,hb⟩
    have hbounds := gridKite_intersection_center_bounds a b x ha hb
    let q : Fin 5 := ⟨Int.toNat ((sub b.center a.center).1+2),by omega⟩
    let r : Fin 5 := ⟨Int.toNat ((sub b.center a.center).2+2),by omega⟩
    have hdelta : ((q.val : Int)-2,(r.val : Int)-2)=sub b.center a.center := by
      ext <;> simp only [q,r] <;> omega
    let a0 : Cell := ⟨(0,0),a.sector⟩
    let b0 : Cell := ⟨((q.val : Int)-2,(r.val : Int)-2),b.sector⟩
    have hb0 : b0 = relativeCell a b := by
      change Cell.mk _ _ = Cell.mk _ _
      rw [hdelta]
    let y := x-integerPoint (lattice a.center)
    have hA : y ∈ gridKiteBody a0 := by
      rw [gridKiteBody_mem_iff]
      have hz : integerPoint (lattice a0.center) = (0 : RealPoint) := by
        ext <;> norm_num [a0,integerPoint,lattice]
      rw [hz,sub_zero]
      exact (gridKiteBody_mem_iff a x).mp ha
    have hB : y ∈ gridKiteBody b0 := by
      rw [hb0,gridKiteBody_mem_iff]
      convert (gridKiteBody_mem_iff b x).mp hb using 1
      congr 1
      ext <;> simp [y,integerPoint,lattice,sub,relativeCell] <;> ring
    have hc := certificate.contact_or_separated a.sector b.sector q r
    change cellContactB a0 b0 || separatedB (cellVertices a0) (cellVertices b0) = true at hc
    have hc' : cellContactB a0 b0 = true ∨
        separatedB (cellVertices a0) (cellVertices b0) = true := by
      simpa only [Bool.or_eq_true_iff,decide_eq_true_eq] using hc
    rcases hc' with hc | hs
    · apply (contact_relative_iff a b).mpr
      rw [←hb0]
      exact (cellContactB_iff a0 b0).mp hc
    · have hvA : ∀ line ∈ polygonFacets (cellVertices a0), ∀ p ∈ cellVertices a0,
          0 ≤ edgeValue line p := by
        simpa [a0] using certificate.facets_nonnegative a.sector 2 2
      have hvB := certificate.facets_nonnegative b.sector q r
      exact False.elim (Set.disjoint_left.mp
        (separatedB_disjoint (cellVertices a0) (cellVertices b0) hs hvA hvB) hA hB)

end
end SpectreGeometry
