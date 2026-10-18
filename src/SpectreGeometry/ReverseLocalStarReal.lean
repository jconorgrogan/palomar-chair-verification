module

public import SpectreGeometry.ReverseLocalStarData
public import SpectreGeometry.ReverseClusterTriangulationFacesAssemblyReal

@[expose] public section


/-! Real soundness of local target-star certificates. A certificate yields
actual neighborhood coverage and exact closed common-face intersections.
Binding the finite stars to occurrences in a marked field is separate. -/
namespace SpectreGeometry.ReverseLocalStars
noncomputable section
open Set HalfplaneCertificate ReverseClusterTriangulation

theorem StarCertificate.faces {ps : List PolygonPacket} {tree : CoverTree}
    {rows : List (List Nat)} (h : StarCertificate ps tree rows) : FamilyHasFaces ps :=
  familyHasFaces_of_rows ps (fun i => rows.getD i []) h.2.2

theorem StarCertificate.ball_subset {ps : List PolygonPacket} {tree : CoverTree}
    {rows : List (List Nat)} (h : StarCertificate ps tree rows) :
    Metric.ball (0 : RealPoint) 1 ⊆ familyBody ps := by
  intro x hx
  apply tree_covered_by_family ps h.1 starBoxFacets tree h.2.1 x
  have hb : |x.1| < 1 ∧ |x.2| < 1 := by
    simpa only [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Prod.fst_zero,Prod.snd_zero,
      sub_zero,max_lt_iff] using hx
  have h1 := abs_lt.mp hb.1
  have h2 := abs_lt.mp hb.2
  norm_num [starBoxFacets,Satisfies,evalConstraint]
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem StarCertificate.origin_interior {ps : List PolygonPacket} {tree : CoverTree}
    {rows : List (List Nat)} (h : StarCertificate ps tree rows) :
    (0 : RealPoint) ∈ interior (familyBody ps) := by
  apply interior_mono h.ball_subset
  rw [Metric.isOpen_ball.interior_eq]
  simp

end
end SpectreGeometry.ReverseLocalStars
