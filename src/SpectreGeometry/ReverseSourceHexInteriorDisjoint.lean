module

public import SpectreGeometry.ReverseSourceHexIntersections
public import SpectreGeometry.ReverseClusterTriangulationFacesReal

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set HalfplaneCertificate ReverseClusterTriangulation

theorem sourceHex_interior_strict (c : ℤ × ℤ) (p : ℝ × ℝ)
    (hp : p ∈ interior (sourceHexCarrier c)) :
    -1 < 2*(p.1-c.1)+(p.2-c.2) ∧ 2*(p.1-c.1)+(p.2-c.2) < 1 ∧
    -1 < (p.1-c.1)+2*(p.2-c.2) ∧ (p.1-c.1)+2*(p.2-c.2) < 1 ∧
    -1 < (p.1-c.1)-(p.2-c.2) ∧ (p.1-c.1)-(p.2-c.2) < 1 := by
  have strict (a b : ℤ)
      (hn : ∀ x ∈ sourceHexCarrier c,
        0 ≤ (a:ℝ)*(x.1-c.1)+(b:ℝ)*(x.2-c.2)+1) :
      0 < (a:ℝ)*(p.1-c.1)+(b:ℝ)*(p.2-c.2)+1 := by
    let f : Constraint := (a,b,1-a*c.1-b*c.2)
    have he (x : RealPoint) : evalConstraint f x =
        (a:ℝ)*(x.1-c.1)+(b:ℝ)*(x.2-c.2)+1 := by
      dsimp [f,evalConstraint]
      push_cast
      ring
    have hc : 0 < evalConstraint f ((c.1:ℝ),(c.2:ℝ)) := by rw [he]; simp
    have hh := constraint_interior_pos f ((c.1:ℝ),(c.2:ℝ)) hc
      (sourceHexCarrier c) (fun x hx => by rw [he]; exact hn x hx) p hp
    rwa [he] at hh
  have h1 := strict 2 1 (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  have h2 := strict (-2) (-1) (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  have h3 := strict 1 2 (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  have h4 := strict (-1) (-2) (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  have h5 := strict 1 (-1) (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  have h6 := strict (-1) 1 (by
    intro x hx; rcases hx with ⟨h1,h2,h3,h4,h5,h6⟩; norm_num; linarith)
  norm_num at h1 h2 h3 h4 h5 h6
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- The interior of one source hexagon misses every distinct closed carrier. -/
theorem sourceHex_interior_disjoint_carrier (c c' : ℤ × ℤ) (hne : c ≠ c') :
    Disjoint (interior (sourceHexCarrier c)) (sourceHexCarrier c') := by
  apply Set.disjoint_left.mpr
  intro p hp hp'
  obtain ⟨d,rfl⟩ := sourceHex_intersection_neighbor (Ne.symm hne)
    ⟨p,interior_subset hp,hp'⟩
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := sourceHex_interior_strict c p hp
  fin_cases d <;>
    norm_num [sourceHexCarrier,sourceHexOffset,sourceHexNeighbor,SpectreFinite.direction] at hp' <;>
    rcases hp' with ⟨g1,g2,g3,g4,g5,g6⟩ <;> linarith

theorem sourceHex_interiors_disjoint (c c' : ℤ × ℤ) (hne : c ≠ c') :
    Disjoint (interior (sourceHexCarrier c)) (interior (sourceHexCarrier c')) :=
  (sourceHex_interior_disjoint_carrier c c' hne).mono_right interior_subset
end
end SpectreGeometry.ReverseExistence
