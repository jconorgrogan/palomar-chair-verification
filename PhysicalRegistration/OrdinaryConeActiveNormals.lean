module

public import PhysicalRegistration.OrdinaryConeInterior

@[expose] public section

/-! Actual ordinary cones have a nonempty orthogonal set of active unit
normals. These are consequences of literal carrier boundary membership. -/
namespace PhysicalRegistration.NativeChair
open scoped InnerProductSpace
open Set
noncomputable section

theorem placedActiveCarrierNormals_pairwise_orthogonal {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m) :
    (↑(placedActiveCarrierNormals f x) : Set (Space m)).Pairwise (fun n w => ⟪n, w⟫_ℝ = 0) := by
  intro n hn w hw hnw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  apply placedCoordinateNormal_orthogonal
  intro hij
  subst j
  exact hnw rfl

theorem placedActiveCarrierNormals_nonempty_of_carrier_frontier {m : ℕ}
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ frontier (carrier m)) :
    (placedActiveCarrierNormals f x).Nonempty := by
  obtain ⟨i, hi⟩ := carrier_frontier_coordinate (f.symm x) hx
  refine ⟨placedCoordinateNormal f i, Finset.mem_image.mpr ⟨i, ?_, rfl⟩⟩
  simpa [activeCarrierAxes] using hi

theorem placedActiveCarrierNormals_nonempty
    {m J : ℕ} [NeZero m] (hm : 2 ≤ m) (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u) :
    (placedActiveCarrierNormals f x).Nonempty := by
  have houtside := (frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey).1
  exact placedActiveCarrierNormals_nonempty_of_carrier_frontier f x
    ((frontier_body_iff_frontier_carrier_of_not_mem_closedTube a (f.symm x) houtside).mp hx)

#print axioms placedActiveCarrierNormals_nonempty
end
end PhysicalRegistration.NativeChair
