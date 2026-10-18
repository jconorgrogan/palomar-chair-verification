module

public import ProductClosure.OrdinaryConeInterior

@[expose] public section

/-! Actual ordinary cones have a nonempty orthogonal set of active unit
normals. These are consequences of literal carrier boundary membership. -/
namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}

theorem placedActiveCarrierNormals_pairwise_orthogonal (polyCells : Finset (Polycube.LatticeIndex (m + 1))) 
    (f : Space m ≃ᵢ Space m) (x : Space m) :
    (↑(placedActiveCarrierNormals polyCells f x) : Set (Space m)).Pairwise (fun n w => ⟪n, w⟫_ℝ = 0) := by
  intro n hn w hw hnw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  apply placedCoordinateNormal_orthogonal
  intro hij
  subst j
  exact hnw rfl

theorem placedActiveCarrierNormals_nonempty_of_carrier_frontier (polyCells : Finset (Polycube.LatticeIndex (m + 1))) 
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ frontier (Polycube.carrier polyCells)) :
    (placedActiveCarrierNormals polyCells f x).Nonempty := by
  obtain ⟨c, i, hi⟩ := carrier_frontier_coordinate polyCells (f.symm x) hx
  refine ⟨placedCoordinateNormal f i, Finset.mem_image.mpr ⟨i, ?_, rfl⟩⟩
  exact (mem_activeCarrierAxes (f.symm x) i).mpr ⟨c, hi⟩

theorem placedActiveCarrierNormals_nonempty
    {J : ℕ} [NeZero m] [Nonempty (Polycube.Cell polyCells)] (hm : 2 ≤ m) (a : Coefficients polyCells J)
    (f : Space m ≃ᵢ Space m) (x : Space m)
    (hx : f.symm x ∈ frontier (body a))
    (hkey : ∀ u, f.symm x ∉ keyGraph a u) :
    (placedActiveCarrierNormals polyCells f x).Nonempty := by
  have houtside := (frontier_body_outside_keyGraphs hm a (f.symm x) hx hkey).1
  exact placedActiveCarrierNormals_nonempty_of_carrier_frontier polyCells f x
    ((frontier_body_iff_frontier_carrier_of_not_mem_closedTube a (f.symm x) houtside).mp hx)

#print axioms placedActiveCarrierNormals_nonempty
end
end ProductClosure.NativeCompiler
