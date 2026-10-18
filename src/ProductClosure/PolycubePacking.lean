module

public import ProductClosure.CarrierLocal
public import Mathlib.Topology.NhdsWithin

@[expose] public section

/-! Exact link from disjoint integer-cell ownership to Euclidean packings. -/
namespace ProductClosure.Polycube
open Set
noncomputable section
variable {d : ℕ}

theorem closure_openLatticeCell (z : LatticeIndex d) :
    closure (openLatticeCell z) = latticeCell z := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  have ho : openLatticeCell z = e ⁻¹' (Set.pi Set.univ (fun i => Ioo (z i : ℝ) ((z i : ℝ) + 1))) := by
    ext x
    simp [openLatticeCell, e]
  rw [ho, ← e.preimage_closure, closure_pi_set]
  have hne (i : Fin d) : (z i : ℝ) ≠ (z i : ℝ) + 1 := by linarith
  ext x
  simp [latticeCell, closure_Ioo (hne _), e, Pi.le_def, ← forall_and]

theorem openLatticeCell_disjoint_carrier {T : Finset (LatticeIndex d)}
    (z : LatticeIndex d) (hz : z ∉ T) : Disjoint (openLatticeCell z) (carrier T) := by
  apply Set.disjoint_left.mpr
  intro x hx ht
  obtain ⟨w, hw, hxw⟩ := (mem_carrier_iff T x).mp ht
  have heq : w = z := by
    funext i
    exact integer_cell_unique (z i) (w i) (x i) (hx i) (hxw i)
  exact hz (heq ▸ hw)

/-- Even closed carrier points cannot lie strictly inside a carrier with
entirely different occupied integer cells. -/
theorem carrier_disjoint_interior_of_disjoint {S T : Finset (LatticeIndex d)}
    (hST : Disjoint S T) : Disjoint (carrier S) (interior (carrier T)) := by
  apply Set.disjoint_left.mpr
  intro x hx ht
  obtain ⟨z, hz, hxz⟩ := (mem_carrier_iff S x).mp hx
  have hzT : z ∉ T := fun h => Finset.disjoint_left.mp hST hz h
  have hd : Disjoint (openLatticeCell z) (interior (carrier T)) :=
    (openLatticeCell_disjoint_carrier z hzT).mono_right interior_subset
  have hdc := hd.closure_left isOpen_interior
  rw [closure_openLatticeCell] at hdc
  exact Set.disjoint_left.mp hdc hxz ht

theorem carrier_interiors_disjoint_of_disjoint {S T : Finset (LatticeIndex d)}
    (hST : Disjoint S T) : Disjoint (interior (carrier S)) (interior (carrier T)) :=
  (carrier_disjoint_interior_of_disjoint hST).mono_left interior_subset

/-- Conversely a shared occupied cell forces overlapping actual interiors. -/
theorem carrier_interiors_disjoint_iff {S T : Finset (LatticeIndex d)} :
    Disjoint (interior (carrier S)) (interior (carrier T)) ↔ Disjoint S T := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro z hzS hzT
    have hcS : interior (latticeCell z) ⊆ interior (carrier S) :=
      interior_mono (fun x hx => (mem_carrier_iff S x).mpr ⟨z, hzS, hx⟩)
    have hcT : interior (latticeCell z) ⊆ interior (carrier T) :=
      interior_mono (fun x hx => (mem_carrier_iff T x).mpr ⟨z, hzT, hx⟩)
    have hz : latticeCenter z ∈ interior (latticeCell z) := by
      rw [interior_latticeCell]
      exact latticeCenter_mem_open z
    exact Set.disjoint_left.mp h (hcS hz) (hcT hz)
  · exact carrier_interiors_disjoint_of_disjoint

theorem exists_latticeCell (x : Space d) : ∃ z : LatticeIndex d, x ∈ latticeCell z := by
  refine ⟨fun i => ⌊x i⌋, fun i => ?_⟩
  exact ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩

end
end ProductClosure.Polycube
