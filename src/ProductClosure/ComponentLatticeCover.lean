module

public import ProductClosure.ComponentCellCenters
public import ProductClosure.IntegralLatticeCells
public import PhysicalRegistration.LatticeStepConnectivity

@[expose] public section

/-! A real whole-key companion component covers the complete integer cell
lattice. No carrier coverage or component connectedness assumption is used. -/
namespace ProductClosure.NativeCompiler
open Set
noncomputable section
variable {m : ℕ} {S : Finset (LatticeIndex m)}
variable [Nonempty (Polycube.Cell S)]

/-- Each coordinate neighbor of a component cell is forced by an internal
native cell or by an actual whole-key companion across its exposed facet. -/
theorem PhysicalTiling.componentCell_latticeStep
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root : ι} {z : LatticeIndex m}
    (hz : T.ComponentCell root z) (k : Fin (m+1)) (positive : Bool) :
    T.ComponentCell root (latticeStep z k positive) := by
  obtain ⟨i, hi, c, hc⟩ := hz
  let e := relativePlacement (f root) (f i)
  obtain ⟨p, b, t, _, hcenters, hsteps⟩ :=
    (T.keyReachable_integral hm hi).lattice_transport
  have hindex : integralCellIndex p b t (cellIndex c) = z := by
    apply latticeCenter_injective
    have hh := hcenters (cellIndex c)
    rw [latticeCenter_cellIndex] at hh
    exact hh.symm.trans hc
  let j := p.symm k
  let direction := b j == positive
  have hpj : p j = k := p.apply_symm_apply k
  have hbdir : (b j == direction) = positive := by
    dsimp [direction]
    cases b j <;> cases positive <;> rfl
  have htarget : e (latticeCenter (latticeStep (cellIndex c) j direction)) =
      latticeCenter (latticeStep z k positive) := by
    rw [hcenters, hsteps, hindex, hpj, hbdir]
  rcases occupied_cell_neighbor c j direction with hinside | houtside
  · obtain ⟨d, hd⟩ := hinside
    refine ⟨i, hi, d, ?_⟩
    rw [hd, latticeCenter_cellIndex] at htarget
    exact htarget
  · obtain ⟨F, _, hF⟩ := houtside
    obtain ⟨l, hl, d, hd⟩ := T.exists_reachable_outside_center hm hi F
    refine ⟨l, hl, d, ?_⟩
    rw [hF] at htarget
    exact hd.trans htarget

/-- The actual component owns every integer lattice cell. -/
theorem PhysicalTiling.componentCell_all
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (z : LatticeIndex m) :
    T.ComponentCell root z := by
  have h := PhysicalRegistration.NativeChair.eq_univ_of_nonempty_latticeStep_closed
    {w | T.ComponentCell root w} (T.componentCell_nonempty root)
    (fun w hw k b => T.componentCell_latticeStep hm hw k b)
  have hz : z ∈ {w | T.ComponentCell root w} := by rw [h]; exact Set.mem_univ z
  exact hz

/-- Center ownership really is ownership of the complete closed unit cell;
this is derived using actual integral signed-permutation transport. -/
theorem PhysicalTiling.componentCell_image
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root : ι} {z : LatticeIndex m}
    (hz : T.ComponentCell root z) :
    ∃ i, T.KeyReachable root i ∧ ∃ c : Polycube.Cell S,
      relativePlacement (f root) (f i) '' unitCell c = latticeCell z := by
  obtain ⟨i, hi, c, hc⟩ := hz
  obtain ⟨p, b, t, hcells, hcenters, _⟩ :=
    (T.keyReachable_integral hm hi).lattice_transport
  have hindex : integralCellIndex p b t (cellIndex c) = z := by
    apply latticeCenter_injective
    have hh := hcenters (cellIndex c)
    rw [latticeCenter_cellIndex] at hh
    exact hh.symm.trans hc
  refine ⟨i, hi, c, ?_⟩
  simpa only [latticeCell_cellIndex, hindex] using hcells (cellIndex c)

/-- In root coordinates, the actual carrier images of reachable tiles cover
all of space. This conclusion is obtained from lattice-neighbor closure. -/
theorem PhysicalTiling.component_carriers_cover_relative
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (x : Space m) :
    ∃ i, T.KeyReachable root i ∧
      x ∈ relativePlacement (f root) (f i) '' Polycube.carrier S := by
  obtain ⟨z, hz⟩ := exists_latticeCell x
  obtain ⟨i, hi, c, hc⟩ := T.componentCell_image hm (T.componentCell_all hm root z)
  rw [← hc] at hz
  obtain ⟨y, hy, hxy⟩ := hz
  exact ⟨i, hi, y, Set.mem_iUnion.mpr ⟨c, hy⟩, hxy⟩

/-- The same actual component carriers cover in the original world frame. -/
theorem PhysicalTiling.component_carriers_cover
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (x : Space m) :
    ∃ i, T.KeyReachable root i ∧ x ∈ f i '' Polycube.carrier S := by
  obtain ⟨i, hi, y, hy, he⟩ := T.component_carriers_cover_relative hm root ((f root).symm x)
  refine ⟨i, hi, y, hy, ?_⟩
  have hh := congrArg (f root) he
  simpa [relativePlacement] using hh

end
end ProductClosure.NativeCompiler
