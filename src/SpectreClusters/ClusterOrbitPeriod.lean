module

public import SpectreClusters.GridCellConnected
public import SpectreFinite.HexStepField
public import SpectreFinite.ParentPartition

@[expose] public section


/-! Algebraic forward chart and period transport. Only inverse/triangle step
laws, exact marks, cell-contact connectivity and intrinsic covariance occur.
Neither a free action nor an injective coordinate chart is a premise. -/
namespace SpectreClusters.ClusterOrbit
open SpectreFinite SpectreFinite.HexSearch SpectreFinite.HexSearch.ParentOwnership

universe u
variable {X : Type u}

/-- The precise local adjacency interface needed from the actual cluster
partition. Distinct owners of contacting kite cells are directed neighbors. -/
def ContactSteps (S : HexStepSystem X) (own : Cell → X) : Prop :=
  ∀ a b, CellContact a b → own b = own a ∨ ∃ d : Fin 6, own b = S.step d (own a)

/-- Full kite-grid connectivity turns the local directed steps into orbit
reachability of every represented owner. No lattice chart is assumed. -/
theorem represented_in_orbit (S : HexStepSystem X) (own : Cell → X)
    (hstep : ContactSteps S own) (base c : Cell) :
    ∃ v : Position, S.translate v (own base) = own c := by
  let P : Cell → Prop := fun c => ∃ v : Position, S.translate v (own base) = own c
  have hpstep (a b : Cell) (hc : CellContact a b) : P a → P b := by
    rintro ⟨v,hv⟩
    rcases hstep a b hc with he | ⟨d,he⟩
    · exact ⟨v,hv.trans he.symm⟩
    · refine ⟨addPos (direction d) v,?_⟩
      rw [S.translate_add,S.translate_direction,hv]
      exact he.symm
  have hpcontact (a b : Cell) (hc : CellContact a b) : P a = P b := by
    apply propext
    refine ⟨hpstep a b hc,?_⟩
    obtain ⟨z,ha,hb⟩ := hc
    exact hpstep b a ⟨z,hb,ha⟩
  have he : P base = P c := contact_invariant_constant P hpcontact base c
  change P c
  exact he ▸ (show P base from ⟨(0,0),S.translate_zero (own base)⟩)

/-- A source-correct surjective cell owner map makes the action transitive.
This does not assert that its stabilizers are trivial. -/
theorem owner_orbit_surjective (S : HexStepSystem X) (own : Cell → X)
    (hstep : ContactSteps S own) (hsurj : ∀ x, ∃ c, own c = x) (base : Cell) (x : X) :
    ∃ v : Position, S.translate v (own base) = x := by
  obtain ⟨c,rfl⟩ := hsurj x
  exact represented_in_orbit S own hstep base c

/-- An intrinsic symmetry commuting with all six steps commutes with every
axial action element. The action theorem itself derives commutation from
opposite_inverse and triangle, rather than assuming commuting generators. -/
theorem symmetry_translate (S : HexStepSystem X) (T : X → X)
    (hT : ∀ d x, T (S.step d x) = S.step d (T x)) (v : Position) (x : X) :
    T (S.translate v x) = S.translate v (T x) := S.map_translate S T hT v x

/-- A lift of a label-preserving intrinsic symmetry is an actual literal
FieldPeriod of the pulled-back Position-to-State field. -/
theorem lift_is_fieldPeriod (S : HexStepSystem X) (label : X → State)
    (T : X → X) (hT : ∀ d x, T (S.step d x) = S.step d (T x))
    (hlabel : ∀ x, label (T x) = label x) (root : X) (v : Position)
    (hlift : S.translate v root = T root) : FieldPeriod (S.labelField label root) v := by
  intro x
  change label (S.translate (addPos v x) root) = label (S.translate x root)
  have hc : addPos v x = addPos x v := by
    apply Prod.ext <;> simp only [addPos] <;> omega
  rw [hc,S.translate_add,hlift,←symmetry_translate S T hT x root,hlabel]

theorem lift_ne_zero (S : HexStepSystem X) (T : X → X) (root : X)
    (hmoves : T root ≠ root) (v : Position) (hlift : S.translate v root = T root) :
    v ≠ (0,0) := by
  intro he
  rw [he,S.translate_zero] at hlift
  exact hmoves hlift.symm

/-- A nonzero actual symmetry of a connected labelled cluster system yields
one concrete globally legal marked field with a nonzero literal FieldPeriod.
No chart injectivity, action freeness or topological covering theorem is used. -/
theorem actual_symmetry_gives_periodic_marked_field
    (S : HexStepSystem X) (label : X → State)
    (hmatch : ∀ d x, facingMark (placed ((0,0),label x)) d =
      -facingMark (placed ((0,0),label (S.step d x))) (opposite d))
    (own : Cell → X) (hstep : ContactSteps S own) (base : Cell)
    (T : X → X) (hT : ∀ d x, T (S.step d x) = S.step d (T x))
    (hlabel : ∀ x, label (T x) = label x)
    (hrepresented : ∃ c, own c = T (own base)) (hmoves : T (own base) ≠ own base) :
    GloballyLegal (S.labelField label (own base)) ∧
      ∃ v : Position, v ≠ (0,0) ∧ FieldPeriod (S.labelField label (own base)) v := by
  obtain ⟨c,hc⟩ := hrepresented
  obtain ⟨v,hv⟩ := represented_in_orbit S own hstep base c
  have hlift := hv.trans hc
  exact ⟨S.labelField_globallyLegal label hmatch (own base),v,
    lift_ne_zero S T (own base) hmoves v hlift,
    lift_is_fieldPeriod S label T hT hlabel (own base) v hlift⟩

end SpectreClusters.ClusterOrbit
