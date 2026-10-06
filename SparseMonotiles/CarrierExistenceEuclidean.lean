module

public import SparseMonotiles.CarrierExistenceNested
public import SparseMonotiles.CarrierHierarchyGeometry
public import Mathlib.Topology.Algebra.Module.Cardinality

@[expose] public section

/-! A registered cell world realizes a genuine Euclidean tiling by the literal
undecorated closed carrier. This never replaces the keyed body by its carrier. -/
namespace SparseMonotiles.CarrierHierarchy.Existence
open Contact Set

/-- Points away from every integer coordinate hyperplane. -/
def GridRegular {d : ℕ} (x : Point d) : Prop :=
  ∀ i, x i ∉ Set.range (fun z : ℤ => (z : ℝ))

theorem gridRegular_dense (d : ℕ) : Dense {x : Point d | GridRegular x} := by
  have hr : Dense (Set.range (fun z : ℤ => (z : ℝ)))ᶜ :=
    (Set.countable_range (fun z : ℤ => (z : ℝ))).dense_compl ℝ
  have hp := dense_pi (Set.univ : Set (Fin d)) (fun _ _ => hr)
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toHomeomorph
  have he := hp.preimage e.isOpenMap
  simpa [GridRegular, Set.preimage, Set.pi, e] using he

/-- At a grid-regular point the containing closed unit cell is unique. -/
theorem regular_cell_unique {d : ℕ} {x : Point d} (hr : GridRegular x)
    {c b : Cell d} (hc : x ∈ closedIntegerCell c) (hb : x ∈ closedIntegerCell b) : c = b := by
  funext i
  have hci := hc i
  have hbi := hb i
  have hnc : x i ≠ (c i : ℝ) := by
    intro h
    exact hr i ⟨c i, h.symm⟩
  have hnb : x i ≠ (b i : ℝ) := by
    intro h
    exact hr i ⟨b i, h.symm⟩
  have hcl : (c i : ℝ) < x i := lt_of_le_of_ne hci.1 hnc.symm
  have hbl : (b i : ℝ) < x i := lt_of_le_of_ne hbi.1 hnb.symm
  have hcb : (c i : ℝ) < ((b i + 1 : ℤ) : ℝ) := by push_cast; linarith [hbi.2]
  have hbc : (b i : ℝ) < ((c i + 1 : ℤ) : ℝ) := by push_cast; linarith [hci.2]
  have hcb' := Int.cast_lt.mp hcb
  have hbc' := Int.cast_lt.mp hbc
  omega

def physicalCarriers {d : ℕ} (W : RegisteredWorld d) : Set (Set (Point d)) :=
  (fun p : Pose d => p.euclidean '' carrier d) '' W.tiles

theorem carrier_covers {d : ℕ} (W : RegisteredWorld d) (x : Point d) :
    ∃ p ∈ W.tiles, x ∈ p.euclidean '' carrier d := by
  let c : Cell d := fun i => ⌊x i⌋
  obtain ⟨p, hp, hpc⟩ := W.covers c
  refine ⟨p, hp, (mem_posed_carrier_iff p x).mpr ⟨c, hpc, ?_⟩⟩
  intro i
  exact ⟨Int.floor_le _, le_of_lt (Int.lt_floor_add_one _)⟩

/-- Cell nonoverlap rules out an open overlap of the actual closed carriers:
any such open set contains a point away from the integer grid. -/
theorem carrier_interiors_disjoint {d : ℕ} (W : RegisteredWorld d)
    {p q : Pose d} (hp : p ∈ W.tiles) (hq : q ∈ W.tiles) (hne : p ≠ q) :
    _root_.Disjoint (interior (p.euclidean '' carrier d))
      (interior (q.euclidean '' carrier d)) := by
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨y, ⟨hyp, hyq⟩, hyr⟩ := (gridRegular_dense d).inter_open_nonempty
    (interior (p.euclidean '' carrier d) ∩ interior (q.euclidean '' carrier d))
    (isOpen_interior.inter isOpen_interior) ⟨x, hxp, hxq⟩
  obtain ⟨c, hpc, hyc⟩ := (mem_posed_carrier_iff p y).mp (interior_subset hyp)
  obtain ⟨b, hqb, hyb⟩ := (mem_posed_carrier_iff q y).mp (interior_subset hyq)
  have hcb := regular_cell_unique hyr hyc hyb
  subst b
  exact hne (W.disjoint p hp q hq c hpc hqb)

/-- Full Euclidean carrier tiling, with all points covered and actual tile
interiors disjoint. The tiles are physical sets under genuine isometries. -/
theorem carrier_isTiling {d : ℕ} (W : RegisteredWorld d) :
    IsTiling (carrier d) (physicalCarriers W) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro A ⟨p, hp, rfl⟩
    exact ⟨p.euclidean.toIsometryEquiv, rfl⟩
  · intro x
    obtain ⟨p, hp, hpx⟩ := carrier_covers W x
    exact ⟨p.euclidean '' carrier d, ⟨p, hp, rfl⟩, hpx⟩
  · rintro A ⟨p, hp, rfl⟩ B ⟨q, hq, rfl⟩ hne
    exact carrier_interiors_disjoint W hp hq (fun h => hne (by rw [h]))

/-- Actual tiling nonemptiness from the alternating-ancestor construction. -/
theorem carrier_hasTiling {d : ℕ} (hd : 0 < d)
    (σ : Bits d → Equiv.Perm (Fin d))
    (he : σ (fun _ => false) = Equiv.refl _) : HasTiling (carrier d) :=
  ⟨physicalCarriers (world hd σ he), carrier_isTiling (world hd σ he)⟩

#print axioms gridRegular_dense
#print axioms carrier_isTiling
#print axioms carrier_hasTiling
end SparseMonotiles.CarrierHierarchy.Existence
