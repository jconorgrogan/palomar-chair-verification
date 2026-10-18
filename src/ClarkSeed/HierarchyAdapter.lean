module

public import ClarkSeed.CellAdapter
public import SparseMonotiles.CarrierHierarchyCharts

@[expose] public section

/-! Full-state group, ownership, and complete-world transport for the recovered
registered CLARK chair. No hierarchy or legality is assumed by the adapter. -/
namespace ClarkSeed.PoseAdapter
noncomputable section
open SparseMonotiles

@[simp] theorem toRegistered_compose {d : ℕ} (p q : Contact.Pose d) :
    toRegistered (SparseMonotiles.CarrierHierarchy.compose p q) = (toRegistered p).comp (toRegistered q) := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  exact add_comm (p.sign i * q.shift (p.perm i)) (p.shift i)

@[simp] theorem toRegistered_inversePose {d : ℕ} (p : Contact.Pose d) :
    toRegistered (SparseMonotiles.CarrierHierarchy.inversePose p) = (toRegistered p).inv := by
  apply RegisteredPrime.Pose.Same.eq
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro i
  change -p.sign (p.perm.symm i) * p.shift (p.perm.symm i) =
    -(p.sign (p.perm.symm i) * p.shift (p.perm.symm i))
  ring

@[simp] theorem toRegistered_normalize {d : ℕ} (p q : Contact.Pose d) :
    toRegistered (SparseMonotiles.CarrierHierarchy.normalize p q) = (toRegistered p).relative (toRegistered q) := by
  simp [SparseMonotiles.CarrierHierarchy.normalize, RegisteredPrime.Pose.relative]

@[simp] theorem toContact_relative {d : ℕ} (p q : RegisteredPrime.Pose d) :
    toContact (p.relative q) = SparseMonotiles.CarrierHierarchy.normalize (toContact p) (toContact q) := by
  apply toRegistered_injective
  simp

@[simp] theorem toRegistered_rootPose (d : ℕ) :
    toRegistered (SparseMonotiles.CarrierHierarchy.rootPose d) = RegisteredPrime.identityPose d := by
  apply RegisteredPrime.Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem occupies_iff_placedCells {m : ℕ} (p : Contact.Pose (m+1))
    (z : Contact.Cell (m+1)) :
    SparseMonotiles.CarrierHierarchy.Occupies p z ↔ z ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)
      (toRegistered p) := inverseCell_mem_iff_placedCells p z

theorem adjacentCells_iff {d : ℕ} (c b : Contact.Cell d) :
    SparseMonotiles.CarrierHierarchy.AdjacentCells c b ↔ ProductClosure.World.LatticeAdjacent c b := by
  constructor
  · rintro ⟨i, hi, hj⟩
    rcases hi with hi | hi
    · refine ⟨i, true, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j; simpa [ProductClosure.World.latticeStep, sub_eq_add_neg] using hi
      · simp [ProductClosure.World.latticeStep, hji, hj j hji]
    · refine ⟨i, false, ?_⟩
      funext j
      by_cases hji : j = i
      · subst j; simpa [ProductClosure.World.latticeStep, sub_eq_add_neg] using hi
      · simp [ProductClosure.World.latticeStep, hji, hj j hji]
  · rintro ⟨i, sign, rfl⟩
    refine ⟨i, ?_, ?_⟩
    · cases sign <;> simp [ProductClosure.World.latticeStep, sub_eq_add_neg]
    · intro j hji
      simp [ProductClosure.World.latticeStep, hji]

/-- Old cell contact uses exactly actual neighboring occupied cells. -/
theorem cellContact_iff {m : ℕ} (p q : Contact.Pose (m+1)) :
    SparseMonotiles.CarrierHierarchy.CellContact p q ↔ ∃ c b,
      c ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m) (toRegistered p) ∧
      b ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m) (toRegistered q) ∧
      ProductClosure.World.LatticeAdjacent c b := by
  simp only [SparseMonotiles.CarrierHierarchy.CellContact, occupies_iff_placedCells, adjacentCells_iff]

/-- Send an actual complete recovered world to the current full-state world. -/
def toWorld {m : ℕ} (W : SparseMonotiles.CarrierHierarchy.RegisteredWorld (m+1)) :
    ProductClosure.World.CompleteTiling (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)) where
  tiles := toRegistered '' W.tiles
  cover := by
    intro z
    obtain ⟨p, hp, hz⟩ := W.covers z
    exact ⟨toRegistered p, ⟨p, hp, rfl⟩, (occupies_iff_placedCells p z).mp hz⟩
  disjoint := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    apply Set.disjoint_left.mpr
    intro z hpz hqz
    apply hne
    exact congrArg toRegistered (W.disjoint p hp q hq z
      ((occupies_iff_placedCells p z).mpr hpz) ((occupies_iff_placedCells q z).mpr hqz))
  nonempty := fun p _ => ProductClosure.World.placedCells_nonempty (ProductClosure.ChairBridge.cells_nonempty m) p

/-- Decode every new complete world into the recovered full-pose world. -/
def fromWorld {m : ℕ}
    (W : ProductClosure.World.CompleteTiling (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m))) :
    SparseMonotiles.CarrierHierarchy.RegisteredWorld (m+1) where
  tiles := {p | toRegistered p ∈ W.tiles}
  covers := by
    intro z
    obtain ⟨p, hp, hz⟩ := W.cover z
    refine ⟨toContact p, ?_, ?_⟩
    · simpa using hp
    · apply (occupies_iff_placedCells _ _).mpr
      simpa using hz
  disjoint := by
    intro p hp q hq z hpz hqz
    apply toRegistered_injective
    by_contra hne
    exact Set.disjoint_left.mp (W.disjoint _ hp _ hq hne)
      ((occupies_iff_placedCells p z).mp hpz) ((occupies_iff_placedCells q z).mp hqz)

@[simp] theorem mem_fromWorld {m : ℕ}
    (W : ProductClosure.World.CompleteTiling (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)))
    (p : Contact.Pose (m+1)) : p ∈ (fromWorld W).tiles ↔ toRegistered p ∈ W.tiles := Iff.rfl

@[simp] theorem mem_toWorld {m : ℕ} (W : SparseMonotiles.CarrierHierarchy.RegisteredWorld (m+1))
    (p : Contact.Pose (m+1)) : toRegistered p ∈ (toWorld W).tiles ↔ p ∈ W.tiles := by
  change toRegistered p ∈ toRegistered '' W.tiles ↔ _
  constructor
  · rintro ⟨q, hq, he⟩
    exact toRegistered_injective he ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The transported law refers to the exact recovered relative pose. -/
def language {d : ℕ} (L : Set (Contact.Pose d))
    (p q : RegisteredPrime.Pose d) : Prop := toContact (p.relative q) ∈ L

theorem fromWorld_legal {m : ℕ}
    (W : ProductClosure.World.CompleteTiling (ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m)))
    (L : Set (Contact.Pose (m+1)))
    (hlegal : W.IsLegal ProductClosure.World.LatticeAdjacent (language L)) : (fromWorld W).Legal L := by
  intro p hp q hq hne hcontact
  obtain ⟨c, b, hc, hb, hadj⟩ := (cellContact_iff p q).mp hcontact
  have hcp := W.owner_eq_of_mem hp hc
  have hbq := W.owner_eq_of_mem hq hb
  have hne' : W.owner c ≠ W.owner b := by
    rw [hcp, hbq]
    exact fun he => hne (toRegistered_injective he)
  have hl := hlegal c b hadj hne'
  simpa [language, hcp, hbq] using hl

theorem toWorld_legal {m : ℕ} (W : SparseMonotiles.CarrierHierarchy.RegisteredWorld (m+1))
    (L : Set (Contact.Pose (m+1))) (hlegal : W.Legal L) :
    (toWorld W).IsLegal ProductClosure.World.LatticeAdjacent (language L) := by
  intro c b hadj hne
  obtain ⟨p, hp, hcp⟩ := (toWorld W).owner_mem c
  obtain ⟨q, hq, hbq⟩ := (toWorld W).owner_mem b
  have hc : c ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m) (toRegistered p) := by
    rw [hcp]; exact (toWorld W).mem_owner c
  have hb : b ∈ ProductClosure.World.placedCells (ProductClosure.ChairBridge.cells m) (toRegistered q) := by
    rw [hbq]; exact (toWorld W).mem_owner b
  have hpq : p ≠ q := by
    intro he; apply hne
    rw [← hcp, ← hbq, he]
  have hl := hlegal p hp q hq hpq ((cellContact_iff p q).mpr ⟨c, b, hc, hb, hadj⟩)
  change toContact (((toWorld W).owner c).relative ((toWorld W).owner b)) ∈ L
  rw [← hcp, ← hbq, toContact_relative, toContact_toRegistered, toContact_toRegistered]
  exact hl

#print axioms toRegistered_normalize
#print axioms toWorld
#print axioms fromWorld
#print axioms fromWorld_legal
#print axioms toWorld_legal
end
end ClarkSeed.PoseAdapter
