module

public import ProductClosure.ProductWorldCore

@[expose] public section

/-!
# Complete product worlds are Cartesian, with full placed states

The only local assumption is the actual product mate language on neighboring
occupied cells. A wrong-factor contact is excluded using the shared passive
cell and factor-footprint disjointness. Integer-lattice connectivity then
proves complete coordinate independence, so independently phase-shifted
columns cannot satisfy this language.
-/
namespace ProductClosure.World

open Set
noncomputable section
universe u v

namespace CompleteTiling
variable {m n : ℕ} {A : Type u} {B : Type v}
  {cellsA : A → Set (Lattice m)} {cellsB : B → Set (Lattice n)}
  {MA : A → A → Prop} {MB : B → B → Prop}
variable (W : CompleteTiling (productCells cellsA cellsB))

/-- Reference section, used only to name the active factor after independence
has been proved. It does not assume the section is a complete factor world. -/
def activeOwner (x : Lattice m) : A := (W.owner (x, 0)).1

def passiveOwner (y : Lattice n) : B := (W.owner (0, y)).2

/-- Moving through an active-coordinate neighboring cell preserves the entire
passive placed state. A passive-language alternative would force a common
passive cell to lie in two disjoint footprints. -/
theorem passive_owner_step
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepB : Separates cellsB MB)
    (x : Lattice m) (y : Lattice n) (i : Fin m) (b : Bool) :
    (W.owner (latticeStep x i b, y)).2 = (W.owner (x, y)).2 := by
  by_cases heq : W.owner (x, y) = W.owner (latticeStep x i b, y)
  · exact (congrArg Prod.snd heq).symm
  obtain hA | hB := hlegal (x, y) (latticeStep x i b, y)
    (Or.inl ⟨⟨i, b, rfl⟩, rfl⟩) heq
  · exact hA.2.symm
  · exact False.elim (Set.disjoint_left.mp (hsepB _ _ hB.2)
      (W.mem_owner (x, y)).2 (W.mem_owner (latticeStep x i b, y)).2)

/-- The symmetric neighboring-cell argument preserves the active placed
state across every passive-coordinate step. -/
theorem active_owner_step
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA)
    (x : Lattice m) (y : Lattice n) (i : Fin n) (b : Bool) :
    (W.owner (x, latticeStep y i b)).1 = (W.owner (x, y)).1 := by
  by_cases heq : W.owner (x, y) = W.owner (x, latticeStep y i b)
  · exact (congrArg Prod.fst heq).symm
  obtain hA | hB := hlegal (x, y) (x, latticeStep y i b)
    (Or.inr ⟨rfl, ⟨i, b, rfl⟩⟩) heq
  · exact False.elim (Set.disjoint_left.mp (hsepA _ _ hA.1)
      (W.mem_owner (x, y)).1 (W.mem_owner (x, latticeStep y i b)).1)
  · exact hB.1.symm

/-- Complete global owner factorization, including all frame data carried
by either state. This compares every cell of every column. -/
theorem owner_factorizes
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    (x : Lattice m) (y : Lattice n) :
    W.owner (x, y) = (W.activeOwner x, W.passiveOwner y) := by
  apply Prod.ext
  · exact eq_of_latticeStep_invariant (fun z => (W.owner (x, z)).1)
      (fun z i b => W.active_owner_step hlegal hsepA x z i b) y 0
  · exact eq_of_latticeStep_invariant (fun z => (W.owner (z, y)).2)
      (fun z i b => W.passive_owner_step hlegal hsepB z y i b) x 0

/-- The actual tile set is exactly the Cartesian product of the two derived
factor-state sets. This excludes missing tile combinations and phantom tiles. -/
theorem tiles_cartesian
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    W.tiles = Set.range W.activeOwner ×ˢ Set.range W.passiveOwner := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨x, y⟩, hxy⟩ := W.nonempty t ht
    have ht' : (W.activeOwner x, W.passiveOwner y) = t :=
      (W.owner_factorizes hlegal hsepA hsepB x y).symm.trans (W.owner_eq_of_mem ht hxy)
    have ha := congrArg (fun p : A × B => p.1) ht'
    have hb := congrArg (fun p : A × B => p.2) ht'
    exact ⟨⟨x, ha⟩, ⟨y, hb⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have ht' : W.owner (x, y) = t := by
      rw [W.owner_factorizes hlegal hsepA hsepB, hx, hy]
    exact ht' ▸ W.owner_mem (x, y)

theorem mem_activeOwner (x : Lattice m) : x ∈ cellsA (W.activeOwner x) :=
  (W.mem_owner (x, 0)).1

theorem mem_passiveOwner (y : Lattice n) : y ∈ cellsB (W.passiveOwner y) :=
  (W.mem_owner (0, y)).2

/-- Any active footprint occurrence determines the same active owner,
regardless of the passive reference section. -/
theorem activeOwner_eq_of_mem
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    {a : A} (ha : a ∈ Set.range W.activeOwner) {x : Lattice m}
    (hx : x ∈ cellsA a) : W.activeOwner x = a := by
  have ht : (a, W.passiveOwner 0) ∈ W.tiles := by
    rw [W.tiles_cartesian hlegal hsepA hsepB]
    exact ⟨ha, ⟨0, rfl⟩⟩
  exact congrArg Prod.fst (W.owner_eq_of_mem ht ⟨hx, W.mem_passiveOwner 0⟩)

theorem passiveOwner_eq_of_mem
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    {b : B} (hb : b ∈ Set.range W.passiveOwner) {y : Lattice n}
    (hy : y ∈ cellsB b) : W.passiveOwner y = b := by
  have ht : (W.activeOwner 0, b) ∈ W.tiles := by
    rw [W.tiles_cartesian hlegal hsepA hsepB]
    exact ⟨⟨0, rfl⟩, hb⟩
  exact congrArg Prod.snd (W.owner_eq_of_mem ht ⟨W.mem_activeOwner 0, hy⟩)

/-- Derived complete active factor tiling. Coverage and disjointness are
proved from the complete product tiling, rather than being extra assumptions. -/
def activeFactor
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    CompleteTiling cellsA where
  tiles := Set.range W.activeOwner
  cover x := ⟨W.activeOwner x, ⟨x, rfl⟩, W.mem_activeOwner x⟩
  disjoint a ha a' ha' hne := Set.disjoint_left.mpr (by
    intro x hx hx'
    exact hne ((W.activeOwner_eq_of_mem hlegal hsepA hsepB ha hx).symm.trans
      (W.activeOwner_eq_of_mem hlegal hsepA hsepB ha' hx')))
  nonempty a ha := by
    obtain ⟨x, rfl⟩ := ha
    exact ⟨x, W.mem_activeOwner x⟩

/-- Derived complete passive factor tiling. -/
def passiveFactor
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    CompleteTiling cellsB where
  tiles := Set.range W.passiveOwner
  cover y := ⟨W.passiveOwner y, ⟨y, rfl⟩, W.mem_passiveOwner y⟩
  disjoint b hb b' hb' hne := Set.disjoint_left.mpr (by
    intro y hy hy'
    exact hne ((W.passiveOwner_eq_of_mem hlegal hsepA hsepB hb hy).symm.trans
      (W.passiveOwner_eq_of_mem hlegal hsepA hsepB hb' hy')))
  nonempty b hb := by
    obtain ⟨y, rfl⟩ := hb
    exact ⟨y, W.mem_passiveOwner y⟩

@[simp] theorem activeFactor_owner
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) (x : Lattice m) :
    (W.activeFactor hlegal hsepA hsepB).owner x = W.activeOwner x :=
  (W.activeFactor hlegal hsepA hsepB).owner_eq_of_mem ⟨x, rfl⟩ (W.mem_activeOwner x)

@[simp] theorem passiveFactor_owner
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) (y : Lattice n) :
    (W.passiveFactor hlegal hsepA hsepB).owner y = W.passiveOwner y :=
  (W.passiveFactor hlegal hsepA hsepB).owner_eq_of_mem ⟨y, rfl⟩ (W.mem_passiveOwner y)

/-- Active neighboring factor tiles satisfy the factor contact language. -/
theorem activeFactor_legal
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    (W.activeFactor hlegal hsepA hsepB).IsLegal LatticeAdjacent MA := by
  intro x x' hadj hne
  simp only [activeFactor_owner] at hne ⊢
  have hprod : W.owner (x, 0) ≠ W.owner (x', 0) := by
    intro heq
    exact hne (congrArg Prod.fst heq)
  obtain hA | hB := hlegal (x, 0) (x', 0) (Or.inl ⟨hadj, rfl⟩) hprod
  · exact hA.1
  · exact False.elim (hne hB.1)

/-- Passive neighboring factor tiles satisfy the factor contact language. -/
theorem passiveFactor_legal
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB) :
    (W.passiveFactor hlegal hsepA hsepB).IsLegal LatticeAdjacent MB := by
  intro y y' hadj hne
  simp only [passiveFactor_owner] at hne ⊢
  have hprod : W.owner (0, y) ≠ W.owner (0, y') := by
    intro heq
    exact hne (congrArg Prod.snd heq)
  obtain hA | hB := hlegal (0, y) (0, y') (Or.inr ⟨rfl, hadj⟩) hprod
  · exact False.elim (hne hA.2)
  · exact hB.2

#print axioms owner_factorizes
#print axioms tiles_cartesian
#print axioms activeFactor_legal
#print axioms passiveFactor_legal

end CompleteTiling
end
end ProductClosure.World
