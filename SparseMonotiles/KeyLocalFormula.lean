module

public import SparseMonotiles.ReferenceKeyHalfspaces
public import SparseMonotiles.KeySupportAtlas

@[expose] public section

/-!
# Finite Boolean halfspace formulas for isolated physical keys

These formulas describe the exact closed bump/dent modification. Inactive
planes can be frozen using the checked local Boolean calculus. The formulas
are not yet a classification of facet or ridge angles.
-/
namespace SparseMonotiles

open Set

namespace HalfspaceFormula

def allAtoms {ι : Type*} : List ι → HalfspaceFormula ι
  | [] => .truth
  | i :: is => .conj (.atom i) (allAtoms is)

theorem eval_allAtoms {ι : Type*} (a : ι → Prop) (is : List ι) :
    eval a (allAtoms is) ↔ ∀ i ∈ is, a i := by
  induction is with
  | nil => simp [allAtoms, eval]
  | cons i is ih => simp [allAtoms, eval, ih]

noncomputable def allRightAtoms (ι : Type*) [Fintype ι] :
    HalfspaceFormula (Unit ⊕ ι) :=
  allAtoms ((Finset.univ.toList : List ι).map Sum.inr)

theorem eval_allRightAtoms {ι : Type*} [Fintype ι] (a : Unit ⊕ ι → Prop) :
    eval a (allRightAtoms ι) ↔ ∀ i, a (.inr i) := by
  simp [allRightAtoms, eval_allAtoms]

end HalfspaceFormula

namespace Contact.Facet

noncomputable def inwardSlack {d : ℕ} (f : Facet d) (x : Point d) : ℝ :=
  if f.positive then (f.gridFacet.anchor f.axis : ℝ) - x f.axis
  else x f.axis - (f.gridFacet.anchor f.axis : ℝ)

theorem continuous_inwardSlack {d : ℕ} (f : Facet d) : Continuous f.inwardSlack := by
  have hcoord : Continuous (fun x : Point d => x f.axis) :=
    (continuous_apply f.axis).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  change Continuous (fun x : Point d =>
    if f.positive then (f.gridFacet.anchor f.axis : ℝ) - x f.axis
    else x f.axis - (f.gridFacet.anchor f.axis : ℝ))
  cases hp : f.positive
  · exact hcoord.sub continuous_const
  · exact continuous_const.sub hcoord

theorem mem_inwardHalfspace_iff {d : ℕ} (f : Facet d) (x : Point d) :
    x ∈ f.inwardHalfspace ↔ 0 ≤ f.inwardSlack x := by
  cases hp : f.positive <;> simp [inwardHalfspace, inwardSlack, hp, sub_nonneg]

end Contact.Facet

/-- One carrier atom and all pyramid atoms form the exact signed-key formula. -/
noncomputable def isolatedKeyFormula (ι : Type*) [Fintype ι] (b : Bool) :
    HalfspaceFormula (Unit ⊕ ι) :=
  keyReplacementFormula (.atom (.inl ())) (HalfspaceFormula.allRightAtoms ι) b

/-- The formula interpretation is exactly the union or closed-dent difference. -/
theorem region_isolatedKeyFormula {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Contact.Facet d) (slack : ι → Point d → ℝ) (b : Bool) :
    (isolatedKeyFormula ι b).region (Sum.elim (fun _ : Unit => f.inwardSlack) slack) =
      keyReplacement f.inwardHalfspace {x | ∀ i, 0 ≤ slack i x} b := by
  rw [isolatedKeyFormula, region_keyReplacementFormula]
  have hC : HalfspaceFormula.region
      (Sum.elim (fun _ : Unit => f.inwardSlack) slack) (.atom (.inl ())) =
      f.inwardHalfspace := by
    ext x
    exact (f.mem_inwardHalfspace_iff x).symm
  have hK : HalfspaceFormula.region
      (Sum.elim (fun _ : Unit => f.inwardSlack) slack)
      (HalfspaceFormula.allRightAtoms ι) = {x | ∀ i, 0 ≤ slack i x} := by
    ext x
    exact HalfspaceFormula.eval_allRightAtoms _
  rw [hC, hK]

/-- A proved physical halfspace/key germ has this exact finite formula. -/
theorem localSetEq_isolatedKeyFormula {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Contact.Facet d) (slack : ι → Point d → ℝ) (b : Bool)
    {p : Point d} {T K : Set (Point d)}
    (hK : ∀ x, x ∈ K ↔ ∀ i, 0 ≤ slack i x)
    (h : LocalSetEq p T (closure (keyReplacement f.inwardHalfspace K b))) :
    LocalSetEq p T (closure ((isolatedKeyFormula ι b).region
      (Sum.elim (fun _ : Unit => f.inwardSlack) slack))) := by
  have heq : K = {x | ∀ i, 0 ≤ slack i x} := Set.ext hK
  rw [region_isolatedKeyFormula, ← heq]
  exact h

/-- At the point in question all inactive halfspaces can be frozen, including
inside a dent complement and after the final physical closure. -/
theorem localSetEq_frozen_isolatedKeyFormula {d : ℕ} {ι : Type*} [Fintype ι]
    (f : Contact.Facet d) (slack : ι → Point d → ℝ) (b : Bool)
    {p : Point d} {T K : Set (Point d)}
    (hf : ∀ i, ContinuousAt (slack i) p)
    (hK : ∀ x, x ∈ K ↔ ∀ i, 0 ≤ slack i x)
    (h : LocalSetEq p T (closure (keyReplacement f.inwardHalfspace K b))) :
    let fields := Sum.elim (fun _ : Unit => f.inwardSlack) slack
    LocalSetEq p T (closure (((isolatedKeyFormula ι b).freeze fields p).region fields)) := by
  let fields := Sum.elim (fun _ : Unit => f.inwardSlack) slack
  have hcont : ∀ j, ContinuousAt (fields j) p := by
    intro j
    cases j with
    | inl u => exact f.continuous_inwardSlack.continuousAt
    | inr i => exact hf i
  exact (localSetEq_isolatedKeyFormula f slack b hK h).trans
    (HalfspaceFormula.localSetEq_closure_freeze fields p hcont (isolatedKeyFormula ι b))

#print axioms region_isolatedKeyFormula
#print axioms localSetEq_isolatedKeyFormula
#print axioms localSetEq_frozen_isolatedKeyFormula

end SparseMonotiles
