module

public import SparseMonotiles.KeyLocalFormula

@[expose] public section

/-! A finite affine-halfspace formula for the actual closed chair carrier. -/
namespace SparseMonotiles

open Set

/-- The inner boundary remains in the closed carrier. -/
theorem mem_carrier_iff_bounds {d : ℕ} (x : Point d) :
    x ∈ carrier d ↔ (∀ i, 0 ≤ x i ∧ x i ≤ 2) ∧ ∃ i, x i ≤ 1 := by
  classical
  constructor
  · rintro ⟨c, ⟨j, hj⟩, hx⟩
    refine ⟨?_, j, ?_⟩
    · intro i
      have hi := hx i
      cases hc : c i <;> simp only [hc, Bool.false_eq_true, if_false, if_true] at hi
      all_goals constructor <;> linarith [hi.1, hi.2]
    · simpa only [hj, Bool.false_eq_true, if_false, zero_add] using (hx j).2
  · rintro ⟨hx, ⟨j, hj⟩⟩
    let c : Fin d → Bool := fun i => decide (1 < x i)
    refine ⟨c, ⟨j, by simp [c, not_lt.mpr hj]⟩, ?_⟩
    intro i
    by_cases hi : 1 < x i
    · simp only [c, hi, decide_true, if_true]
      exact ⟨le_of_lt hi, by linarith [(hx i).2]⟩
    · simp only [c, hi, decide_false, Bool.false_eq_true, if_false, zero_add]
      exact ⟨(hx i).1, le_of_not_gt hi⟩

namespace HalfspaceFormula

def anyAtoms {ι : Type*} : List ι → HalfspaceFormula ι
  | [] => .falsity
  | i :: is => .disj (.atom i) (anyAtoms is)

theorem eval_anyAtoms {ι : Type*} (a : ι → Prop) (is : List ι) :
    eval a (anyAtoms is) ↔ ∃ i ∈ is, a i := by
  induction is with
  | nil => simp [anyAtoms, eval]
  | cons i is ih => simp [anyAtoms, eval, ih]

end HalfspaceFormula

abbrev CarrierHalfspaceIndex (d : ℕ) := Fin d × Fin 3

noncomputable def carrierHalfspaceSlack {d : ℕ} (j : CarrierHalfspaceIndex d)
    (x : Point d) : ℝ :=
  if j.2 = 0 then x j.1 else if j.2 = 1 then 2 - x j.1 else 1 - x j.1

noncomputable def carrierHalfspaceFormula (d : ℕ) : HalfspaceFormula (CarrierHalfspaceIndex d) :=
  .conj
    (.conj
      (HalfspaceFormula.allAtoms ((Finset.univ.toList : List (Fin d)).map
        fun i => (i, 0)))
      (HalfspaceFormula.allAtoms ((Finset.univ.toList : List (Fin d)).map
        fun i => (i, 1))))
    (HalfspaceFormula.anyAtoms ((Finset.univ.toList : List (Fin d)).map
      fun i => (i, 2)))

theorem carrierHalfspaceFormula_region (d : ℕ) :
    (carrierHalfspaceFormula d).region carrierHalfspaceSlack = carrier d := by
  ext x
  rw [mem_carrier_iff_bounds]
  simp [carrierHalfspaceFormula, HalfspaceFormula.region, HalfspaceFormula.eval,
    HalfspaceFormula.eval_allAtoms, HalfspaceFormula.eval_anyAtoms,
    carrierHalfspaceSlack, sub_nonneg, forall_and]

theorem continuous_carrierHalfspaceSlack {d : ℕ} (j : CarrierHalfspaceIndex d) :
    Continuous (carrierHalfspaceSlack j) := by
  have hcoord : Continuous (fun x : Point d => x j.1) :=
    (continuous_apply j.1).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  change Continuous (fun x : Point d =>
    if j.2 = 0 then x j.1 else if j.2 = 1 then 2 - x j.1 else 1 - x j.1)
  by_cases h0 : j.2 = 0
  · simp only [if_pos h0]
    exact hcoord
  · by_cases h1 : j.2 = 1
    · simp only [if_neg h0, if_pos h1]
      exact continuous_const.sub hcoord
    · simp only [if_neg h0, if_neg h1]
      exact continuous_const.sub hcoord

/-- The entire undecorated carrier has a finite active-plane germ at each point. -/
theorem localSetEq_carrier_frozen_halfspace_formula {d : ℕ} (p : Point d) :
    LocalSetEq p (carrier d) (closure
      (((carrierHalfspaceFormula d).freeze carrierHalfspaceSlack p).region
        carrierHalfspaceSlack)) := by
  have h := HalfspaceFormula.localSetEq_closure_freeze carrierHalfspaceSlack p
    (fun j => (continuous_carrierHalfspaceSlack j).continuousAt) (carrierHalfspaceFormula d)
  simpa only [carrierHalfspaceFormula_region, (carrier_isClosed d).closure_eq] using h

#print axioms mem_carrier_iff_bounds
#print axioms carrierHalfspaceFormula_region
#print axioms localSetEq_carrier_frozen_halfspace_formula

end SparseMonotiles
