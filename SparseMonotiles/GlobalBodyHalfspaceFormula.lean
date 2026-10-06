module

public import SparseMonotiles.CarrierHalfspaceFormula
public import SparseMonotiles.CanonicalBindings5
public import SparseMonotiles.CanonicalBindings7

@[expose] public section

/-!
# Fixed global halfspace formulas for the exact bodies

The plane family is chosen once, before a generic point is selected. Unlike
local patch selection, this finite family is independent of the point. The
actual closed dent construction is retained by the final closure.
-/
namespace SparseMonotiles

open Set

namespace HalfspaceFormula

def relabel {ι κ : Type*} (f : ι → κ) : HalfspaceFormula ι → HalfspaceFormula κ
  | .truth => .truth
  | .falsity => .falsity
  | .atom i => .atom (f i)
  | .conj A B => .conj (relabel f A) (relabel f B)
  | .disj A B => .disj (relabel f A) (relabel f B)
  | .neg A => .neg (relabel f A)

theorem eval_relabel {ι κ : Type*} (f : ι → κ) (a : κ → Prop) (A : HalfspaceFormula ι) :
    eval a (relabel f A) ↔ eval (fun i => a (f i)) A := by
  induction A with
  | truth => rfl
  | falsity => rfl
  | atom i => rfl
  | conj A B hA hB => exact and_congr hA hB
  | disj A B hA hB => exact or_congr hA hB
  | neg A hA => exact not_congr hA

def anyFormulas {ι : Type*} : List (HalfspaceFormula ι) → HalfspaceFormula ι
  | [] => .falsity
  | A :: As => .disj A (anyFormulas As)

theorem eval_anyFormulas {ι : Type*} (a : ι → Prop) (As : List (HalfspaceFormula ι)) :
    eval a (anyFormulas As) ↔ ∃ A ∈ As, eval a A := by
  induction As with
  | nil => simp [anyFormulas, eval]
  | cons A As ih => simp [anyFormulas, eval, ih]

theorem region_relabel {ι κ X : Type*} (f : ι → κ) (a : κ → X → ℝ)
    (A : HalfspaceFormula ι) :
    (A.relabel f).region a = A.region (fun i => a (f i)) := by
  ext x
  exact eval_relabel f (fun i => 0 ≤ a i x) A

@[simp] theorem region_conj {ι X : Type*} (f : ι → X → ℝ) (A B : HalfspaceFormula ι) :
    (HalfspaceFormula.conj A B).region f = A.region f ∩ B.region f := rfl
@[simp] theorem region_disj {ι X : Type*} (f : ι → X → ℝ) (A B : HalfspaceFormula ι) :
    (HalfspaceFormula.disj A B).region f = A.region f ∪ B.region f := rfl
@[simp] theorem region_neg {ι X : Type*} (f : ι → X → ℝ) (A : HalfspaceFormula ι) :
    (HalfspaceFormula.neg A).region f = (A.region f)ᶜ := rfl

end HalfspaceFormula

abbrev GlobalBodyHalfspaceIndex {d : ℕ} (ks : List (KeyData d)) (ι : Type*) :=
  CarrierHalfspaceIndex d ⊕ (Fin ks.length × ι)

noncomputable def globalBodySlacks {d : ℕ} {ks : List (KeyData d)} {ι : Type*}
    (slack : Fin ks.length → ι → Point d → ℝ) :
    GlobalBodyHalfspaceIndex ks ι → Point d → ℝ
  | .inl j => carrierHalfspaceSlack j
  | .inr (i,j) => slack i j

noncomputable def globalKeyFormula {d : ℕ} (ks : List (KeyData d))
    (ι : Type*) [Fintype ι] (i : Fin ks.length) :
    HalfspaceFormula (GlobalBodyHalfspaceIndex ks ι) :=
  HalfspaceFormula.allAtoms ((Finset.univ.toList : List ι).map fun j => .inr (i,j))

noncomputable def globalKeyUnionFormula {d : ℕ} (ks : List (KeyData d))
    (ι : Type*) [Fintype ι] (b : Bool) :
    HalfspaceFormula (GlobalBodyHalfspaceIndex ks ι) :=
  HalfspaceFormula.anyFormulas ((Finset.univ.toList : List (Fin ks.length)).map fun i =>
    if (ks.get i).bump = b then globalKeyFormula ks ι i else .falsity)

noncomputable def globalBodyFormula {d : ℕ} (ks : List (KeyData d))
    (ι : Type*) [Fintype ι] : HalfspaceFormula (GlobalBodyHalfspaceIndex ks ι) :=
  .conj (.disj ((carrierHalfspaceFormula d).relabel Sum.inl)
    (globalKeyUnionFormula ks ι true)) (.neg (globalKeyUnionFormula ks ι false))

theorem globalKeyFormula_region {d : ℕ} {ks : List (KeyData d)} {ι : Type*} [Fintype ι]
    (slack : Fin ks.length → ι → Point d → ℝ)
    (hkey : ∀ i x, x ∈ keySolid (ks.get i) ↔ ∀ j, 0 ≤ slack i j x) (i : Fin ks.length) :
    (globalKeyFormula ks ι i).region (globalBodySlacks slack) = keySolid (ks.get i) := by
  ext x
  change HalfspaceFormula.eval (fun j => 0 ≤ globalBodySlacks slack j x)
    (globalKeyFormula ks ι i) ↔ _
  simp only [globalKeyFormula, HalfspaceFormula.eval_allAtoms, List.forall_mem_map,
    Finset.mem_toList, Finset.mem_univ, forall_true_left, globalBodySlacks]
  exact (hkey i x).symm

theorem globalKeyUnionFormula_region {d : ℕ} {ks : List (KeyData d)} {ι : Type*} [Fintype ι]
    (slack : Fin ks.length → ι → Point d → ℝ)
    (hkey : ∀ i x, x ∈ keySolid (ks.get i) ↔ ∀ j, 0 ≤ slack i j x) (b : Bool) :
    (globalKeyUnionFormula ks ι b).region (globalBodySlacks slack) = keyUnion ks b := by
  classical
  ext x
  change HalfspaceFormula.eval (fun j => 0 ≤ globalBodySlacks slack j x)
    (globalKeyUnionFormula ks ι b) ↔ _
  rw [globalKeyUnionFormula, HalfspaceFormula.eval_anyFormulas]
  constructor
  · rintro ⟨A,hA,he⟩
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hA
    by_cases hb : (ks.get i).bump = b
    · have hi : x ∈ (globalKeyFormula ks ι i).region (globalBodySlacks slack) := by
        simpa only [if_pos hb, HalfspaceFormula.region, Set.mem_setOf_eq] using he
      rw [globalKeyFormula_region slack hkey] at hi
      exact ⟨ks.get i, ks.get_mem i, hb, hi⟩
    · change HalfspaceFormula.eval (fun j => 0 ≤ globalBodySlacks slack j x)
        (if (ks.get i).bump = b then globalKeyFormula ks ι i else .falsity) at he
      simp only [if_neg hb, HalfspaceFormula.eval] at he
  · rintro ⟨k,hk,hb,hx⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hk
    refine ⟨_, List.mem_map.mpr ⟨i, by simp, rfl⟩, ?_⟩
    have hi : x ∈ (globalKeyFormula ks ι i).region (globalBodySlacks slack) := by
      rw [globalKeyFormula_region slack hkey]
      exact hx
    simpa only [if_pos hb, HalfspaceFormula.region, Set.mem_setOf_eq] using hi

/-- A global finite Boolean formula describes the entire exact closed body. -/
theorem body_eq_closure_globalBodyFormula {d : ℕ} {ks : List (KeyData d)} {ι : Type*}
    [Fintype ι] (slack : Fin ks.length → ι → Point d → ℝ)
    (hkey : ∀ i x, x ∈ keySolid (ks.get i) ↔ ∀ j, 0 ≤ slack i j x) :
    body ks = closure ((globalBodyFormula ks ι).region (globalBodySlacks slack)) := by
  rw [globalBodyFormula, HalfspaceFormula.region_conj, HalfspaceFormula.region_disj,
    HalfspaceFormula.region_neg, HalfspaceFormula.region_relabel,
    globalKeyUnionFormula_region slack hkey true,
    globalKeyUnionFormula_region slack hkey false]
  change body ks = closure (((carrierHalfspaceFormula d).region carrierHalfspaceSlack ∪
    keyUnion ks true) ∩ (keyUnion ks false)ᶜ)
  rw [carrierHalfspaceFormula_region]
  rfl

theorem continuous_globalBodySlacks {d : ℕ} {ks : List (KeyData d)} {ι : Type*}
    (slack : Fin ks.length → ι → Point d → ℝ)
    (h : ∀ i j, Continuous (slack i j)) (j : GlobalBodyHalfspaceIndex ks ι) :
    Continuous (globalBodySlacks slack j) := by
  cases j with
  | inl j => exact continuous_carrierHalfspaceSlack j
  | inr ij => exact h ij.1 ij.2

namespace Canonical

noncomputable def chosenKeyPose5 (i : Fin keys5.length) : Contact.Pose 5 :=
  Classical.choose (everyKey5_isCanonical (keys5.get i) (keys5.get_mem i))
noncomputable def chosenKeyPose7 (i : Fin keys7.length) : Contact.Pose 7 :=
  Classical.choose (everyKey7_isCanonical (keys7.get i) (keys7.get_mem i))

theorem chosenKeyPose5_spec (i : Fin keys5.length) :
    keySolid (keys5.get i) = (chosenKeyPose5 i).euclidean '' referenceSolid5 :=
  Classical.choose_spec (everyKey5_isCanonical (keys5.get i) (keys5.get_mem i))
theorem chosenKeyPose7_spec (i : Fin keys7.length) :
    keySolid (keys7.get i) = (chosenKeyPose7 i).euclidean '' referenceSolid7 :=
  Classical.choose_spec (everyKey7_isCanonical (keys7.get i) (keys7.get_mem i))

noncomputable def globalKeySlacks5 (i : Fin keys5.length) := posedHalfspaceSlack5 (chosenKeyPose5 i)
noncomputable def globalKeySlacks7 (i : Fin keys7.length) := posedHalfspaceSlack7 (chosenKeyPose7 i)

end Canonical

open Canonical

noncomputable def T5GlobalSlacks := globalBodySlacks globalKeySlacks5
noncomputable def T7GlobalSlacks := globalBodySlacks globalKeySlacks7

theorem T5_global_halfspace_formula :
    T5 = closure ((globalBodyFormula keys5 (PyramidHalfspaceIndex 4)).region T5GlobalSlacks) :=
  body_eq_closure_globalBodyFormula globalKeySlacks5 fun i x =>
    mem_keySolid5_iff_posed_halfspaces (chosenKeyPose5 i) (chosenKeyPose5_spec i) x

theorem T7_global_halfspace_formula :
    T7 = closure ((globalBodyFormula keys7 (PyramidHalfspaceIndex 6)).region T7GlobalSlacks) :=
  body_eq_closure_globalBodyFormula globalKeySlacks7 fun i x =>
    mem_keySolid7_iff_posed_halfspaces (chosenKeyPose7 i) (chosenKeyPose7_spec i) x

theorem continuous_T5GlobalSlacks (j) : Continuous (T5GlobalSlacks j) :=
  continuous_globalBodySlacks globalKeySlacks5
    (fun i k => continuous_posedHalfspaceSlack5 (chosenKeyPose5 i) k) j

theorem continuous_T7GlobalSlacks (j) : Continuous (T7GlobalSlacks j) :=
  continuous_globalBodySlacks globalKeySlacks7
    (fun i k => continuous_posedHalfspaceSlack7 (chosenKeyPose7 i) k) j

#print axioms body_eq_closure_globalBodyFormula
#print axioms T5_global_halfspace_formula
#print axioms T7_global_halfspace_formula

end SparseMonotiles
