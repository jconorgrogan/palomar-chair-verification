module

public import SparseMonotiles.Model
public import SparseMonotiles.PolyhedralGerms

@[expose] public section

/-!
# Exact local reduction of the finite-key body

This file is an interface for, not a proof of, the concrete boundary inventory.
It works directly with `Model.body`, including the final closure. An explicit
isolation neighborhood removes all keys except one, or all keys; a separate
carrier germ and key germ then give the corresponding Boolean local model.

Isolation can be supplied by finite closed supports, or by an interior point
of a support disjoint from every other support. No support separation, carrier
halfspace description, regularity of a dent difference, or literal-key binding
is silently assumed. In particular the closure of a dent difference is retained.
-/

namespace SparseMonotiles

open Set Filter
open scoped Topology

section LocalTopology

variable {X : Type*} [TopologicalSpace X]

/-- Interior, like closure, depends only on the germ of a set. -/
theorem LocalSetEq.interior {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    LocalSetEq p (interior s) (interior t) := by
  simpa only [closure_compl, compl_compl] using h.compl.closure.compl

/-- An exact material germ gives the exact boundary germ. -/
theorem LocalSetEq.frontier {p : X} {s t : Set X} (h : LocalSetEq p s t) :
    LocalSetEq p (frontier s) (frontier t) := by
  simpa only [frontier_eq_closure_inter_closure] using h.closure.inter h.compl.closure

/-- Closing a union-minus-dents construction commutes with local replacement. -/
theorem localSetEq_closed_modification {p : X} {C C' B B' D D' : Set X}
    (hC : LocalSetEq p C C') (hB : LocalSetEq p B B')
    (hD : LocalSetEq p D D') :
    LocalSetEq p (closure ((C ∪ B) \ D)) (closure ((C' ∪ B') \ D')) :=
  ((hC.union hB).diff hD).closure

/-- The preclosure local model for one signed key. -/
def keyReplacement (C K : Set X) (b : Bool) : Set X :=
  if b then C ∪ K else C \ K

/-- The carrier and the selected key can be replaced by any proved local models. -/
theorem LocalSetEq.keyReplacement {p : X} {C C' K K' : Set X}
    (hC : LocalSetEq p C C') (hK : LocalSetEq p K K') (b : Bool) :
    LocalSetEq p (SparseMonotiles.keyReplacement C K b)
      (SparseMonotiles.keyReplacement C' K' b) := by
  cases b
  · exact hC.diff hK
  · exact hC.union hK

/-- Finitely many closed forbidden supports missing `p` miss a common neighborhood.
The predicate `P` explicitly specifies which supports are to be excluded. -/
theorem eventually_avoids_closed_list {ι : Type*} (ks : List ι)
    (support : ι → Set X) (P : ι → Prop) (p : X)
    (hclosed : ∀ k ∈ ks, P k → IsClosed (support k))
    (havoid : ∀ k ∈ ks, P k → p ∉ support k) :
    ∀ᶠ x in 𝓝 p, ∀ k ∈ ks, P k → x ∉ support k := by
  induction ks with
  | nil => exact Eventually.of_forall (by simp)
  | cons k ks ih =>
      have hk : ∀ᶠ x in 𝓝 p, P k → x ∉ support k := by
        by_cases hP : P k
        · exact Filter.Eventually.mono ((hclosed k (by simp) hP).isOpen_compl.mem_nhds
            (havoid k (by simp) hP)) fun _ hx _ => hx
        · exact Eventually.of_forall fun _ h => (hP h).elim
      have hks := ih
        (fun j hj => hclosed j (List.mem_cons_of_mem k hj))
        (fun j hj => havoid j (List.mem_cons_of_mem k hj))
      apply (hk.and hks).mono
      intro x hx j hj hP
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hx.1 hP
      · exact hx.2 j hj hP

end LocalTopology

/-- The exact finite union of closed carrier cells is closed, in every dimension. -/
theorem carrier_isClosed (d : ℕ) : IsClosed (carrier d) := by
  have hcoord (i : Fin d) : Continuous (fun x : Point d => x i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
  have hcarrier : carrier d = ⋃ c : Fin d → Bool,
      ({x : Point d | ∃ i, c i = false} ∩
        ⋂ i : Fin d, {x : Point d |
          (if c i then (1 : ℝ) else 0) ≤ x i ∧
          x i ≤ (if c i then (1 : ℝ) else 0) + 1}) := by
    ext x
    simp only [carrier, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter]
  rw [hcarrier]
  apply isClosed_iUnion_of_finite
  intro c
  apply isClosed_const.inter
  apply isClosed_iInter
  intro i
  exact (isClosed_le continuous_const (hcoord i)).inter
    (isClosed_le (hcoord i) continuous_const)

section LiteralBody

variable {d : ℕ} {ks : List (KeyData d)} {k : KeyData d} {p : Point d}

/-- In a neighborhood excluding every other key, each sign-union has only the
selected key, and only when its sign is the requested sign. -/
theorem localSetEq_keyUnion_isolated (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j) (b : Bool) :
    LocalSetEq p (keyUnion ks b) (if k.bump = b then keySolid k else ∅) := by
  classical
  apply hiso.mono
  intro x hx
  by_cases hb : k.bump = b
  · simp only [if_pos hb]
    constructor
    · rintro ⟨j, hj, hjb, hxj⟩
      have hjk : j = k := by
        by_contra hne
        exact hx j hj hne hxj
      simpa only [hjk] using hxj
    · intro hxk
      exact ⟨k, hk, hb, hxk⟩
  · simp only [if_neg hb, Set.mem_empty_iff_false, iff_false]
    rintro ⟨j, hj, hjb, hxj⟩
    by_cases hjk : j = k
    · exact hb (hjk ▸ hjb)
    · exact hx j hj hjk hxj

/-- If all key solids are absent on a neighborhood, both sign-unions vanish there. -/
theorem localSetEq_keyUnion_empty
    (haway : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j) (b : Bool) :
    LocalSetEq p (keyUnion ks b) ∅ := by
  apply haway.mono
  intro x hx
  change (∃ j ∈ ks, j.bump = b ∧ x ∈ keySolid j) ↔ False
  constructor
  · rintro ⟨j, hj, _, hxj⟩
    exact hx j hj hxj
  · exact False.elim

/-- Exact isolated-key reduction of the literal model, with closure retained. -/
theorem localSetEq_body_isolated_key (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j) :
    LocalSetEq p (body ks)
      (closure (keyReplacement (carrier d) (keySolid k) k.bump)) := by
  have h := localSetEq_closed_modification (LocalSetEq.refl p (carrier d))
    (localSetEq_keyUnion_isolated hk hiso true)
    (localSetEq_keyUnion_isolated hk hiso false)
  cases hb : k.bump <;> simpa only [body, keyReplacement, hb, Bool.false_eq_true,
    Bool.true_eq_false, if_false, if_true, Set.union_empty, Set.diff_empty] using h

/-- Bumps replace the carrier germ by the carrier/key union. -/
theorem localSetEq_body_isolated_bump (hk : k ∈ ks) (hb : k.bump = true)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j) :
    LocalSetEq p (body ks) (closure (carrier d ∪ keySolid k)) := by
  simpa only [keyReplacement, hb, if_true] using localSetEq_body_isolated_key hk hiso

/-- Dents replace the carrier germ by the closed carrier/key difference.
This statement does not replace that closure by `carrier \ interior keySolid`. -/
theorem localSetEq_body_isolated_dent (hk : k ∈ ks) (hb : k.bump = false)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j) :
    LocalSetEq p (body ks) (closure (carrier d \ keySolid k)) := by
  simpa only [keyReplacement, hb, Bool.false_eq_true, if_false] using
    localSetEq_body_isolated_key hk hiso

/-- Away from all keys the body has precisely the closed-carrier germ. -/
theorem localSetEq_body_away_keys
    (haway : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j) :
    LocalSetEq p (body ks) (closure (carrier d)) := by
  simpa only [body, Set.union_empty, Set.diff_empty] using
    localSetEq_closed_modification (LocalSetEq.refl p (carrier d))
      (localSetEq_keyUnion_empty haway true) (localSetEq_keyUnion_empty haway false)

/-- Away from all keys the exact body and exact carrier agree locally. -/
theorem localSetEq_body_carrier_away_keys
    (haway : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j) :
    LocalSetEq p (body ks) (carrier d) := by
  simpa only [(carrier_isClosed d).closure_eq] using localSetEq_body_away_keys haway

/-- The carrier model may be a halfspace, a wedge, or any other proved germ. -/
theorem localSetEq_body_isolated_models {C K : Set (Point d)} (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j)
    (hC : LocalSetEq p (carrier d) C) (hK : LocalSetEq p (keySolid k) K) :
    LocalSetEq p (body ks) (closure (keyReplacement C K k.bump)) :=
  (localSetEq_body_isolated_key hk hiso).trans ((hC.keyReplacement hK k.bump).closure)

/-- A closed local carrier model eliminates the final closure away from keys. -/
theorem localSetEq_body_away_keys_model {C : Set (Point d)}
    (haway : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j)
    (hC : LocalSetEq p (carrier d) C) (hclosed : IsClosed C) :
    LocalSetEq p (body ks) C := by
  simpa only [hclosed.closure_eq] using (localSetEq_body_away_keys haway).trans hC.closure

/-- Finite closed support exclusion supplies the isolated-key premise.
Only supports for keys other than the selected key need be closed. -/
theorem key_isolation_of_closed_supports (support : KeyData d → Set (Point d))
    (hcover : ∀ j ∈ ks, keySolid j ⊆ support j)
    (hclosed : ∀ j ∈ ks, j ≠ k → IsClosed (support j))
    (havoid : ∀ j ∈ ks, j ≠ k → p ∉ support j) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j :=
  (eventually_avoids_closed_list ks support (fun j => j ≠ k) p hclosed havoid).mono
    fun _ hx j hj hne hxj => hx j hj hne (hcover j hj hxj)

/-- Pairwise support disjointness is sufficient at a point in the selected support.
Closedness of the other supports is essential to get a neighborhood. -/
theorem key_isolation_of_disjoint_closed_supports
    (support : KeyData d → Set (Point d))
    (hcover : ∀ j ∈ ks, keySolid j ⊆ support j)
    (hclosed : ∀ j ∈ ks, j ≠ k → IsClosed (support j))
    (hdisjoint : ∀ j ∈ ks, j ≠ k → Disjoint (support k) (support j))
    (hp : p ∈ support k) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j := by
  apply key_isolation_of_closed_supports support hcover hclosed
  intro j hj hne hpj
  exact Set.disjoint_left.mp (hdisjoint j hj hne) hp hpj

/-- Alternatively, an interior point of the selected support gives isolation
without closedness assumptions on any support. -/
theorem key_isolation_of_support_interior
    (support : KeyData d → Set (Point d))
    (hcover : ∀ j ∈ ks, keySolid j ⊆ support j)
    (hdisjoint : ∀ j ∈ ks, j ≠ k → Disjoint (support k) (support j))
    (hp : p ∈ interior (support k)) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j := by
  apply Filter.Eventually.mono (mem_interior_iff_mem_nhds.mp hp)
  intro x hx j hj hne hxj
  exact Set.disjoint_left.mp (hdisjoint j hj hne) hx (hcover j hj hxj)

/-- A point outside every closed support has a key-free neighborhood. -/
theorem away_keys_of_closed_supports (support : KeyData d → Set (Point d))
    (hcover : ∀ j ∈ ks, keySolid j ⊆ support j)
    (hclosed : ∀ j ∈ ks, IsClosed (support j))
    (havoid : ∀ j ∈ ks, p ∉ support j) :
    ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, x ∉ keySolid j := by
  have h := eventually_avoids_closed_list ks support (fun _ => True) p
    (fun j hj _ => hclosed j hj) (fun j hj _ => havoid j hj)
  exact h.mono fun _ hx j hj hxj => hx j hj trivial (hcover j hj hxj)

end LiteralBody

section BooleanModels

variable {X ι : Type*}

/-- Boolean counterpart of the signed single-key replacement. -/
def keyReplacementFormula (C K : HalfspaceFormula ι) (b : Bool) : HalfspaceFormula ι :=
  if b then .disj C K else .conj C (.neg K)

/-- No geometric hypothesis is used in translating a signed replacement to syntax. -/
theorem region_keyReplacementFormula (f : ι → X → ℝ) (C K : HalfspaceFormula ι)
    (b : Bool) :
    (keyReplacementFormula C K b).region f =
      keyReplacement (C.region f) (K.region f) b := by
  cases b <;> rfl

/-- The literal body reduces to the exact closed Boolean formula for a halfspace
(or any supplied carrier formula) and the isolated key. -/
theorem localSetEq_body_isolated_formula {d : ℕ} {ks : List (KeyData d)}
    {k : KeyData d} {p : Point d} (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j)
    (f : ι → Point d → ℝ) (C K : HalfspaceFormula ι)
    (hC : LocalSetEq p (carrier d) (C.region f))
    (hK : LocalSetEq p (keySolid k) (K.region f)) :
    LocalSetEq p (body ks) (closure ((keyReplacementFormula C K k.bump).region f)) := by
  rw [region_keyReplacementFormula]
  exact localSetEq_body_isolated_models hk hiso hC hK

/-- Finite continuous halfspace models can additionally freeze every inactive atom.
The supplied carrier formula may be one atom, or a multi-atom carrier wedge. -/
theorem localSetEq_body_isolated_frozen_formula [Finite ι]
    {d : ℕ} {ks : List (KeyData d)} {k : KeyData d} {p : Point d} (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j)
    (f : ι → Point d → ℝ) (hf : ∀ i, ContinuousAt (f i) p)
    (C K : HalfspaceFormula ι)
    (hC : LocalSetEq p (carrier d) (C.region f))
    (hK : LocalSetEq p (keySolid k) (K.region f)) :
    LocalSetEq p (body ks)
      (closure (((keyReplacementFormula C K k.bump).freeze f p).region f)) :=
  (localSetEq_body_isolated_formula hk hiso f C K hC hK).trans
    ((keyReplacementFormula C K k.bump).localSetEq_closure_freeze f p hf)

/-- The frozen Boolean model describes the physical boundary germ as well. -/
theorem localSetEq_frontier_body_isolated_frozen_formula [Finite ι]
    {d : ℕ} {ks : List (KeyData d)} {k : KeyData d} {p : Point d} (hk : k ∈ ks)
    (hiso : ∀ᶠ x in 𝓝 p, ∀ j ∈ ks, j ≠ k → x ∉ keySolid j)
    (f : ι → Point d → ℝ) (hf : ∀ i, ContinuousAt (f i) p)
    (C K : HalfspaceFormula ι)
    (hC : LocalSetEq p (carrier d) (C.region f))
    (hK : LocalSetEq p (keySolid k) (K.region f)) :
    LocalSetEq p (frontier (body ks))
      (frontier (closure (((keyReplacementFormula C K k.bump).freeze f p).region f))) :=
  (localSetEq_body_isolated_frozen_formula hk hiso f hf C K hC hK).frontier

end BooleanModels

#print axioms carrier_isClosed
#print axioms localSetEq_body_carrier_away_keys
#print axioms LocalSetEq.interior
#print axioms LocalSetEq.frontier
#print axioms localSetEq_body_isolated_key
#print axioms localSetEq_body_away_keys
#print axioms localSetEq_body_isolated_models
#print axioms key_isolation_of_disjoint_closed_supports
#print axioms key_isolation_of_support_interior
#print axioms away_keys_of_closed_supports
#print axioms localSetEq_body_isolated_formula
#print axioms localSetEq_body_isolated_frozen_formula
#print axioms localSetEq_frontier_body_isolated_frozen_formula

end SparseMonotiles
