module

public import SparseMonotiles.LocalBoundaryPlanes
public import SparseMonotiles.CarrierHalfspaceFormula
public import SparseMonotiles.ReferenceKeyHalfspaces
public import SparseMonotiles.CanonicalBindings5
public import SparseMonotiles.CanonicalBindings7

@[expose] public section

/-! Carrier boundary planes and the global key-or-carrier boundary dichotomy.
This retains actual plane indices without assuming registration or genericity. -/
namespace SparseMonotiles
open Set Filter Canonical
open scoped Topology Classical

theorem frontier_carrier_subset_zero {d : ℕ} :
    frontier (carrier d) ⊆ {x | ∃ j : CarrierHalfspaceIndex d, carrierHalfspaceSlack j x=0} := by
  have h := frontier_closed_truth_region_subset_zero carrierHalfspaceSlack
    (fun j : CarrierHalfspaceIndex d => continuous_carrierHalfspaceSlack j)
    (fun v => (carrierHalfspaceFormula d).eval v)
  change frontier (closure ((carrierHalfspaceFormula d).region carrierHalfspaceSlack)) ⊆ _ at h
  rw [carrierHalfspaceFormula_region,(carrier_isClosed d).closure_eq] at h
  exact h

theorem card_active_carrier_fields_le {d : ℕ} (p : Point d) :
    (Finset.univ.filter (fun j : CarrierHalfspaceIndex d => carrierHalfspaceSlack j p=0)).card ≤ d := by
  let active := Finset.univ.filter (fun j : CarrierHalfspaceIndex d => carrierHalfspaceSlack j p=0)
  have hinj : Set.InjOn Prod.fst (active : Set (CarrierHalfspaceIndex d)) := by
    rintro ⟨i,s⟩ hi ⟨j,t⟩ hj hij
    change i=j at hij
    subst j
    have hs : carrierHalfspaceSlack (i,s) p=0 := (Finset.mem_filter.mp hi).2
    have ht : carrierHalfspaceSlack (i,t) p=0 := (Finset.mem_filter.mp hj).2
    fin_cases s <;> fin_cases t <;> simp [carrierHalfspaceSlack] at hs ht ⊢ <;> linarith
  have h := Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_univ _ ) hinj
  simpa using h

/-- At most one active carrier level occurs per coordinate. -/
theorem carrier_local_boundary_plane_cover {d : ℕ} (p : Point d) {T : Set (Point d)}
    (hT : LocalSetEq p T (carrier d)) : HasLocalBoundaryPlaneCover T p d := by
  have hlocal : LocalSetEq p T
      (closure {x | (carrierHalfspaceFormula d).eval (fun j => 0 ≤ carrierHalfspaceSlack j x)}) := by
    change LocalSetEq p T (closure ((carrierHalfspaceFormula d).region carrierHalfspaceSlack))
    rw [carrierHalfspaceFormula_region,(carrier_isClosed d).closure_eq]
    exact hT
  have hcover : ∀ᶠ x in 𝓝 p, x ∈ frontier T →
      ∃ j : CarrierHalfspaceIndex d, carrierHalfspaceSlack j p=0 ∧ carrierHalfspaceSlack j x=0 := by
    filter_upwards [hlocal.frontier,eventually_frontier_closed_truth_region_active carrierHalfspaceSlack
      (fun j : CarrierHalfspaceIndex d => continuous_carrierHalfspaceSlack j)
      (fun v => (carrierHalfspaceFormula d).eval v) p] with x hx hc hp
    exact hc (hx.mp hp)
  apply localBoundaryPlaneCover_of_finite_active_fields p d carrierHalfspaceSlack
    (fun j => EuclideanSpace.single j.1 1) ?_ (card_active_carrier_fields_le p) ?_ hcover
  · intro j h
    have hh := congrArg (fun x : Point d => x j.1) h
    simpa [EuclideanSpace.single_apply] using hh
  · rintro ⟨i,j⟩ hp x
    fin_cases j <;> simp [carrierHalfspaceSlack,EuclideanSpace.inner_single_left] at hp ⊢ <;>
      constructor <;> intro h <;> linarith

/-- Outside all closed literal keys, physical boundary comes from an actual
carrier coordinate plane. No local support-selection hypothesis is needed. -/
theorem frontier_body_key_or_carrier_plane {d : ℕ} (ks : List (KeyData d))
    (hclosed : ∀ k ∈ ks, IsClosed (keySolid k)) {p : Point d} (hp : p ∈ frontier (body ks)) :
    (∃ k ∈ ks, p ∈ keySolid k) ∨ (∃ j : CarrierHalfspaceIndex d, carrierHalfspaceSlack j p=0) := by
  by_cases hk : ∃ k ∈ ks, p ∈ keySolid k
  · exact Or.inl hk
  · right
    have haway := away_keys_of_closed_supports keySolid (fun _ _ => Subset.rfl) hclosed
      (fun k hkm hpk => hk ⟨k,hkm,hpk⟩)
    have hcar := localSetEq_body_carrier_away_keys haway
    exact frontier_carrier_subset_zero (hcar.frontier.mem_iff.mp hp)

theorem keySolid_isClosed_of_canonical {n : ℕ} (k r : KeyData (n+1))
    (hc : r.centre (Fin.last n)=0) (hr : r.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight r) (q : Contact.Pose (n+1))
    (hq : keySolid k=q.euclidean '' keySolid r) : IsClosed (keySolid k) := by
  have hclosed : IsClosed (keySolid r) := by
    rw [keySolid_eq_iInter_halfspaces r hc hr hh]
    exact isClosed_iInter (fun j => isClosed_le
      (keyPyramidHalfspaceNormal r j).continuous_of_finiteDimensional continuous_const)
  rw [hq]
  exact q.euclidean.toHomeomorph.isClosedMap _ hclosed

theorem T5_frontier_key_or_carrier_plane {p : Point 5} (hp : p ∈ frontier T5) :
    (∃ k ∈ keys5, p ∈ keySolid k) ∨
      (∃ j : CarrierHalfspaceIndex 5, carrierHalfspaceSlack j p=0) := by
  apply frontier_body_key_or_carrier_plane keys5 ?_ hp
  intro k hk
  obtain ⟨q,hq⟩ := everyKey5_isCanonical k hk
  exact keySolid_isClosed_of_canonical k ((referenceBox5 true).toKeyData 19200)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by change (0 : ℝ) < (((referenceBox5 true).toKeyData 19200).apex 4 : ℝ)
        exact_mod_cast referenceBox5_height_pos true) q hq

theorem T7_frontier_key_or_carrier_plane {p : Point 7} (hp : p ∈ frontier T7) :
    (∃ k ∈ keys7, p ∈ keySolid k) ∨
      (∃ j : CarrierHalfspaceIndex 7, carrierHalfspaceSlack j p=0) := by
  apply frontier_body_key_or_carrier_plane keys7 ?_ hp
  intro k hk
  obtain ⟨q,hq⟩ := everyKey7_isCanonical k hk
  exact keySolid_isClosed_of_canonical k ((referenceBox7 true).toKeyData 188160)
    (by simp [Fin.last]) (by simp [Fin.last])
    (by change (0 : ℝ) < (((referenceBox7 true).toKeyData 188160).apex 6 : ℝ)
        exact_mod_cast referenceBox7_height_pos true) q hq

#print axioms carrier_local_boundary_plane_cover
#print axioms T5_frontier_key_or_carrier_plane
#print axioms T7_frontier_key_or_carrier_plane
end SparseMonotiles
