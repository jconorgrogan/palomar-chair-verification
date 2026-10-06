module

public import SparseMonotiles.LocalBoundaryPlanes
public import SparseMonotiles.KeyGenuineHalfspaces
public import SparseMonotiles.TwoPlaneWedgeModels

@[expose] public section

/-! Near the actual key apex, the only boundary planes are the genuine side
planes. The redundant upper-height equation is removed by an opposite-side
pair before taking the closed dent material boundary. -/
namespace SparseMonotiles
open Set Filter
open scoped Topology Classical

theorem nonbase_key_halfspaces_eq_sides {n : ℕ} (k : KeyData (n+1))
    (i₀ : Fin n) (hw : keyPyramidLo k i₀ < keyPyramidHi k i₀)
    (e : Point (n+1) → Point (n+1)) :
    nonbaseHalfspaces (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) =
      {x | ∀ a : Fin n × Bool, 0 ≤ keyPyramidHalfspaceSlack k (.inr a) (e x)} := by
  ext x
  constructor
  · intro hx a
    exact hx (.inr a) (by simp)
  · intro hx j hj
    have hlo := hx (i₀,false)
    have hhi := hx (i₀,true)
    simp only [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
      keyPyramidHalfspaceNormal_apply] at hlo hhi
    have ht : e x (Fin.last n) ≤ keyPyramidHeight k := by
      by_contra h
      have hm := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sub_pos.mpr hw)
      nlinarith
    rcases j with b | a
    · cases b
      · exact (hj rfl).elim
      · change 0 ≤ keyPyramidHeight k-e x (Fin.last n)
        exact sub_nonneg.mpr ht
    · exact hx a

theorem localSetEq_merged_positive_base_sides {n : ℕ} (k : KeyData (n+1))
    (i₀ : Fin n) (hw : keyPyramidLo k i₀ < keyPyramidHi k i₀)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (b : Bool) {p : Point (n+1)}
    (hbase : 0 < keyPyramidHalfspaceSlack k (.inl false) (e p)) :
    LocalSetEq p (mergedKeyRegion (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) b)
      {x | (if b then (fun v : (Fin n × Bool) → Prop => ∀ a, v a)
        else (fun v : (Fin n × Bool) → Prop => ¬ ∀ a, v a))
        (fun a => 0 ≤ keyPyramidHalfspaceSlack k (.inr a) (e x))} := by
  have hnb := nonbase_key_halfspaces_eq_sides k i₀ hw e
  have hf : Continuous (fun x => keyPyramidHalfspaceSlack k (.inl false) (e x)) :=
    (continuous_keyPyramidHalfspaceSlack k _).comp e.continuous
  filter_upwards [hf.continuousAt.eventually (Ioi_mem_nhds hbase)] with x hx
  rw [keyPyramidHalfspaceSlack_base] at hx
  cases b <;> simp [mergedKeyRegion,hnb,hx.le,not_le.mpr hx]

/-- The actual body's local frontier near the apex is covered by the indexed
2n side planes, for either bump/dent orientation. -/
theorem key_apex_eventually_frontier_side_planes {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (i₀ : Fin n)
    (hw : keyPyramidLo k i₀ < keyPyramidHi k i₀)
    (e : Point (n+1) ≃ᵃⁱ[ℝ] Point (n+1)) (b : Bool)
    {p : Point (n+1)} {T : Set (Point (n+1))}
    (ha : e p = rationalPoint k.apex)
    (hT : LocalSetEq p T (closure (mergedKeyRegion
      (fun j x => keyPyramidHalfspaceSlack k j (e x)) (.inl false) b))) :
    ∀ᶠ x in 𝓝 p, x ∈ frontier T →
      ∃ i : Fin n, ∃ c : Bool, keyPyramidHalfspaceSlack k (.inr (i,c)) (e x)=0 := by
  have hbase : 0 < keyPyramidHalfspaceSlack k (.inl false) (e p) := by
    rw [ha,keyPyramidHalfspaceSlack_base]
    exact hh
  have hl := hT.trans (localSetEq_merged_positive_base_sides k i₀ hw e b hbase).closure
  have hcover := eventually_frontier_closed_truth_region_active
    (fun a : Fin n × Bool => fun x => keyPyramidHalfspaceSlack k (.inr a) (e x))
    (fun a => (continuous_keyPyramidHalfspaceSlack k _).comp e.continuous)
    (if b then (fun v : (Fin n × Bool) → Prop => ∀ a, v a)
      else (fun v : (Fin n × Bool) → Prop => ¬ ∀ a, v a)) p
  filter_upwards [hl.frontier,hcover] with x hx hc hfront
  obtain ⟨a,_,ha⟩ := hc (hx.mp hfront)
  exact ⟨a.1,a.2,ha⟩

#print axioms key_apex_eventually_frontier_side_planes
end SparseMonotiles
