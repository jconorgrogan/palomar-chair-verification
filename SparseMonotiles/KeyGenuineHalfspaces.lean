module

public import SparseMonotiles.KeySlackNormals

@[expose] public section

/-! # Actual key solids using only genuine facet planes
The redundant upper-height inequality follows from one opposite tangent pair
with positive width. This removes it before matching supporting-plane families.
-/
namespace SparseMonotiles
open Set

theorem mem_keySolid_iff_genuine_facet_slacks {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (i₀ : Fin n)
    (hwidth : keyPyramidLo k i₀ < keyPyramidHi k i₀) (x : Point (n+1)) :
    x ∈ keySolid k ↔ ∀ a : PyramidFacetIndex n,
      0 ≤ keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) x := by
  constructor
  · intro hx a
    exact (mem_keySolid_iff_nonneg_slacks k hc hr hh x).mp hx _
  · intro hx
    have hlo := hx (some (i₀,false))
    have hhi := hx (some (i₀,true))
    simp only [pyramidFacetHalfspaceIndex, keyPyramidHalfspaceSlack,
      keyPyramidHalfspaceBound, pyramidHalfspaceBound, keyPyramidHalfspaceNormal_apply] at hlo hhi
    have htop : x (Fin.last n) ≤ keyPyramidHeight k := by
      by_contra h
      have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (sub_pos.mpr hwidth)
      nlinarith
    apply (mem_keySolid_iff_nonneg_slacks k hc hr hh x).mpr
    intro j
    rcases j with b | u
    · cases b
      · exact hx none
      · change 0 ≤ keyPyramidHeight k - x (Fin.last n)
        exact sub_nonneg.mpr htop
    · exact hx (some u)

theorem keySolid_eq_genuine_facet_halfspaces {n : ℕ}
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (i₀ : Fin n)
    (hwidth : keyPyramidLo k i₀ < keyPyramidHi k i₀) :
    keySolid k = {x | ∀ a : PyramidFacetIndex n,
      0 ≤ keyPyramidHalfspaceSlack k (pyramidFacetHalfspaceIndex a) x} := by
  ext x
  exact mem_keySolid_iff_genuine_facet_slacks k hc hr hh i₀ hwidth x

#print axioms keySolid_eq_genuine_facet_halfspaces
end SparseMonotiles
