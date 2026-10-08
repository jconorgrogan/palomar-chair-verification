module

public import SparseMonotiles.StripCreaseCrossingPyramid
public import SparseMonotiles.GenericKeyRidgeActive

@[expose] public section

/-! # A pruned open crease is an actual two-active-equation key crease -/
namespace SparseMonotiles

/-- A relative-open pruned crease cannot contain the apex: at least one
other retained side equation vanishes at the apex. -/
theorem keySideBoundary_strict_point_ne_apex {n : ℕ} (hn : 2 ≤ n)
    (k : KeyData (n+1)) (i : Fin n) (a : PyramidSideBoundaryIndex i) {x : Point (n+1)}
    (hstrict : ∀ c : PyramidSideBoundaryIndex i, c ≠ a →
      0 < keyPyramidHalfspaceSlack k
        (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i c)) x) :
    x ≠ rationalPoint k.apex := by
  intro hx
  subst x
  cases a with
  | none =>
      letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨j,hji⟩ := exists_ne i
      have hh := hstrict (some (⟨j,hji⟩,false)) (by simp)
      exact (lt_irrefl (0 : ℝ)) (by simpa [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
        key_apex_side_slack_zero] using hh)
  | some a =>
      rcases a with ⟨j,b⟩
      have hne : (some (j,!b) : PyramidSideBoundaryIndex i) ≠ some (j,b) := by
        cases b <;> simp
      have hh := hstrict (some (j,!b)) hne
      exact (lt_irrefl (0 : ℝ)) (by simpa [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
        key_apex_side_slack_zero] using hh)

/-- Pruned-crease positivity implies strict positivity of every omitted full
H-representation equation, including upper height and the opposite selected
side. Thus the crossing supplies exactly the two active equations required
by the physical key-ridge theorem. -/
theorem keySideBoundary_full_other_slacks_pos {n : ℕ} (hn : 2 ≤ n)
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (i : Fin n) (b : Bool) (a : PyramidSideBoundaryIndex i) {x : Point (n+1)}
    (hsolid : x ∈ keySolid k)
    (hselected : keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0)
    (hstrict : ∀ c : PyramidSideBoundaryIndex i, c ≠ a →
      0 < keyPyramidHalfspaceSlack k
        (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i c)) x) :
    ∀ j : PyramidHalfspaceIndex n, j ≠ .inr (i,b) →
      j ≠ pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a) →
      0 < keyPyramidHalfspaceSlack k j x := by
  have hheight := key_height_lt_of_ne_apex k hc hr hh hsolid
    (keySideBoundary_strict_point_ne_apex hn k i a hstrict)
  have hgap : 0 < (keyPyramidHeight k-x (Fin.last n))*(keyPyramidHi k i-keyPyramidLo k i) :=
    mul_pos (sub_pos.mpr hheight) (sub_pos.mpr (hw i))
  intro j hjs hja
  rcases j with c | ⟨j,c⟩
  · cases c
    · apply hstrict none
      intro ha
      apply hja
      rw [← ha]
      rfl
    · change 0 < keyPyramidHeight k-x (Fin.last n)
      exact sub_pos.mpr hheight
  · by_cases hji : j = i
    · subst j
      cases b <;> cases c
      all_goals try exact (hjs rfl).elim
      all_goals
        change _ - _ = 0 at hselected
        change 0 < _ - _
        dsimp [keyPyramidHalfspaceBound,keyPyramidHalfspaceNormal,pyramidHalfspaceBound,
          pyramidHalfspaceNormal] at hselected ⊢
        nlinarith only [hselected,hgap]
    · apply hstrict (some (⟨j,hji⟩,c))
      intro ha
      apply hja
      rw [← ha]
      rfl

/-- Every retained boundary facet makes a genuine base-side or distinct-axis
side-side pair with the selected side. -/
theorem pyramidSideBoundary_is_genuine_ridge_pair {n : ℕ}
    (i : Fin n) (b : Bool) (a : PyramidSideBoundaryIndex i) :
    IsPyramidRidgePair (some (i,b)) (pyramidSideBoundaryFacet i a) := by
  cases a with
  | none => trivial
  | some a => exact Ne.symm a.1.property

#print axioms keySideBoundary_strict_point_ne_apex
#print axioms keySideBoundary_full_other_slacks_pos
#print axioms pyramidSideBoundary_is_genuine_ridge_pair
end SparseMonotiles
