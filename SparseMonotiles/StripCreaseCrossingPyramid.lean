module

public import SparseMonotiles.CanonicalRidgeRank
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-!
# Pruned actual side-face inequalities

On a selected side plane, retain the base and both planes for every other
box axis. The omitted opposite plane and upper-height inequality are derived.
This prevents duplicate apical equations from becoming false rank premises.
-/
namespace SparseMonotiles
open Set

/-- Boundary facets of the selected side face: its base and all other axes. -/
abbrev PyramidSideBoundaryIndex {n : ℕ} (i : Fin n) :=
  Option ({j : Fin n // j ≠ i} × Bool)

def pyramidSideBoundaryFacet {n : ℕ} (i : Fin n) :
    PyramidSideBoundaryIndex i → PyramidFacetIndex n
  | none => none
  | some (j,b) => some (j.val,b)

/-- On one side plane the pruned inequalities already imply the full actual
pyramid. The height upper bound follows from any remaining positive-width
axis, rather than being retained as a duplicate apical equation. -/
theorem pyramidSidePlane_mem_halfspaces_iff_pruned {n : ℕ} (hn : 2 ≤ n)
    (lo hi o : Fin n → ℝ) {h : ℝ} (hwidth : ∀ j, lo j < hi j)
    (i : Fin n) (b : Bool) {p : PyramidPoint n}
    (hside : p ∈ pyramidFacetPlane lo hi o h (some (i,b))) :
    p ∈ pyramidHalfspaces lo hi o h ↔
      0 ≤ p.2 ∧ ∀ j, j ≠ i →
        (h-p.2)*lo j+p.2*o j ≤ h*p.1 j ∧
          h*p.1 j ≤ (h-p.2)*hi j+p.2*o j := by
  constructor
  · exact fun hp => ⟨hp.1,fun j _ => hp.2.2 j⟩
  · rintro ⟨hp0,hother⟩
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    obtain ⟨j,hji⟩ := exists_ne i
    have hpair := hother j hji
    have hheight : p.2 ≤ h := by
      have hw := hwidth j
      nlinarith [hpair.1,hpair.2]
    refine ⟨hp0,hheight,?_⟩
    intro j
    by_cases hji : j = i
    · subst j
      have hgap : 0 ≤ (h-p.2)*(hi i-lo i) :=
        mul_nonneg (sub_nonneg.mpr hheight) (sub_nonneg.mpr (hwidth i).le)
      cases b <;> change (h-p.2)*_+p.2*o i = h*p.1 i at hside <;>
        constructor <;> nlinarith
    · exact hother j hji

/-- The corresponding exact criterion for the Euclidean convex-hull key,
using only the pruned affine slacks on the selected side plane. -/
theorem keySidePlane_mem_solid_iff_pruned {n : ℕ} (hn : 2 ≤ n)
    (k : KeyData (n+1))
    (hc : k.centre (Fin.last n) = 0) (hr : k.radius (Fin.last n) = 0)
    (hh : 0 < keyPyramidHeight k) (hw : ∀ j, keyPyramidLo k j < keyPyramidHi k j)
    (i : Fin n) (b : Bool) {x : Point (n+1)}
    (hside : keyPyramidHalfspaceSlack k (.inr (i,b)) x = 0) :
    x ∈ keySolid k ↔ ∀ a : PyramidSideBoundaryIndex i,
      0 ≤ keyPyramidHalfspaceSlack k
        (pyramidFacetHalfspaceIndex (pyramidSideBoundaryFacet i a)) x := by
  have hplane : pointPyramidEquiv n x ∈ pyramidFacetPlane
      (keyPyramidLo k) (keyPyramidHi k) (keyPyramidApex k) (keyPyramidHeight k) (some (i,b)) := by
    rw [mem_pyramidFacetPlane_iff]
    exact (sub_eq_zero.mp hside).symm
  rw [mem_keySolid_iff_pyramidHalfspaces k hc hr hh,
    pyramidSidePlane_mem_halfspaces_iff_pruned hn _ _ _ hw i b hplane]
  constructor
  · rintro ⟨hp0,hother⟩ a
    cases a with
    | none => simpa [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
        keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,keyPyramidHalfspaceNormal,
        pyramidHalfspaceBound,pyramidHalfspaceNormal] using hp0
    | some a =>
        rcases a with ⟨⟨j,hji⟩,c⟩
        have hp := hother j hji
        simp only [pointPyramidEquiv_fst,pointPyramidEquiv_snd] at hp
        cases c <;>
          change 0 ≤ _ - _ <;>
          dsimp [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
            keyPyramidHalfspaceBound,keyPyramidHalfspaceNormal,pyramidHalfspaceBound,
            pyramidHalfspaceNormal] <;> nlinarith [hp.1,hp.2]
  · intro hs
    have hp0 := hs none
    have hp0' : 0 ≤ x (Fin.last n) := by
      simpa [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
        keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,keyPyramidHalfspaceNormal,
        pyramidHalfspaceBound,pyramidHalfspaceNormal] using hp0
    refine ⟨hp0',?_⟩
    intro j hji
    have hlo := hs (some (⟨j,hji⟩,false))
    have hhi := hs (some (⟨j,hji⟩,true))
    change 0 ≤ _ - _ at hlo hhi
    dsimp [pyramidSideBoundaryFacet,pyramidFacetHalfspaceIndex,
      keyPyramidHalfspaceBound,keyPyramidHalfspaceNormal,pyramidHalfspaceBound,
      pyramidHalfspaceNormal] at hlo hhi
    simp only [pointPyramidEquiv_fst,pointPyramidEquiv_snd] at hlo hhi ⊢
    constructor <;> nlinarith

/-- Two different genuine pyramid facet normals are independent. This also
includes the two opposite side normals on a common tangential axis. -/
theorem pyramidFacetSlopeNormal_pair_linearIndependent {n : ℕ}
    (s : Fin n → Bool → ℝ) (hs : ∀ i b, 0 < s i b)
    (a b : PyramidFacetIndex n) (hab : a ≠ b) :
    LinearIndependent ℝ ![pyramidFacetSlopeNormal s a,pyramidFacetSlopeNormal s b] := by
  by_cases hc : pyramidFacetCoordinate a ≠ pyramidFacetCoordinate b
  · have heq : (fun j : Fin 2 => pyramidFacetSlopeNormal s (![a,b] j)) =
        ![pyramidFacetSlopeNormal s a,pyramidFacetSlopeNormal s b] := by
      funext j; fin_cases j <;> rfl
    rw [← heq]
    apply pyramidFacetSlopeNormal_linearIndependent s (fun i b => ne_of_gt (hs i b)) ![a,b]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [Function.comp_def] at hij ⊢
    · exact (hc hij).elim
    · exact (hc hij.symm).elim
  · have hcoord := not_ne_iff.mp hc
    cases a with
    | none =>
        cases b with
        | none => exact (hab rfl).elim
        | some b => simp [pyramidFacetCoordinate] at hcoord
    | some a =>
        cases b with
        | none => simp [pyramidFacetCoordinate] at hcoord
        | some b =>
            rcases a with ⟨i,u⟩
            rcases b with ⟨j,v⟩
            have hij : i = j := by simpa [pyramidFacetCoordinate] using hcoord
            subst j
            have huv : u ≠ v := by intro h; exact hab (by rw [h])
            apply Fintype.linearIndependent_iff.mpr
            intro g hg
            have hgs : g 0 • pyramidFacetSlopeNormal s (some (i,u)) +
                g 1 • pyramidFacetSlopeNormal s (some (i,v)) = 0 := by
              simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using hg
            have hl : g 0+g 1 = 0 := by
              have hh := congrArg (fun z : Point (n+1) => z (Fin.last n)) hgs
              simpa [pyramidFacetSlopeNormal] using hh
            have hi : g 0*(if u then s i u else -s i u) +
                g 1*(if v then s i v else -s i v) = 0 := by
              have hh := congrArg (fun z : Point (n+1) => z i.castSucc) hgs
              simpa [pyramidFacetSlopeNormal] using hh
            have hg1 : g 1 = -g 0 := by linarith
            rw [hg1] at hi
            cases u <;> cases v
            all_goals try exact (huv rfl).elim
            all_goals
              simp only [Bool.false_eq_true,if_false,if_true] at hi
              have hm : g 0*(s i false+s i true) = 0 := by nlinarith only [hi]
              have h0 : g 0 = 0 := (mul_eq_zero.mp hm).resolve_right
                (ne_of_gt (add_pos (hs i false) (hs i true)))
              have h1 : g 1 = 0 := by linarith
              intro j
              fin_cases j <;> assumption

#print axioms pyramidSidePlane_mem_halfspaces_iff_pruned
#print axioms keySidePlane_mem_solid_iff_pruned
#print axioms pyramidFacetSlopeNormal_pair_linearIndependent
end SparseMonotiles
