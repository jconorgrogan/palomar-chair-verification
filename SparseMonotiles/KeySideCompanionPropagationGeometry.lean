module

public import SparseMonotiles.StripCreaseCrossingPyramid
public import SparseMonotiles.CanonicalRidgeRank
public import SparseMonotiles.GenericRidgePoints

@[expose] public section

/-! # Generic actual side-side creases for K2 propagation
The ridge, its codimension and the active-plane containment are conclusions.
The explicit strict crease seed is supplied separately by concrete geometry.
-/
namespace SparseMonotiles
open Set

theorem exists_generic_key_side_side_crease
    {n : ℕ} {κ : Type*} [Countable κ] (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ j b, 0 < keySideDistance k j b)
    (i j : Fin n) (hij : i ≠ j) (si sj : Bool) {p : Point (n+1)}
    (hi : keyPyramidHalfspaceSlack k (.inr (i,si)) p=0)
    (hj : keyPyramidHalfspaceSlack k (.inr (j,sj)) p=0)
    (ho : ∀ a : PyramidHalfspaceIndex n, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
      0 < keyPyramidHalfspaceSlack k a p)
    (H : κ → AffineSubspace ℝ (Point (n+1))) :
    ∃ y : Point (n+1), ∃ L : AffineSubspace ℝ (Point (n+1)),
      y ∈ keySolid k ∧ keyPyramidHalfspaceSlack k (.inr (i,si)) y=0 ∧
      keyPyramidHalfspaceSlack k (.inr (j,sj)) y=0 ∧
      (∀ a : PyramidHalfspaceIndex n, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
        0 < keyPyramidHalfspaceSlack k a y) ∧
      y ∈ L ∧ Module.finrank ℝ L.direction+2=n+1 ∧
      ∀ a, y ∈ H a → L ≤ H a := by
  classical
  let f : Fin 2 → PyramidFacetIndex n := ![some (i,si),some (j,sj)]
  let N : Fin 2 → Point (n+1) :=
    ![pyramidFacetSlopeNormal (keySideSlope k) (some (i,si)),
      pyramidFacetSlopeNormal (keySideSlope k) (some (j,sj))]
  let L := normalAffineIntersection N p
  have hpair : some (i,si) ≠ some (j,sj) := by
    intro h
    apply hij
    exact congrArg Prod.fst (Option.some.inj h)
  have hN : LinearIndependent ℝ N := pyramidFacetSlopeNormal_pair_linearIndependent
    (keySideSlope k) (fun a b => div_pos hh (hd a b)) _ _ hpair
  have hdim : Module.finrank ℝ L.direction+2=n+1 := by
    simpa only [Fintype.card_fin] using normalAffineIntersection_codimension N hN p
  have hpL : p ∈ L := (mem_normalAffineIntersection_iff N p p).mpr (fun _ => rfl)
  have hside : ∀ x ∈ L, keyPyramidHalfspaceSlack k (.inr (i,si)) x=0 ∧
      keyPyramidHalfspaceSlack k (.inr (j,sj)) x=0 := by
    intro x hx
    have hn := (mem_normalAffineIntersection_iff N p x).mp hx
    have heq (a : Fin 2) : keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex (f a)) x =
        keyPyramidHalfspaceNormal k (pyramidFacetHalfspaceIndex (f a)) p := by
      apply (key_facet_form_eq_iff_normal_inner_eq k hd (f a) x p).mpr
      have hna : N a = pyramidFacetSlopeNormal (keySideSlope k) (f a) := by fin_cases a <;> rfl
      simpa only [hna] using hn a
    have h0 := heq 0
    have h1 := heq 1
    change keyPyramidHalfspaceNormal k (.inr (i,si)) x = keyPyramidHalfspaceNormal k (.inr (i,si)) p at h0
    change keyPyramidHalfspaceNormal k (.inr (j,sj)) x = keyPyramidHalfspaceNormal k (.inr (j,sj)) p at h1
    constructor
    · simpa only [keyPyramidHalfspaceSlack,h0] using hi
    · simpa only [keyPyramidHalfspaceSlack,h1] using hj
  let J := {a : PyramidHalfspaceIndex n // a ≠ .inr (i,si) ∧ a ≠ .inr (j,sj)}
  let O : Set L := {x | ∀ a : J, 0 < keyPyramidHalfspaceSlack k a (x : Point (n+1))}
  have hO : IsOpen O := by
    change IsOpen {x : L | ∀ a : J, 0 < keyPyramidHalfspaceSlack k a (x : Point (n+1))}
    rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro a
    exact isOpen_lt continuous_const ((continuous_keyPyramidHalfspaceSlack k a).comp continuous_subtype_val)
  have hOne : O.Nonempty := ⟨⟨p,hpL⟩,fun a => ho a a.property.1 a.property.2⟩
  obtain ⟨y,hy,hgeneric⟩ := exists_genericRidgePoint_in_open L ⟨p,hpL⟩ H hO hOne
  have hys := hside y y.property
  have hyo : ∀ a : PyramidHalfspaceIndex n, a ≠ .inr (i,si) → a ≠ .inr (j,sj) →
      0 < keyPyramidHalfspaceSlack k a y := fun a hai haj => hy ⟨a,hai,haj⟩
  refine ⟨y,L,?_,hys.1,hys.2,hyo,y.property,hdim,hgeneric⟩
  apply (mem_keySolid_iff_nonneg_slacks k hc hr hh y).mpr
  intro a
  by_cases hai : a=.inr (i,si)
  · rw [hai,hys.1]
  by_cases haj : a=.inr (j,sj)
  · rw [haj,hys.2]
  exact (hyo a hai haj).le

/-- The graph joining differently indexed sides of a box pyramid is connected
as soon as there are two tangent axes. Opposite sides use one intermediate axis. -/
theorem side_companion_constant_of_distinct_axes {n : ℕ} (hn : 2 ≤ n)
    {α : Type*} (C : Fin n → Bool → α)
    (h : ∀ i j, i ≠ j → ∀ si sj, C i si = C j sj) :
    ∀ i j si sj, C i si = C j sj := by
  intro i j si sj
  by_cases hij : i=j
  · subst j
    obtain ⟨l,hl⟩ : ∃ l : Fin n, l ≠ i := by
      by_cases hi : i=⟨0,by omega⟩
      · refine ⟨⟨1,by omega⟩,?_⟩
        rw [hi]
        intro heq
        have := congrArg Fin.val heq
        norm_num at this
      · exact ⟨⟨0,by omega⟩,Ne.symm hi⟩
    exact (h i l hl.symm si false).trans (h l i hl false sj)
  · exact h i j hij si sj

#print axioms exists_generic_key_side_side_crease
#print axioms side_companion_constant_of_distinct_axes

end SparseMonotiles
