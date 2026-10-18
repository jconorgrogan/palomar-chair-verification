module

public import SpectreFinite.HexRotation

@[expose] public section


/-! Arithmetic geometry of arbitrary finite axial balls; no large bounded
truth table is needed for rotation invariance. -/
namespace SpectreFinite.HexSearch

theorem mem_hexRegion_iff (n : Nat) (x : Position) :
    x ∈ hexRegion n ↔
      -(n : Int) ≤ x.1 ∧ x.1 ≤ (n : Int) ∧
      -(n : Int) ≤ x.2 ∧ x.2 ≤ (n : Int) ∧
      -(n : Int) ≤ x.1+x.2 ∧ x.1+x.2 ≤ (n : Int) := by
  constructor
  · intro h
    obtain ⟨hm, hs⟩ := List.mem_filter.mp h
    have habs : (x.1+x.2).natAbs ≤ n := of_decide_eq_true hs
    obtain ⟨q, hq, hx⟩ := List.mem_flatMap.mp hm
    obtain ⟨r, hr, he⟩ := List.mem_map.mp hx
    have hq' := List.mem_range.mp hq
    have hr' := List.mem_range.mp hr
    subst x
    dsimp at habs ⊢
    omega
  · rintro ⟨hql,hqu,hrl,hru,hsl,hsu⟩
    apply List.mem_filter.mpr
    refine ⟨?_, decide_eq_true_eq.mpr (by omega)⟩
    apply List.mem_flatMap.mpr
    refine ⟨(x.1+(n:Int)).toNat, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    refine ⟨(x.2+(n:Int)).toNat, List.mem_range.mpr (by omega), ?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem hexRegion_rotation (n : Nat) : ∀ t : Fin 6, ∀ x ∈ hexRegion n,
    rotatePosition t x ∈ hexRegion n := by
  intro t x hx
  have h := (mem_hexRegion_iff n x).mp hx
  apply (mem_hexRegion_iff n _).mpr
  have hcase : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨
      t.val = 4 ∨ t.val = 5 := by omega
  rcases hcase with h0 | h1 | h2 | h3 | h4 | h5 <;>
    simp_all [rotatePosition] <;> omega

theorem hexRegion_mono {n m : Nat} (hn : n ≤ m) {x : Position}
    (hx : x ∈ hexRegion n) : x ∈ hexRegion m := by
  have h := (mem_hexRegion_iff n x).mp hx
  apply (mem_hexRegion_iff m x).mpr
  omega

theorem addPos_mem_hexRegion {n m : Nat} {x y : Position}
    (hx : x ∈ hexRegion n) (hy : y ∈ hexRegion m) :
    addPos x y ∈ hexRegion (n+m) := by
  have h := (mem_hexRegion_iff n x).mp hx
  have h' := (mem_hexRegion_iff m y).mp hy
  apply (mem_hexRegion_iff (n+m) _).mpr
  dsimp [addPos]
  omega

theorem subtraction_mem_hexRegion {n m : Nat} {x y : Position}
    (hx : x ∈ hexRegion n) (hy : y ∈ hexRegion m) :
    (x.1-y.1, x.2-y.2) ∈ hexRegion (n+m) := by
  have h := (mem_hexRegion_iff n x).mp hx
  have h' := (mem_hexRegion_iff m y).mp hy
  apply (mem_hexRegion_iff (n+m) _).mpr
  dsimp
  omega

end SpectreFinite.HexSearch
