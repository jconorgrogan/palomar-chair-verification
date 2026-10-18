module

public import SpectreFinite.HexRegionGeometry

@[expose] public section


/-! Exact finite rectangular sets of native axial cells. These cardinality
and membership facts support the later quadratic-growth argument excluding
nontrivial quotients of the coarse axial graph. No graph freeness is assumed. -/
namespace SpectreFinite.HexSearch

def axialRectangle (q0 r0 : Int) (width height : Nat) : List Position :=
  (List.range width).flatMap fun (q : Nat) =>
    (List.range height).map fun (r : Nat) => (q0+(q:Int),r0+(r:Int))

theorem mem_axialRectangle_iff (q0 r0 : Int) (width height : Nat) (x : Position) :
    x ∈ axialRectangle q0 r0 width height ↔
    q0 ≤ x.1 ∧ x.1 < q0+(width:Int) ∧ r0 ≤ x.2 ∧ x.2 < r0+(height:Int) := by
  constructor
  · intro h
    obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp h
    obtain ⟨r,hr,he⟩ := List.mem_map.mp hr
    have hq' := List.mem_range.mp hq
    have hr' := List.mem_range.mp hr
    subst x
    dsimp
    omega
  · rintro ⟨hql,hqu,hrl,hru⟩
    apply List.mem_flatMap.mpr
    refine ⟨(x.1-q0).toNat,List.mem_range.mpr (by omega),?_⟩
    apply List.mem_map.mpr
    refine ⟨(x.2-r0).toNat,List.mem_range.mpr (by omega),?_⟩
    apply Prod.ext <;> dsimp <;> omega

theorem axialRectangle_length (q0 r0 : Int) (width height : Nat) :
    (axialRectangle q0 r0 width height).length = width*height := by
  simp [axialRectangle,List.length_flatMap,List.map_const',List.sum_replicate_nat]

theorem axialRectangle_nodup (q0 r0 : Int) (width height : Nat) :
    (axialRectangle q0 r0 width height).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro q hq
    apply List.Pairwise.map _ _ List.nodup_range
    intro r s hrs he
    have hh := congrArg Prod.snd he
    simp only at hh
    exact hrs (by omega)
  · apply List.Pairwise.imp _ List.nodup_range
    intro q p hqp x hx y hy he
    obtain ⟨r,hr,hre⟩ := List.mem_map.mp hx
    obtain ⟨s,hs,hse⟩ := List.mem_map.mp hy
    have hh := congrArg Prod.fst (hre.trans (he.trans hse.symm))
    simp only at hh
    exact hqp (by omega)

def positiveSquare (n : Nat) : List Position := axialRectangle 0 0 (n+1) (n+1)

theorem positiveSquare_length (n : Nat) : (positiveSquare n).length = (n+1)*(n+1) :=
  axialRectangle_length 0 0 (n+1) (n+1)

theorem positiveSquare_nodup (n : Nat) : (positiveSquare n).Nodup :=
  axialRectangle_nodup 0 0 (n+1) (n+1)

theorem positiveSquare_coordinates (n : Nat) (x : Position) (hx : x ∈ positiveSquare n) :
    0 ≤ x.1 ∧ x.1 ≤ (n:Int) ∧ 0 ≤ x.2 ∧ x.2 ≤ (n:Int) := by
  have h := (mem_axialRectangle_iff 0 0 (n+1) (n+1) x).mp hx
  omega

end SpectreFinite.HexSearch
