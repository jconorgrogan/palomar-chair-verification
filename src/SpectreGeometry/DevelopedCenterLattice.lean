module

public import SpectreGeometry.QuadraticDevelopment
public import SpectreGeometry.DeformedLatticeCertificate

@[expose] public section


namespace SpectreGeometry
noncomputable section

def kiteCenterMap : (ℤ × ℤ) →+ (ℚ × ℚ) where
  toFun p := (4*(p.1 : ℚ)+2*(p.2 : ℚ),-2*(p.1 : ℚ)+2*(p.2 : ℚ))
  map_zero' := by simp
  map_add' := by
    intro p q
    apply Prod.ext <;> simp <;> ring

def rationalKiteCenterLattice : AddSubgroup (ℚ × ℚ) := kiteCenterMap.range

theorem rationalKitePoint_lattice (p : KiteVertexPoint) (h : InKiteCenterLattice p) :
    rationalKitePoint p ∈ rationalKiteCenterLattice := by
  rcases h with ⟨h1,h2⟩
  have he1 : 4*((p.1-p.2)/6)+2*((p.1+2*p.2)/6) = p.1 := by omega
  have he2 : -2*((p.1-p.2)/6)+2*((p.1+2*p.2)/6) = p.2 := by omega
  refine ⟨((p.1-p.2)/6,(p.1+2*p.2)/6),?_⟩
  apply Prod.ext
  · change 4*((p.1-p.2)/6 : ℤ)+2*((p.1+2*p.2)/6 : ℤ) = (p.1 : ℚ)
    exact_mod_cast he1
  · change -2*((p.1-p.2)/6 : ℤ)+2*((p.1+2*p.2)/6 : ℤ) = (p.2 : ℚ)
    exact_mod_cast he2

theorem rationalKitePoint_add (p q : KiteVertexPoint) :
    rationalKitePoint (kiteVertexAdd p q) = rationalKitePoint p+rationalKitePoint q := by
  apply Prod.ext <;> simp [rationalKitePoint,kiteVertexAdd]

theorem rationalKitePoint_sub (p q : KiteVertexPoint) :
    rationalKitePoint (kiteVertexSub p q) = rationalKitePoint p-rationalKitePoint q := by
  apply Prod.ext <;> simp [rationalKitePoint,kiteVertexSub]

theorem developed_anchor_difference (x y : ℚ × ℚ) (a b : Fin 12) (e j : Fin 14)
    (h : x+rationalKitePoint (deformedVertex a e) =
      y+rationalKitePoint (deformedVertex b (next j))) :
    (y+rationalKitePoint (deformedOffset b))-(x+rationalKitePoint (deformedOffset a)) =
      rationalKitePoint (deformedAnchorShift a b e j) := by
  rw [deformedAnchorShift,rationalKitePoint_sub,rationalKitePoint_add,rationalKitePoint_sub]
  have hh : y-x = rationalKitePoint (deformedVertex a e)-rationalKitePoint (deformedVertex b (next j)) := by
    exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using h.symm)
  rw [←hh]
  abel

end
end SpectreGeometry
