module

public import SpectreGeometry.GridKiteProbeReal
public import SpectreGeometry.GridKiteContactData
public import SpectreGeometry.GridFieldExtraction

@[expose] public section


/-! Exact equivalence of finite vertex-incidence and nonempty intersection
of actual closed grid-kite carriers, including corner-only contact. -/
namespace SpectreGeometry
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate GridKiteContact

/-- The infinite lattice reduction is derived from real carrier membership. -/
theorem gridKite_intersection_center_bounds (a b : Cell) (x : RealPoint)
    (ha : x ∈ gridKiteBody a) (hb : x ∈ gridKiteBody b) :
    -2 ≤ (sub b.center a.center).1 ∧ (sub b.center a.center).1 ≤ 2 ∧
      -2 ≤ (sub b.center a.center).2 ∧ (sub b.center a.center).2 ≤ 2 := by
  have ha' := localKite_bounds a.sector _ ((gridKiteBody_mem_iff a x).mp ha)
  have hb' := localKite_bounds b.sector _ ((gridKiteBody_mem_iff b x).mp hb)
  have hl : -4 ≤ ((lattice (sub b.center a.center)).1 : ℝ) ∧
      ((lattice (sub b.center a.center)).1 : ℝ) ≤ 4 ∧
      -4 ≤ ((lattice (sub b.center a.center)).2 : ℝ) ∧
      ((lattice (sub b.center a.center)).2 : ℝ) ≤ 4 := by
    simp only [integerPoint,lattice,sub,Prod.fst_sub,Prod.snd_sub] at ha' hb' ⊢
    push_cast at ha' hb' ⊢
    constructor
    · linarith [ha'.1,hb'.2.1]
    constructor
    · linarith [ha'.2.1,hb'.1]
    constructor
    · linarith [ha'.2.2.1,hb'.2.2.2]
    · linarith [ha'.2.2.2,hb'.2.2.1]
  have hl' : -4 ≤ (lattice (sub b.center a.center)).1 ∧
      (lattice (sub b.center a.center)).1 ≤ 4 ∧
      -4 ≤ (lattice (sub b.center a.center)).2 ∧
      (lattice (sub b.center a.center)).2 ≤ 4 := by exact_mod_cast hl
  simp only [lattice] at hl'
  omega

theorem evalConstraint_convex_lower (line : Constraint) (bound : ℝ) :
    Convex ℝ {x : RealPoint | bound ≤ evalConstraint line x} := by
  intro x hx y hy t u ht hu htu
  change bound ≤ evalConstraint line (t • x+u • y)
  have he : evalConstraint line (t • x+u • y) =
      t*evalConstraint line x+u*evalConstraint line y := by
    simp only [evalConstraint,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    have hc : t*(line.2.2 : ℝ)+u*(line.2.2 : ℝ)=(line.2.2 : ℝ) := by
      rw [←add_mul,htu,one_mul]
    nlinarith [hc]
  rw [he]
  calc
    bound = t*bound+u*bound := by rw [←add_mul,htu,one_mul]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hx ht) (mul_le_mul_of_nonneg_left hy hu)

theorem integerHull_constraint_lower (vs : List SpectreClusters.Point) (line : Constraint)
    (bound : ℝ) (h : ∀ p ∈ vs, bound ≤ evalConstraint line (integerPoint p))
    {x : RealPoint} (hx : x ∈ integerHull vs) : bound ≤ evalConstraint line x := by
  exact convexHull_min (by rintro y ⟨p,hp,rfl⟩; exact h p hp)
    (evalConstraint_convex_lower line bound) hx

theorem strictlySeparatedB_disjoint (as bs : List SpectreClusters.Point)
    (h : strictlySeparatedB as bs = true)
    (hvalid : ∀ line ∈ polygonFacets as, ∀ p ∈ as, 0 ≤ edgeValue line p) :
    Disjoint (integerHull as) (integerHull bs) := by
  obtain ⟨line,hline,hneg⟩ := List.any_eq_true.mp h
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hp : 0 ≤ evalConstraint line x := integerHull_constraint_lower as line 0
    (by intro p hp; rw [edgeValue_real]; exact_mod_cast hvalid line hline p hp) hx
  have hn : 1 ≤ evalConstraint (negConstraint line) x :=
    integerHull_constraint_lower bs (negConstraint line) 1 (by
      intro p hp
      have hh := of_decide_eq_true (List.all_eq_true.mp hneg p hp)
      rw [eval_neg,edgeValue_real]
      exact_mod_cast (show (1 : Int) ≤ -edgeValue line p by omega)) hy
  rw [eval_neg] at hn
  linarith

theorem separatedB_disjoint (as bs : List SpectreClusters.Point)
    (h : separatedB as bs = true)
    (ha : ∀ line ∈ polygonFacets as, ∀ p ∈ as, 0 ≤ edgeValue line p)
    (hb : ∀ line ∈ polygonFacets bs, ∀ p ∈ bs, 0 ≤ edgeValue line p) :
    Disjoint (integerHull as) (integerHull bs) := by
  have hh : strictlySeparatedB as bs = true ∨ strictlySeparatedB bs as = true := by
    simpa only [separatedB,Bool.or_eq_true_iff] using h
  rcases hh with h | h
  · exact strictlySeparatedB_disjoint as bs h ha
  · exact (strictlySeparatedB_disjoint bs as h hb).symm

end
end SpectreGeometry
