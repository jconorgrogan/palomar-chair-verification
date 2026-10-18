module

public import SpectreGeometry.LiteralKiteBody
public import SpectreGeometry.GridAffineGeometry
public import SpectreClusters.GridKiteProbeData

@[expose] public section


/-! A strict interior probe for every genuine closed grid kite, and uniqueness
of the grid kite containing that probe, with infinite lattice bounds proved. -/
namespace SpectreGeometry
noncomputable section
open Set HalfplaneCertificate SpectreClusters SpectreClusters.BodyBSP SpectreClusters.GridKiteProbe

theorem integerPoint_sub (a b : SpectreClusters.Point) :
    integerPoint (SpectreClusters.sub a b) = integerPoint a-integerPoint b := by
  ext <;> simp [integerPoint,SpectreClusters.sub]

theorem localKite_mem_iff (k : Turn) (x : RealPoint) :
    x ∈ integerHull (localVertices k) ↔ Satisfies (localFacets k) x :=
  integerHull_facets_four _ x (by revert k; decide) (local_facets_convex k)

theorem gridKiteBody_translate (c : Cell) :
    gridKiteBody c = (Homeomorph.addLeft (integerPoint (lattice c.center))) ''
      integerHull (localVertices c.sector) := by
  have h := integerHull_image_motion 0 c.center (localVertices c.sector)
  simpa only [gridKiteBody,cellVertices,SpectreClusters.rotate,Fin.val_zero,gridMotion_apply,
    gridRotation,Homeomorph.coe_addLeft] using h

theorem gridKiteBody_mem_iff (c : Cell) (x : RealPoint) :
    x ∈ gridKiteBody c ↔ x-integerPoint (lattice c.center) ∈ integerHull (localVertices c.sector) := by
  rw [gridKiteBody_translate]
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa using hy
  · intro hx
    exact ⟨_,hx,by simp⟩

theorem evalConstraint_continuous (c : Constraint) : Continuous (evalConstraint c) := by
  unfold evalConstraint
  fun_prop

theorem strict_facets_open (fs : List Constraint) :
    IsOpen {x : RealPoint | ∀ c ∈ fs, 0 < evalConstraint c x} := by
  induction fs with
  | nil => simpa using isOpen_univ
  | cons c fs ih =>
    simpa only [List.mem_cons,forall_eq_or_imp,Set.setOf_and] using
      (isOpen_lt continuous_const (evalConstraint_continuous c)).inter ih

theorem localProbe_mem_interior (k : Turn) :
    integerPoint (localProbe k) ∈ interior (integerHull (localVertices k)) := by
  apply interior_maximal (t := {x : RealPoint | ∀ c ∈ localFacets k, 0<evalConstraint c x})
    (fun x hx => (localKite_mem_iff k x).mpr (fun c hc => (hx c hc).le))
    (strict_facets_open (localFacets k))
  intro c hc
  rw [edgeValue_real]
  exact_mod_cast (of_decide_eq_true (List.all_eq_true.mp (localProbe_strict k) c hc))

/-- Every lattice kite has a proved interior point in its literal closed body. -/
theorem gridProbe_mem_interior (c : Cell) :
    integerPoint (probe c) ∈ interior (gridKiteBody c) := by
  rw [gridKiteBody_translate,←Homeomorph.image_interior]
  refine ⟨integerPoint (localProbe c.sector),localProbe_mem_interior c.sector,?_⟩
  exact (integerPoint_add _ _).symm

theorem integerHull_box (vs : List SpectreClusters.Point) (a b c d : ℝ)
    (hv : ∀ p ∈ vs, a ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ b ∧
      c ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ d) :
    ∀ x ∈ integerHull vs, a ≤ x.1 ∧ x.1 ≤ b ∧ c ≤ x.2 ∧ x.2 ≤ d := by
  apply convexHull_min
  · rintro x ⟨p,hp,rfl⟩
    exact hv p hp
  · intro x hx y hy t u ht hu htu
    change a ≤ (t • x+u • y).1 ∧ (t • x+u • y).1 ≤ b ∧
      c ≤ (t • x+u • y).2 ∧ (t • x+u • y).2 ≤ d
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    constructor
    · calc a = t*a+u*a := by rw [←add_mul,htu,one_mul]
           _ ≤ t*x.1+u*y.1 := add_le_add (mul_le_mul_of_nonneg_left hx.1 ht) (mul_le_mul_of_nonneg_left hy.1 hu)
    constructor
    · calc t*x.1+u*y.1 ≤ t*b+u*b := add_le_add (mul_le_mul_of_nonneg_left hx.2.1 ht) (mul_le_mul_of_nonneg_left hy.2.1 hu)
           _ = b := by rw [←add_mul,htu,one_mul]
    constructor
    · calc c = t*c+u*c := by rw [←add_mul,htu,one_mul]
           _ ≤ t*x.2+u*y.2 := add_le_add (mul_le_mul_of_nonneg_left hx.2.2.1 ht) (mul_le_mul_of_nonneg_left hy.2.2.1 hu)
    · calc t*x.2+u*y.2 ≤ t*d+u*d := add_le_add (mul_le_mul_of_nonneg_left hx.2.2.2 ht) (mul_le_mul_of_nonneg_left hy.2.2.2 hu)
           _ = d := by rw [←add_mul,htu,one_mul]

theorem localKite_bounds (k : Turn) (x : RealPoint) (hx : x ∈ integerHull (localVertices k)) :
    -2 ≤ x.1 ∧ x.1 ≤ 2 ∧ -2 ≤ x.2 ∧ x.2 ≤ 2 := by
  apply integerHull_box (localVertices k) (-2) 2 (-2) 2 _ x hx
  intro p hp
  exact_mod_cast localVertices_bounds k p hp

theorem probe_relative (a b : Cell) :
    integerPoint (probe a)-integerPoint (lattice b.center) =
      integerPoint (sub (localProbe a.sector) (lattice (sub b.center a.center))) := by
  rw [integerPoint_sub,probe,integerPoint_add]
  have h : lattice (sub b.center a.center) = sub (lattice b.center) (lattice a.center) := by
    ext <;> simp [lattice,sub] <;> ring
  rw [h,integerPoint_sub]
  abel

theorem probe_center_bounds (a b : Cell) (hx : integerPoint (probe a) ∈ gridKiteBody b) :
    -1 ≤ (sub b.center a.center).1 ∧ (sub b.center a.center).1 ≤ 1 ∧
      -1 ≤ (sub b.center a.center).2 ∧ (sub b.center a.center).2 ≤ 1 := by
  have hb := localKite_bounds b.sector _ ((gridKiteBody_mem_iff b _).mp hx)
  rw [probe_relative] at hb
  have hb' : -2 ≤ (sub (localProbe a.sector) (lattice (sub b.center a.center))).1 ∧
      (sub (localProbe a.sector) (lattice (sub b.center a.center))).1 ≤ 2 ∧
      -2 ≤ (sub (localProbe a.sector) (lattice (sub b.center a.center))).2 ∧
      (sub (localProbe a.sector) (lattice (sub b.center a.center))).2 ≤ 2 := by
    simp only [integerPoint] at hb
    exact_mod_cast hb
  apply lattice_box_bound
  have hp := localProbe_bounds a.sector
  simp only [sub] at hb' ⊢
  omega

/-- The probe of a kite lies in no other closed grid kite, including boundary. -/
theorem gridProbe_unique (a b : Cell) (hx : integerPoint (probe a) ∈ gridKiteBody b) : a=b := by
  have hbounds := probe_center_bounds a b hx
  have hs := (localKite_mem_iff b.sector _).mp ((gridKiteBody_mem_iff b _).mp hx)
  rw [probe_relative] at hs
  have hcheck : containedB a.sector b.sector (sub b.center a.center)=true := by
    apply List.all_eq_true.mpr
    intro line hl
    have h := hs line hl
    rw [edgeValue_real] at h
    apply decide_eq_true
    exact_mod_cast h
  let q : Fin 3 := ⟨Int.toNat ((sub b.center a.center).1+1),by omega⟩
  let r : Fin 3 := ⟨Int.toNat ((sub b.center a.center).2+1),by omega⟩
  have hdelta : ((q.val : Int)-1,(r.val : Int)-1)=sub b.center a.center := by
    ext <;> simp only [q,r] <;> omega
  have hh := (finite_unique a.sector b.sector q r).mp (hdelta ▸ hcheck)
  have hc : a.center=b.center := by
    have hx := congrArg Prod.fst hdelta
    have hy := congrArg Prod.snd hdelta
    simp only [sub] at hx hy
    rw [hh.1] at hx
    rw [hh.2.1] at hy
    ext <;> omega
  cases a
  cases b
  simp_all

end
end SpectreGeometry
