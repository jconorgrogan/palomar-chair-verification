module

public import SpectreGeometry.PolygonSegments
public import SpectreGeometry.PolygonFanData
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FinCases

@[expose] public section


/-! A concrete compact polygonal carrier, defined as the fourteen certified
radial triangles. This proves compactness and nonempty interior of the body;
its tiling properties and physical correspondence remain separate. -/
namespace SpectreGeometry
noncomputable section
open scoped BigOperators

def triangleBody (i : Fin 14) : Set RealPoint :=
  convexHull ℝ {realVertex i,realVertex (next i),realize fanCenter}

def polygonBody : Set RealPoint := ⋃ i : Fin 14, triangleBody i

theorem triangleBody_compact (i : Fin 14) : IsCompact (triangleBody i) :=
  (Set.toFinite {realVertex i,realVertex (next i),realize fanCenter}).isCompact_convexHull ℝ

theorem polygonBody_compact : IsCompact polygonBody := isCompact_iUnion triangleBody_compact

theorem three_point_convex_combo (a b c : RealPoint) (α β γ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hsum : α+β+γ=1) :
    α • a + β • b + γ • c ∈ convexHull ℝ {a,b,c} := by
  let w : Fin 3 → ℝ := ![α,β,γ]
  let z : Fin 3 → RealPoint := ![a,b,c]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i hi
    fin_cases i <;> simp only [w] <;> assumption
  have hws : ∑ i : Fin 3, w i = 1 := by
    simpa [Fin.sum_univ_succ,w,add_assoc] using hsum
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)), z i ∈ convexHull ℝ {a,b,c} := by
    intro i hi
    apply subset_convexHull
    fin_cases i <;> simp [z]
  have hh := (convex_convexHull ℝ {a,b,c}).sum_mem hw hws hz
  simpa [Fin.sum_univ_succ,w,z,add_assoc] using hh

def interiorRectangle : Set RealPoint :=
  Set.Ioo (49/100 : ℝ) (51/100) ×ˢ Set.Ioo (24/100 : ℝ) (26/100)

theorem interiorRectangle_open : IsOpen interiorRectangle := isOpen_Ioo.prod isOpen_Ioo

theorem interiorRectangle_subset_first_triangle : interiorRectangle ⊆ triangleBody 0 := by
  intro p hp
  obtain ⟨hx,hy⟩ := hp
  have h1 : 0 ≤ 1-p.1+p.2/2 := by linarith [hx.1,hx.2,hy.1,hy.2]
  have h2 : 0 ≤ p.1-3*p.2/2 := by linarith [hx.1,hx.2,hy.1,hy.2]
  have h3 : 0 ≤ p.2 := by linarith [hy.1]
  have hh := three_point_convex_combo (0,0) (1,0) (3/2,1)
    (1-p.1+p.2/2) (p.1-3*p.2/2) p.2 h1 h2 h3 (by ring)
  have he : (1-p.1+p.2/2) • ((0,0) : RealPoint) +
      (p.1-3*p.2/2) • (1,0) + p.2 • (3/2,1) = p := by
    apply Prod.ext <;> simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul] <;> ring
  rw [he] at hh
  have hvertices : triangleBody 0 = convexHull ℝ {((0,0) : RealPoint),(1,0),(3/2,1)} := by
    norm_num [triangleBody,realVertex,realize,vertex,vertices,next,fanCenter,Quad3.eval]
  rw [hvertices]
  exact hh

theorem interiorRectangle_subset : interiorRectangle ⊆ polygonBody := by
  intro p hp
  exact Set.mem_iUnion.mpr ⟨0,interiorRectangle_subset_first_triangle hp⟩

theorem polygonBody_interior_nonempty : (interior polygonBody).Nonempty := by
  have hp : ((1/2,1/4) : RealPoint) ∈ interiorRectangle := by norm_num [interiorRectangle]
  have hi : ((1/2,1/4) : RealPoint) ∈ interior interiorRectangle := by
    rw [interiorRectangle_open.interior_eq]
    exact hp
  exact ⟨(1/2,1/4),interior_mono interiorRectangle_subset hi⟩

end
end SpectreGeometry
