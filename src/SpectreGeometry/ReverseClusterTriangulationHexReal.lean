module

public import SpectreGeometry.ReverseClusterTriangulationScaleReal

@[expose] public section

namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

def baseHexFacets : List Constraint :=
  [(2,1,3),(1,2,3),(-1,1,3),(-2,-1,3),(-1,-2,3),(1,-1,3)]

def baseHexBody : Set RealPoint := integerHull hexCorners

def hexFan (d : Fin 6) : Set RealPoint :=
  integerHull [(0,0),hexCorners.getD d.val (0,0),hexCorners.getD ((d.val+1)%6) (0,0)]

theorem facetHex_subset_fans : facetBody baseHexFacets ⊆ ⋃ d : Fin 6, hexFan d := by
  intro x hx
  have hh : 0 ≤ 2*x.1+x.2+3 ∧ 0 ≤ x.1+2*x.2+3 ∧
      0 ≤ -x.1+x.2+3 ∧ 0 ≤ -2*x.1-x.2+3 ∧
      0 ≤ -x.1-2*x.2+3 ∧ 0 ≤ x.1-x.2+3 := by
    simpa [facetBody,baseHexFacets,Satisfies,evalConstraint,sub_eq_add_neg] using hx
  have hfan (d : Fin 6)
      (h : Satisfies (polygonFacets [(0,0),hexCorners.getD d.val (0,0),
          hexCorners.getD ((d.val+1)%6) (0,0)]) x) : x ∈ hexFan d := by
    apply (integerHull_facets_three _ x (by simp) ?_).2 h
    have hp : ∀ d : Fin 6, polygonPositiveB [(0,0),hexCorners.getD d.val (0,0),
        hexCorners.getD ((d.val+1)%6) (0,0)] = true := by decide
    exact hp d
  by_cases ha : x.1+2*x.2 ≤ 0
  · by_cases hb : 0 ≤ x.2-x.1
    · refine mem_iUnion.2 ⟨0,hfan 0 ?_⟩
      norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
      exact ⟨by linarith,by linarith,by linarith⟩
    · by_cases hc : 2*x.1+x.2 ≤ 0
      · refine mem_iUnion.2 ⟨1,hfan 1 ?_⟩
        norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
        exact ⟨by linarith,by linarith,by linarith⟩
      · refine mem_iUnion.2 ⟨2,hfan 2 ?_⟩
        norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
        exact ⟨by linarith,by linarith,by linarith⟩
  · by_cases hb : x.2-x.1 ≤ 0
    · refine mem_iUnion.2 ⟨3,hfan 3 ?_⟩
      norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
      exact ⟨by linarith,by linarith,by linarith⟩
    · by_cases hc : 0 ≤ 2*x.1+x.2
      · refine mem_iUnion.2 ⟨4,hfan 4 ?_⟩
        norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
        exact ⟨by linarith,by linarith,by linarith⟩
      · refine mem_iUnion.2 ⟨5,hfan 5 ?_⟩
        norm_num [polygonFacets,cycleEdges,hexCorners,Satisfies,edgeFacet,evalConstraint]
        exact ⟨by linarith,by linarith,by linarith⟩

theorem baseHex_corner_mem (p : Point) (hp : p ∈ hexCorners) : integerPoint p ∈ baseHexBody :=
  subset_convexHull ℝ _ ⟨p,hp,rfl⟩

theorem baseHex_zero_mem : (0 : RealPoint) ∈ baseHexBody := by
  have h0 := baseHex_corner_mem (-2,1) (by decide)
  have h3 := baseHex_corner_mem (2,-1) (by decide)
  have h := (convex_convexHull ℝ (integerPoint '' {p | p ∈ hexCorners})) h0 h3
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ)+1/2=1 by norm_num)
  norm_num [integerPoint] at h
  exact h

theorem hexFan_subset_baseHex (d : Fin 6) : hexFan d ⊆ baseHexBody := by
  apply convexHull_min ?_ (convex_convexHull ℝ _)
  rintro x ⟨p,hp,rfl⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · have he : integerPoint (0,0) = (0 : RealPoint) := by
      ext <;> simp [integerPoint]
    rw [he]
    exact baseHex_zero_mem
  · apply baseHex_corner_mem
    exact getD_mem_of_lt hexCorners d.val (0,0) (by simpa [hexCorners] using d.isLt)
  · apply baseHex_corner_mem
    exact getD_mem_of_lt hexCorners ((d.val+1)%6) (0,0)
      (by simpa [hexCorners] using Nat.mod_lt (d.val+1) (by decide : 0<6))

theorem baseHexBody_eq_facets : baseHexBody = facetBody baseHexFacets := by
  apply Subset.antisymm
  · intro x hx
    exact verticesSatisfyB_sound hexCorners baseHexFacets (by decide) x hx
  · intro x hx
    obtain ⟨d,hd⟩ := mem_iUnion.mp (facetHex_subset_fans hx)
    exact hexFan_subset_baseHex d hd

theorem baseHexBody_eq_fans : baseHexBody = ⋃ d : Fin 6, hexFan d := by
  apply Subset.antisymm
  · rw [baseHexBody_eq_facets]
    exact facetHex_subset_fans
  · intro x hx
    obtain ⟨d,hd⟩ := mem_iUnion.mp hx
    exact hexFan_subset_baseHex d hd

def dilateFacet (n : Int) (f : Constraint) : Constraint := (f.1,f.2.1,n*f.2.2)

theorem eval_dilateFacet (n : Int) (f : Constraint) (x : RealPoint) :
    evalConstraint (dilateFacet n f) ((n : ℝ) • x) = (n : ℝ)*evalConstraint f x := by
  simp only [evalConstraint,dilateFacet,Int.cast_mul,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem satisfies_dilated (n : Int) (hn : 0<n) (fs : List Constraint) (x : RealPoint) :
    Satisfies (fs.map (dilateFacet n)) ((n : ℝ) • x) ↔ Satisfies fs x := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  constructor
  · intro hx f hf
    have h := hx (dilateFacet n f) (List.mem_map.mpr ⟨f,hf,rfl⟩)
    rw [eval_dilateFacet] at h
    exact nonneg_of_mul_nonneg_right h hn'
  · intro hx f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    rw [eval_dilateFacet]
    exact mul_nonneg hn'.le (hx g hg)

theorem facetBody_dilated (n : Int) (hn : 0<n) (fs : List Constraint) :
    facetBody (fs.map (dilateFacet n)) =
      (fun x : RealPoint => (n : ℝ) • x) '' facetBody fs := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  ext y
  constructor
  · intro hy
    change Satisfies (fs.map (dilateFacet n)) y at hy
    refine ⟨(n : ℝ)⁻¹ • y,?_,?_⟩
    · apply (satisfies_dilated n hn fs _).1
      simpa only [smul_smul,mul_inv_cancel₀ hn',one_smul] using hy
    · simp only [smul_smul,mul_inv_cancel₀ hn',one_smul]
  · rintro ⟨x,hx,rfl⟩
    exact (satisfies_dilated n hn fs x).2 hx

/-- The fixed regular axial hexagon at unit center spacing. -/
def standardHexBody : Set RealPoint :=
  (fun x : RealPoint => (1/3 : ℝ) • x) '' baseHexBody

theorem normalize_dilated_hex (n : Int) (hn : 0<n) :
    (fun x : RealPoint => (1/(3*(n : ℝ))) • x) ''
        facetBody (baseHexFacets.map (dilateFacet n)) = standardHexBody := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [facetBody_dilated n hn,←baseHexBody_eq_facets,Set.image_image]
  have he : (1/(3*(n : ℝ)))*(n : ℝ) = (1/3 : ℝ) := by field_simp [hn']
  simp only [standardHexBody,smul_smul,he]

end
end SpectreGeometry.ReverseClusterTriangulation
