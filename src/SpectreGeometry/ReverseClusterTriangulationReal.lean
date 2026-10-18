module

public import SpectreGeometry.ReverseClusterTriangulationCertificates
public import SpectreGeometry.RealPolygonFacets
public import SpectreGeometry.LiteralKiteBody
public import SpectreGeometry.ConvexZeroFace

@[expose] public section


/-! Real soundness of finite common-mesh carrier certificates. The conclusions
are equalities of closed two-dimensional carriers, not boundary equalities. -/
namespace SpectreGeometry.ReverseClusterTriangulation
noncomputable section
open Set SpectreClusters SpectreClusters.BodyBSP HalfplaneCertificate

def familyBody (ps : List PolygonPacket) : Set RealPoint :=
  ⋃ p ∈ ps, integerHull p.vertices

def facetBody (fs : List Constraint) : Set RealPoint := {x | Satisfies fs x}

theorem packetChecked_sound (p : PolygonPacket) (hp : packetCheckedB p = true)
    (x : RealPoint) : x ∈ integerHull p.vertices ↔ Satisfies p.facets x := by
  simp only [packetCheckedB,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at hp
  rw [facetBinding_sound _ _ _ hp.1.1]
  rcases hp.2 with h | h
  · exact integerHull_facets_three _ _ h hp.1.2
  · exact integerHull_facets_four _ _ h hp.1.2

theorem familyChecked_mem (ps : List PolygonPacket) (hp : familyCheckedB ps = true)
    (p : PolygonPacket) (hm : p ∈ ps) : packetCheckedB p = true :=
  List.all_eq_true.mp hp p hm

theorem getD_mem_of_lt {α : Type} (xs : List α) (n : Nat) (d : α)
    (hn : n < xs.length) : xs.getD n d ∈ xs := by
  induction xs generalizing n with
  | nil => simp at hn
  | cons a as ih =>
    cases n with
    | zero => simp
    | succ n =>
      have h : n < as.length := by simpa using hn
      simpa only [List.getD_cons_succ,List.mem_cons] using Or.inr (ih n h)

theorem tree_covered_by_family (ps : List PolygonPacket)
    (hp : familyCheckedB ps = true) (fs : List Constraint) (tree : CoverTree)
    (ht : checkTree fs (familyFacets ps) tree = true) (x : RealPoint)
    (hx : Satisfies fs x) : x ∈ familyBody ps := by
  obtain ⟨i,hi,hxi⟩ := checkTree_sound _ _ _ ht x hx
  have hm := getD_mem_of_lt (familyFacets ps) i [] hi
  obtain ⟨p,hp',he⟩ := List.mem_map.mp hm
  rw [←he] at hxi
  exact mem_iUnion.2 ⟨p,mem_iUnion.2 ⟨hp',
    (packetChecked_sound p (familyChecked_mem ps hp p hp') x).2 hxi⟩⟩

theorem coverFamilyB_at (targets : List (List Constraint))
    (ps : List PolygonPacket) (ts : List CoverTree)
    (hc : coverFamilyB targets ps ts = true) (p : PolygonPacket) (hp : p ∈ ps) :
    ∃ t, checkTree (p.facets ++ [unitFacet]) targets t = true := by
  induction ps generalizing ts with
  | nil => simp at hp
  | cons q qs ih =>
    cases ts with
    | nil => simp [coverFamilyB] at hc
    | cons t ts =>
      simp only [coverFamilyB,Bool.and_eq_true] at hc
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨t,hc.1⟩
      · exact ih ts hc.2 hp

theorem coverFamilyB_sound (ps qs : List PolygonPacket) (trees : List CoverTree)
    (hp : familyCheckedB ps = true) (hq : familyCheckedB qs = true)
    (hc : coverFamilyB (familyFacets qs) ps trees = true) :
    familyBody ps ⊆ familyBody qs := by
  intro x hx
  obtain ⟨p,hp',hxp⟩ := by simpa only [familyBody,mem_iUnion] using hx
  obtain ⟨t,ht⟩ := coverFamilyB_at _ ps trees hc p hp'
  exact tree_covered_by_family qs hq _ t ht x (satisfies_unit_append _ _
    ((packetChecked_sound p (familyChecked_mem ps hp p hp') x).1 hxp))

theorem coverFamilyB_antisymm (ps qs : List PolygonPacket) (forward backward : List CoverTree)
    (hp : familyCheckedB ps = true) (hq : familyCheckedB qs = true)
    (hf : coverFamilyB (familyFacets qs) ps forward = true)
    (hb : coverFamilyB (familyFacets ps) qs backward = true) :
    familyBody ps = familyBody qs :=
  Subset.antisymm (coverFamilyB_sound ps qs forward hp hq hf)
    (coverFamilyB_sound qs ps backward hq hp hb)

theorem evalConstraint_combo (c : Constraint) (x y : RealPoint) (t u : ℝ)
    (htu : t+u=1) : evalConstraint c (t • x + u • y) =
      t * evalConstraint c x + u * evalConstraint c y := by
  have hu : u=1-t := by linarith
  subst u
  simp only [evalConstraint,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem constraint_nonnegative_hull (c : Constraint) (vs : List Point)
    (h : ∀ v ∈ vs, 0 ≤ edgeValue c v) (x : RealPoint) (hx : x ∈ integerHull vs) :
    0 ≤ evalConstraint c x := by
  have hs : integerPoint '' {p | p ∈ vs} ⊆ {y | 0 ≤ evalConstraint c y} := by
    rintro y ⟨p,hp,rfl⟩
    change 0 ≤ evalConstraint c (integerPoint p)
    rw [edgeValue_real]
    exact_mod_cast h p hp
  have hv : Convex ℝ {y : RealPoint | 0 ≤ evalConstraint c y} := by
    intro a ha b hb t u ht hu htu
    change 0 ≤ evalConstraint c (t • a + u • b)
    rw [evalConstraint_combo _ _ _ _ _ htu]
    exact add_nonneg (mul_nonneg ht ha) (mul_nonneg hu hb)
  exact convexHull_min hs hv hx

theorem verticesSatisfyB_sound (vs : List Point) (fs : List Constraint)
    (hc : verticesSatisfyB vs fs = true) (x : RealPoint) (hx : x ∈ integerHull vs) :
    Satisfies fs x := by
  intro c hc'
  have h := List.all_eq_true.mp hc c hc'
  exact constraint_nonnegative_hull c vs
    (fun v hv => of_decide_eq_true (List.all_eq_true.mp h v hv)) x hx

theorem familyWithinB_sound (ps : List PolygonPacket) (fs : List Constraint)
    (hc : familyWithinB ps fs = true) : familyBody ps ⊆ facetBody fs := by
  intro x hx
  obtain ⟨p,hp,hxp⟩ := by simpa only [familyBody,mem_iUnion] using hx
  exact verticesSatisfyB_sound p.vertices fs (List.all_eq_true.mp hc p hp) x hxp

theorem checked_hex_cover (ps : List PolygonPacket) (hex : List Constraint) (tree : CoverTree)
    (hp : familyCheckedB ps = true)
    (hc : checkTree (hex ++ [unitFacet]) (familyFacets ps) tree = true)
    (hw : familyWithinB ps hex = true) : familyBody ps = facetBody hex := by
  apply Subset.antisymm (familyWithinB_sound ps hex hw)
  intro x hx
  exact tree_covered_by_family ps hp _ tree hc x (satisfies_unit_append _ _ hx)

end
end SpectreGeometry.ReverseClusterTriangulation
