module

public import SpectreGeometry.DeformationHomeomorphismDiameterData
public import SpectreGeometry.DeformationHomeomorphismTile

@[expose] public section


/-! A strict quadratic maximum principle proves that the actual polygon has
one unordered diameter pair. No recognition of corners is assumed. -/
namespace SpectreGeometry.Deformation
noncomputable section
open Set

def squaredDistance (x y : RealPoint) : ℝ := (x.1-y.1)^2+(x.2-y.2)^2

theorem squaredDistance_nonneg (x y : RealPoint) : 0 ≤ squaredDistance x y :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem squaredDistance_zero (x y : RealPoint) (h : squaredDistance x y=0) : x=y := by
  have hx : x.1=y.1 := by
    have := sq_nonneg (x.2-y.2)
    dsimp [squaredDistance] at h
    nlinarith [sq_nonneg (x.1-y.1)]
  have hy : x.2=y.2 := by
    dsimp [squaredDistance] at h
    nlinarith [sq_nonneg (x.1-y.1),sq_nonneg (x.2-y.2)]
  exact Prod.ext hx hy

theorem squaredDistance_combo (x z y : RealPoint) (a b : ℝ) (hab : a+b=1) :
    squaredDistance (a • x+b • z) y =
      a*squaredDistance x y+b*squaredDistance z y-a*b*squaredDistance x z := by
  have hb : b=1-a := by linarith
  subst b
  simp only [squaredDistance,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

/-- A sphere touches a convex hull only in its generating points when all
of those points lie in the associated closed ball. -/
theorem squaredDistance_hull_bound (s : Set RealPoint) (y : RealPoint) (D : ℝ)
    (hs : ∀ x ∈ s, squaredDistance x y ≤ D) :
    ∀ x ∈ convexHull ℝ s, squaredDistance x y ≤ D ∧ (squaredDistance x y=D → x∈s) := by
  let T : Set RealPoint := {x | squaredDistance x y ≤ D ∧ (squaredDistance x y=D → x∈s)}
  have hst : s ⊆ T := fun x hx => ⟨hs x hx,fun _ => hx⟩
  have hc : Convex ℝ T := by
    intro u hu v hv a b ha hb hab
    change squaredDistance (a • u+b • v) y ≤ D ∧ _
    have hu' : squaredDistance u y ≤ D ∧ (squaredDistance u y=D → u∈s) := hu
    have hv' : squaredDistance v y ≤ D ∧ (squaredDistance v y=D → v∈s) := hv
    have he := squaredDistance_combo u v y a b hab
    have hn := squaredDistance_nonneg u v
    have hw : a*squaredDistance u y+b*squaredDistance v y ≤ D := by
      calc
        _ ≤ a*D+b*D := add_le_add (mul_le_mul_of_nonneg_left hu'.1 ha) (mul_le_mul_of_nonneg_left hv'.1 hb)
        _ = D := by rw [←add_mul,hab,one_mul]
    have hp : 0 ≤ a*b*squaredDistance u v := mul_nonneg (mul_nonneg ha hb) hn
    refine ⟨by linarith,?_⟩
    intro hz
    by_cases hza : a=0
    · have hzb : b=1 := by linarith
      simpa [hza,hzb] using hv'.2 (by simpa [hza,hzb] using hz)
    by_cases hzb : b=0
    · have hza' : a=1 := by linarith
      simpa [hza',hzb] using hu'.2 (by simpa [hza',hzb] using hz)
    have hpz : a*b*squaredDistance u v=0 := by linarith
    have huv : u=v := squaredDistance_zero u v ((mul_eq_zero.mp hpz).resolve_left
      (mul_ne_zero hza hzb))
    subst v
    have hcombo : a • u+b • u=u := by rw [←add_smul,hab,one_smul]
    rw [hcombo] at hz ⊢
    exact hu'.2 hz
  exact convexHull_min hst hc

def polygonVertices : Set RealPoint := range realVertex

theorem polygonBody_subset_vertex_hull : polygonBody ⊆ convexHull ℝ polygonVertices := by
  rw [sourceTriangles_cover_polygonBody]
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  rw [sourceTriangle_eq_hull] at hi
  exact convexHull_mono (by rintro _ ⟨v,rfl⟩; exact ⟨triangleIndex i v,rfl⟩) hi

theorem vertex_squaredDistance (i j : Fin 14) :
    squaredDistance (realVertex i) (realVertex j)=Quad3.eval (vertexSquaredDistance i j)/4 := by
  have h := realize_dot (ExactPoint.sub (vertex i) (vertex j)) (ExactPoint.sub (vertex i) (vertex j))
  rw [realize_sub] at h
  change RealPoint.dot (RealPoint.sub (realVertex i) (realVertex j))
    (RealPoint.sub (realVertex i) (realVertex j)) = _ at h
  simpa [squaredDistance,RealPoint.dot,RealPoint.sub,pow_two,vertexSquaredDistance] using h

def diameterSquared : ℝ := 12+6*Real.sqrt 3

theorem vertex_diameter_bound (i j : Fin 14) :
    squaredDistance (realVertex i) (realVertex j) ≤ diameterSquared ∧
      (squaredDistance (realVertex i) (realVertex j)=diameterSquared ↔ DiameterPair i j) := by
  rw [vertex_squaredDistance]
  by_cases h : DiameterPair i j
  · rw [diameter_pair_value i j h]
    norm_num [Quad3.eval,diameterSquared,h]
    ring_nf
    trivial
  · have hp := Quad3.positive_sound _ (other_pair_strictly_shorter i j h)
    rw [Quad3.eval_sub] at hp
    norm_num [Quad3.eval] at hp
    have hlt : Quad3.eval (vertexSquaredDistance i j)/4 < diameterSquared := by
      dsimp [diameterSquared,Quad3.eval]
      linarith
    exact ⟨hlt.le,iff_of_false (ne_of_lt hlt) h⟩

theorem polygon_diameter_unique (x y : RealPoint) (hx : x∈polygonBody) (hy : y∈polygonBody)
    (hxy : squaredDistance x y=diameterSquared) :
    (x=realVertex 6 ∧ y=realVertex 12) ∨ (x=realVertex 12 ∧ y=realVertex 6) := by
  have hxH := polygonBody_subset_vertex_hull hx
  have hyH := polygonBody_subset_vertex_hull hy
  have hb : ∀ a∈polygonVertices, ∀ b∈polygonVertices, squaredDistance a b ≤ diameterSquared := by
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    exact (vertex_diameter_bound i j).1
  have hb' : ∀ a∈polygonVertices, squaredDistance a y ≤ diameterSquared := by
    intro a ha
    have ht := (squaredDistance_hull_bound polygonVertices a diameterSquared
      (fun b hb' => by simpa [squaredDistance,sub_sq_comm] using hb a ha b hb') y hyH).1
    simpa [squaredDistance,sub_sq_comm] using ht
  obtain ⟨i,rfl⟩ := (squaredDistance_hull_bound polygonVertices y diameterSquared hb' x hxH).2 hxy
  obtain ⟨j,rfl⟩ := (squaredDistance_hull_bound polygonVertices (realVertex i) diameterSquared
    (fun b hb' => by simpa [squaredDistance,sub_sq_comm] using hb (realVertex i) ⟨i,rfl⟩ b hb') y hyH).2
      (by simpa [squaredDistance,sub_sq_comm] using hxy)
  rcases (vertex_diameter_bound i j).2.mp hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp

theorem polygon_below_three (x : RealPoint) (hx : x∈polygonBody) : x.2<3 := by
  have hh : convexHull ℝ polygonVertices ⊆ {p : RealPoint | p.2<3} := by
    apply convexHull_min
    · rintro _ ⟨i,rfl⟩
      have hp := Quad3.positive_sound _ (vertices_below_three i)
      rw [Quad3.eval_sub] at hp
      norm_num [Quad3.eval] at hp
      change Quad3.eval (vertex i).2/2<3
      dsimp [Quad3.eval]
      linarith
    · intro u hu v hv a b ha hb hab
      change a*u.2+b*v.2<3
      change u.2<3 at hu
      change v.2<3 at hv
      have hw : 0<a ∨ 0<b := by by_contra h; push_neg at h; linarith
      rcases hw with hw | hw
      · nlinarith [mul_pos hw (sub_pos.mpr hu),mul_nonneg hb (sub_nonneg.mpr hv.le)]
      · nlinarith [mul_nonneg ha (sub_nonneg.mpr hu.le),mul_pos hw (sub_pos.mpr hv)]
  exact hh (polygonBody_subset_vertex_hull hx)

end
end SpectreGeometry.Deformation
