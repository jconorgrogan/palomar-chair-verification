module

public import SpectreGeometry.ReverseSourceHexLocalFinite
public import SpectreFinite.ListedPatches
public import Mathlib.Analysis.Convex.Segment

@[expose] public section


namespace SpectreGeometry.ReverseExistence
noncomputable section

def sourceHexCorner (d : Fin 6) : ℝ × ℝ :=
  [((-2/3:ℝ),(1/3:ℝ)),((-1/3:ℝ),(-1/3:ℝ)),((1/3:ℝ),(-2/3:ℝ)),
   ((2/3:ℝ),(-1/3:ℝ)),((1/3:ℝ),(1/3:ℝ)),((-1/3:ℝ),(2/3:ℝ))].getD d.val (0,0)

def sourceHexNeighbor (c : ℤ × ℤ) (d : Fin 6) : ℤ × ℤ :=
  (c.1+(SpectreFinite.direction d).1,c.2+(SpectreFinite.direction d).2)

theorem sourceHex_intersection_neighbor {c c' : ℤ × ℤ} (hne : c' ≠ c)
    (h : (sourceHexCarrier c ∩ sourceHexCarrier c').Nonempty) :
    ∃ d : Fin 6, c' = sourceHexNeighbor c d := by
  obtain ⟨p,hp,hp'⟩ := h
  rcases hp with ⟨h1,h2,h3,h4,h5,h6⟩
  rcases hp' with ⟨g1,g2,g3,g4,g5,g6⟩
  have hxl : (-4:ℤ) ≤ 3*(c'.1-c.1) := by
    have hr : (-4:ℝ) ≤ 3*((c'.1:ℝ)-(c.1:ℝ)) := by linarith
    exact_mod_cast hr
  have hxu : 3*(c'.1-c.1) ≤ (4:ℤ) := by
    have hr : 3*((c'.1:ℝ)-(c.1:ℝ)) ≤ (4:ℝ) := by linarith
    exact_mod_cast hr
  have hyl : (-4:ℤ) ≤ 3*(c'.2-c.2) := by
    have hr : (-4:ℝ) ≤ 3*((c'.2:ℝ)-(c.2:ℝ)) := by linarith
    exact_mod_cast hr
  have hyu : 3*(c'.2-c.2) ≤ (4:ℤ) := by
    have hr : 3*((c'.2:ℝ)-(c.2:ℝ)) ≤ (4:ℝ) := by linarith
    exact_mod_cast hr
  have hx : c'.1-c.1 = -1 ∨ c'.1-c.1 = 0 ∨ c'.1-c.1 = 1 := by omega
  have hy : c'.2-c.2 = -1 ∨ c'.2-c.2 = 0 ∨ c'.2-c.2 = 1 := by omega
  rcases hx with hx|hx|hx <;> rcases hy with hy|hy|hy
  · have hxr : (c'.1:ℝ)-(c.1:ℝ) = (-1:ℝ) := by exact_mod_cast hx
    have hyr : (c'.2:ℝ)-(c.2:ℝ) = (-1:ℝ) := by exact_mod_cast hy
    exfalso
    linarith
  · refine ⟨0,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · refine ⟨5,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · refine ⟨1,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · exfalso
    apply hne
    apply Prod.ext <;> omega
  · refine ⟨4,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · refine ⟨2,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · refine ⟨3,?_⟩
    apply Prod.ext <;> simp [sourceHexNeighbor,SpectreFinite.direction] <;> omega
  · have hxr : (c'.1:ℝ)-(c.1:ℝ) = (1:ℝ) := by exact_mod_cast hx
    have hyr : (c'.2:ℝ)-(c.2:ℝ) = (1:ℝ) := by exact_mod_cast hy
    exfalso
    linarith

theorem sourceHex_neighbor_parametric (u v : ℝ) (d : Fin 6) :
    (sourceHexOffset u v ∧ sourceHexOffset
      (u-(SpectreFinite.direction d).1) (v-(SpectreFinite.direction d).2)) ↔
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      u = (1-t)*(sourceHexCorner d).1+t*(sourceHexCorner (d+1)).1 ∧
      v = (1-t)*(sourceHexCorner d).2+t*(sourceHexCorner (d+1)).2 := by
  fin_cases d <;> norm_num [sourceHexCorner,SpectreFinite.direction]
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨3*u+2,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨-3*v-1,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨3*u-1,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨2-3*u,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨3*v-1,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith
  · constructor
    · rintro ⟨h,g⟩
      rcases h with ⟨h1,h2,h3,h4,h5,h6⟩
      rcases g with ⟨g1,g2,g3,g4,g5,g6⟩
      refine ⟨-1-3*u,?_,?_,?_,?_⟩ <;> linarith
    · rintro ⟨t,ht0,ht1,hu,hv⟩
      constructor <;> unfold sourceHexOffset <;>
        refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

end
end SpectreGeometry.ReverseExistence
