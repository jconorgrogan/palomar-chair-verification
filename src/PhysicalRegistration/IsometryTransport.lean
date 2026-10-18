module

public import PhysicalRegistration.NativeAssembly
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section


/-!
Actual local key charts are transported through arbitrary ambient isometric
bijections, including every rotation, reflection, and translation. Mazur–Ulam
supplies the affine structure; no lattice or signed-permutation condition is
assumed. The final theorem excludes three interior-disjoint placed key graphs
at one point, without assuming whole-key matching.
-/

namespace PhysicalRegistration
open scoped InnerProductSpace
open Set

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem affineIsometry_map_add (f : E ≃ᵃⁱ[ℝ] F) (x v : E) :
    f (x + v) = f x + f.linearIsometryEquiv v := by
  simpa only [vadd_eq_add, add_comm] using f.map_vadd x v

/-- A genuine local inward chart, with unchanged radius and slope, transports
under an arbitrary affine isometry. Its inward normal is transformed by the
orthogonal linear part and its tangent height by the inverse linear part. -/
noncomputable def LocalLipschitzGraphAt.mapAffineIsometry
    {S : Set E} {x : E} {L : ℝ} (G : LocalLipschitzGraphAt S x L)
    (f : E ≃ᵃⁱ[ℝ] F) : LocalLipschitzGraphAt (f '' S) (f x) L where
  inward := f.linearIsometryEquiv G.inward
  inward_unit := by rw [f.linearIsometryEquiv.norm_map, G.inward_unit]
  radius := G.radius
  radius_pos := G.radius_pos
  height := fun v => G.height (f.linearIsometryEquiv.symm v)
  height_zero := by simp [G.height_zero]
  height_lipschitz := by
    intro v w hv hw hvr hwr
    have hvi : ⟪G.inward, f.linearIsometryEquiv.symm v⟫_ℝ = 0 := by
      rw [← f.linearIsometryEquiv.inner_map_map G.inward
        (f.linearIsometryEquiv.symm v), f.linearIsometryEquiv.apply_symm_apply]
      exact hv
    have hwi : ⟪G.inward, f.linearIsometryEquiv.symm w⟫_ℝ = 0 := by
      rw [← f.linearIsometryEquiv.inner_map_map G.inward
        (f.linearIsometryEquiv.symm w), f.linearIsometryEquiv.apply_symm_apply]
      exact hw
    have h := G.height_lipschitz (f.linearIsometryEquiv.symm v)
      (f.linearIsometryEquiv.symm w) hvi hwi
      (by simpa using hvr) (by simpa using hwr)
    simpa only [← map_sub, f.linearIsometryEquiv.symm.norm_map] using h
  interior_above := by
    intro v s hv hvr hsr hs
    have hvi : ⟪G.inward, f.linearIsometryEquiv.symm v⟫_ℝ = 0 := by
      rw [← f.linearIsometryEquiv.inner_map_map G.inward
        (f.linearIsometryEquiv.symm v), f.linearIsometryEquiv.apply_symm_apply]
      exact hv
    have hpoint := G.interior_above (f.linearIsometryEquiv.symm v) s hvi
      (by simpa using hvr) hsr hs
    have hmap : f (x + f.linearIsometryEquiv.symm v + s • G.inward) =
        f x + v + s • f.linearIsometryEquiv G.inward := by
      rw [affineIsometry_map_add, affineIsometry_map_add,
        f.linearIsometryEquiv.apply_symm_apply, map_smul]
    have himage : f (x + f.linearIsometryEquiv.symm v + s • G.inward) ∈
        interior (f '' S) :=
      f.toHomeomorph.isOpenMap.image_interior_subset S ⟨_, hpoint, rfl⟩
    rwa [hmap] at himage

/-- Mazur–Ulam removes the need to assume affine structure of the placement:
every ambient isometric bijection preserves the actual local chart property. -/
noncomputable def LocalLipschitzGraphAt.mapIsometry
    {S : Set E} {x : E} {L : ℝ} (G : LocalLipschitzGraphAt S x L)
    (f : E ≃ᵢ F) : LocalLipschitzGraphAt (f '' S) (f x) L :=
  G.mapAffineIsometry f.toRealAffineIsometryEquiv

namespace NativeChair
noncomputable section

def keyGraph {m J : ℕ} [NeZero m] (a : Coefficients m J) (u : Site m) : Set (Space m) :=
  {x | x ∈ closedTube J u ∧ normalCoord u x = siteHeight a u x}

def placedBody {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) : Set (Space m) := f '' body a

def placedKeyGraph {m J : ℕ} [NeZero m] (a : Coefficients m J)
    (f : Space m ≃ᵢ Space m) (u : Site m) : Set (Space m) := f '' keyGraph a u

/-- Every point of every arbitrarily placed native key graph has the proved
actual interior chart. Placements are unrestricted ambient isometries. -/
def placed_key_local_graph {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (f : Space m ≃ᵢ Space m) (u : Site m)
    (y : Space m) (hy : y ∈ placedKeyGraph a f u) :
    LocalLipschitzGraphAt (placedBody a f) y
      ((J : ℝ) * pMax m J / denominator m J) := by
  let hexists : ∃ x, x ∈ keyGraph a u ∧ f x = y := hy
  let x := Classical.choose hexists
  have hx : x ∈ keyGraph a u := (Classical.choose_spec hexists).1
  have hxy : f x = y := (Classical.choose_spec hexists).2
  rw [← hxy]
  exact (body_key_local_graph hm a u x hx.1 hx.2).mapIsometry f

/-- Three interior-disjoint congruent copies of the actual bounded keyed
chair cannot meet at three key-graph points. This includes lower-dimensional
junctions and uses no face-to-face, whole-feature, or lattice hypothesis. -/
theorem no_three_placed_key_graphs {m J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients m J) (f : Fin 3 → Space m ≃ᵢ Space m)
    (u : Fin 3 → Site m) (y : Space m)
    (hy : ∀ i, y ∈ placedKeyGraph a (f i) (u i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))) :
    False :=
  no_three_local_graphs (fun i => placedBody a (f i)) y
    ((J : ℝ) * pMax m J / denominator m J)
    (native_slope_lt_half m J hm).1 (native_slope_lt_half m J hm).2
    (fun i => placed_key_local_graph hm a (f i) (u i) y (hy i)) hdisjoint

end
end NativeChair

#print axioms LocalLipschitzGraphAt.mapAffineIsometry
#print axioms LocalLipschitzGraphAt.mapIsometry
#print axioms NativeChair.placed_key_local_graph
#print axioms NativeChair.no_three_placed_key_graphs
end PhysicalRegistration
