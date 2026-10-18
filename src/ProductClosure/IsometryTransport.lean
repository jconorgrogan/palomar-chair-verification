module

public import ProductClosure.NativeAssembly
public import PhysicalRegistration.IsometryTransport

@[expose] public section

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

def keyGraph {J : ℕ} [NeZero m] (a : Coefficients S J) (u : Site S) : Set (Space m) :=
  {x | x ∈ closedTube J u ∧ normalCoord u x = siteHeight a u x}

def placedBody {J : ℕ} [NeZero m] (a : Coefficients S J)
    (f : Space m ≃ᵢ Space m) : Set (Space m) := f '' body a

def placedKeyGraph {J : ℕ} [NeZero m] (a : Coefficients S J)
    (f : Space m ≃ᵢ Space m) (u : Site S) : Set (Space m) := f '' keyGraph a u

/-- Every point of every arbitrarily placed native key graph has the proved
actual interior chart. Placements are unrestricted ambient isometries. -/
def placed_key_local_graph {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients S J) (f : Space m ≃ᵢ Space m) (u : Site S)
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
theorem no_three_placed_key_graphs {J : ℕ} [NeZero m] (hm : 2 ≤ m)
    (a : Coefficients S J) (f : Fin 3 → Space m ≃ᵢ Space m)
    (u : Fin 3 → Site S) (y : Space m)
    (hy : ∀ i, y ∈ placedKeyGraph a (f i) (u i))
    (hdisjoint : Pairwise fun i j =>
      Disjoint (interior (placedBody a (f i))) (interior (placedBody a (f j)))) :
    False :=
  no_three_local_graphs (fun i => placedBody a (f i)) y
    ((J : ℝ) * pMax m J / denominator m J)
    (native_slope_lt_half m J hm).1 (native_slope_lt_half m J hm).2
    (fun i => placed_key_local_graph hm a (f i) (u i) y (hy i)) hdisjoint

end
end ProductClosure.NativeCompiler
