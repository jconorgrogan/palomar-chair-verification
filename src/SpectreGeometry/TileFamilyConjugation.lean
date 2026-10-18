module

public import Mathlib.Data.Set.Image

@[expose] public section


namespace SpectreGeometry
open Set

/-- Pull a tile-family symmetry through an injective coordinate chart. Exact
family equality, rather than an assumed correspondence of indices, is used. -/
theorem tile_family_symmetry_conjugate {X Y I J : Type*}
    (H : X → Y) (hH : Function.Injective H) (s : X → X) (t : Y → Y)
    (A : I → Set X) (B : J → Set Y)
    (hcomm : ∀ x, H (s x) = t (H x))
    (hfamily : Set.range (fun i => H '' A i) = Set.range B)
    (hsym : Set.range (fun j => t '' B j) = Set.range B) :
    Set.range (fun i => s '' A i) = Set.range A := by
  have hc (S : Set X) : H '' (s '' S) = t '' (H '' S) := by
    rw [Set.image_image,Set.image_image]
    apply congrArg (fun k : X → Y => k '' S)
    funext x
    exact hcomm x
  apply hH.image_injective.image_injective
  calc
    (fun S : Set X => H '' S) '' Set.range (fun i => s '' A i) =
        Set.range (fun i => H '' (s '' A i)) := (Set.range_comp' _ _).symm
    _ = Set.range (fun i => t '' (H '' A i)) := by simp only [hc]
    _ = (fun S : Set Y => t '' S) '' Set.range (fun i => H '' A i) := Set.range_comp' _ _
    _ = (fun S : Set Y => t '' S) '' Set.range B := by rw [hfamily]
    _ = Set.range (fun j => t '' B j) := (Set.range_comp' _ _).symm
    _ = Set.range B := hsym
    _ = Set.range (fun i => H '' A i) := hfamily.symm
    _ = (fun S : Set X => H '' S) '' Set.range A := Set.range_comp' _ _

end SpectreGeometry
