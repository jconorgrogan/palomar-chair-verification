module

public import Mathlib.Data.Set.Prod

@[expose] public section


namespace SpectreGeometry
open Set

def cartesianTileFamily {X Y I J : Type*} (A : I → Set X) (B : J → Set Y) :
    Set (Set (X × Y)) := Set.range (fun ij : I × J => A ij.1 ×ˢ B ij.2)

theorem fst_cartesianTileFamily {X Y I J : Type*} [Nonempty J]
    (A : I → Set X) (B : J → Set Y) (hB : ∀ j, (B j).Nonempty) :
    (fun S : Set (X × Y) => Prod.fst '' S) '' cartesianTileFamily A B = Set.range A := by
  ext S
  constructor
  · rintro ⟨_,⟨⟨i,j⟩,rfl⟩,rfl⟩
    change Prod.fst '' (A i ×ˢ B j) ∈ Set.range A
    rw [Set.fst_image_prod _ (hB j)]
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨A i ×ˢ B j,⟨(i,j),rfl⟩,Set.fst_image_prod _ (hB j)⟩

theorem snd_cartesianTileFamily {X Y I J : Type*} [Nonempty I]
    (A : I → Set X) (B : J → Set Y) (hA : ∀ i, (A i).Nonempty) :
    (fun S : Set (X × Y) => Prod.snd '' S) '' cartesianTileFamily A B = Set.range B := by
  ext S
  constructor
  · rintro ⟨_,⟨⟨i,j⟩,rfl⟩,rfl⟩
    change Prod.snd '' (A i ×ˢ B j) ∈ Set.range B
    rw [Set.snd_image_prod (hA i)]
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i⟩ := ‹Nonempty I›
    exact ⟨A i ×ˢ B j,⟨(i,j),rfl⟩,Set.snd_image_prod (hA i) _⟩

theorem coordinate_image_product {X Y : Type*} (u : X → X) (v : Y → Y)
    (A : Set X) (B : Set Y) :
    (fun p : X × Y => (u p.1,v p.2)) '' (A ×ˢ B) = (u '' A) ×ˢ (v '' B) := by
  ext p
  constructor
  · rintro ⟨⟨x,y⟩,⟨hx,hy⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,⟨y,hy,rfl⟩⟩
  · rintro ⟨⟨x,hx,he⟩,⟨y,hy,hf⟩⟩
    exact ⟨(x,y),⟨hx,hy⟩,Prod.ext he hf⟩

/-- A coordinatewise symmetry of a genuine Cartesian tile family induces
symmetries of both factor families. In particular this applies to translations.
Global Cartesian consistency is an explicit premise, not a consequence here. -/
theorem cartesian_family_symmetry_projects {X Y I J : Type*} [Nonempty I] [Nonempty J]
    (A : I → Set X) (B : J → Set Y) (hA : ∀ i, (A i).Nonempty)
    (hB : ∀ j, (B j).Nonempty) (u : X → X) (v : Y → Y)
    (hsym : Set.range (fun ij : I × J =>
      (fun p : X × Y => (u p.1,v p.2)) '' (A ij.1 ×ˢ B ij.2)) = cartesianTileFamily A B) :
    Set.range (fun i => u '' A i) = Set.range A ∧
      Set.range (fun j => v '' B j) = Set.range B := by
  have he : cartesianTileFamily (fun i => u '' A i) (fun j => v '' B j) =
      cartesianTileFamily A B := by
    simpa only [coordinate_image_product,cartesianTileFamily] using hsym
  constructor
  · have hp := congrArg (fun F : Set (Set (X × Y)) =>
        (fun S : Set (X × Y) => Prod.fst '' S) '' F) he
    simpa only [fst_cartesianTileFamily _ _ (fun j => (hB j).image v),
      fst_cartesianTileFamily A B hB] using hp
  · have hp := congrArg (fun F : Set (Set (X × Y)) =>
        (fun S : Set (X × Y) => Prod.snd '' S) '' F) he
    simpa only [snd_cartesianTileFamily _ _ (fun i => (hA i).image u),
      snd_cartesianTileFamily A B hA] using hp

end SpectreGeometry
