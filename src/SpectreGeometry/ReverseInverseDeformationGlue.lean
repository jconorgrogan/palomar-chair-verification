module

public import SpectreGeometry.ReverseInverseDeformation

@[expose] public section


/-! Constructing the reverse deformation from actual compatible inverse
charts on an actual closed plane cover. No globally defined reverse map is
assumed by the public homeomorphism constructor. -/
namespace SpectreGeometry.ReverseExistence
noncomputable section
open Set Deformation

variable {ι : Type*}

def inverseCoverMap (C : ι → Set EPlane) (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane) (x : EPlane) : EPlane :=
  let j := Classical.choose (hcover x)
  inverseAffineChart (k j) (i j) (a j) (b j) x

theorem inverseCoverMap_on (C : ι → Set EPlane) (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane)
    (hagree : ∀ j l x, x ∈ C j → x ∈ C l →
      inverseAffineChart (k j) (i j) (a j) (b j) x =
        inverseAffineChart (k l) (i l) (a l) (b l) x)
    (j : ι) (x : EPlane) (hx : x ∈ C j) :
    inverseCoverMap C hcover k i a b x = inverseAffineChart (k j) (i j) (a j) (b j) x :=
  hagree _ j x (Classical.choose_spec (hcover x)) hx

/-- The genuine reverse plane homeomorphism constructed by choice of a local
inverse chart. Compatibility makes that choice immaterial. -/
def gluedInverseHomeomorph (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane)
    (hagree : ∀ j l x, x ∈ C j → x ∈ C l →
      inverseAffineChart (k j) (i j) (a j) (b j) x =
        inverseAffineChart (k l) (i l) (a l) (b l) x) : EPlane ≃ₜ EPlane :=
  inverseCoverHomeomorph C hlocal hclosed hcover k i a b
    (inverseCoverMap C hcover k i a b) (by
      intro j x hx
      rw [inverseCoverMap_on C hcover k i a b hagree j x hx]
      exact affine_inverse_chart (k j) (i j) (a j) (b j) x)

@[simp] theorem gluedInverseHomeomorph_apply (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane)
    (hagree : ∀ j l x, x ∈ C j → x ∈ C l →
      inverseAffineChart (k j) (i j) (a j) (b j) x =
        inverseAffineChart (k l) (i l) (a l) (b l) x) (x : EPlane) :
    gluedInverseHomeomorph C hlocal hclosed hcover k i a b hagree x =
      inverseCoverMap C hcover k i a b x :=
  inverseCoverHomeomorph_apply _ _ _ _ _ _ _ _ _ _ _

theorem gluedInverseHomeomorph_on (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane)
    (hagree : ∀ j l x, x ∈ C j → x ∈ C l →
      inverseAffineChart (k j) (i j) (a j) (b j) x =
        inverseAffineChart (k l) (i l) (a l) (b l) x)
    (j : ι) (x : EPlane) (hx : x ∈ C j) :
    gluedInverseHomeomorph C hlocal hclosed hcover k i a b hagree x =
      inverseAffineChart (k j) (i j) (a j) (b j) x := by
  rw [gluedInverseHomeomorph_apply]
  exact inverseCoverMap_on C hcover k i a b hagree j x hx

/-- Each closed chart carrier has its exact inverse-affine image. -/
theorem gluedInverseHomeomorph_image (C : ι → Set EPlane)
    (hlocal : LocallyFinite C) (hclosed : ∀ j, IsClosed (C j))
    (hcover : ∀ x, ∃ j, x ∈ C j)
    (k i : ι → Fin 12) (a b : ι → EPlane)
    (hagree : ∀ j l x, x ∈ C j → x ∈ C l →
      inverseAffineChart (k j) (i j) (a j) (b j) x =
        inverseAffineChart (k l) (i l) (a l) (b l) x)
    (j : ι) :
    gluedInverseHomeomorph C hlocal hclosed hcover k i a b hagree '' C j =
      inverseAffineChart (k j) (i j) (a j) (b j) '' C j :=
  Set.image_congr (fun x hx => gluedInverseHomeomorph_on C hlocal hclosed hcover k i a b hagree j x hx)

end
end SpectreGeometry.ReverseExistence
