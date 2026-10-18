module

public import SpectreGeometry.PolygonProductConeGerms

@[expose] public section


namespace SpectreGeometry
noncomputable section
open Set

abbrev ProductPlane := EuclideanSpace ℝ (Fin 2)

def euclideanProductCoordinates : (ProductPlane × ProductPlane) ≃ₜ EFour :=
  (euclideanCoordinates.symm.prodCongr euclideanCoordinates.symm).trans
    productCoordinates.toHomeomorph

@[simp] theorem euclideanProductCoordinates_apply (x y : ProductPlane) :
    euclideanProductCoordinates (x,y) = WithLp.toLp 2 ![x 0,x 1,y 0,y 1] := rfl

theorem euclideanProductCoordinates_dist_sq (x y : ProductPlane × ProductPlane) :
    dist (euclideanProductCoordinates x) (euclideanProductCoordinates y)^2 =
      dist x.1 y.1 ^ 2 + dist x.2 y.2 ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq,EuclideanSpace.dist_sq_eq,EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_succ]
  change dist (x.1 0) (y.1 0)^2 + (dist (x.1 1) (y.1 1)^2 +
    (dist (x.2 0) (y.2 0)^2 + (dist (x.2 1) (y.2 1)^2 + 0))) =
    (dist (x.1 0) (y.1 0)^2 + (dist (x.1 1) (y.1 1)^2 + 0)) +
    (dist (x.2 0) (y.2 0)^2 + (dist (x.2 1) (y.2 1)^2 + 0))
  ring

/-- Independent planar isometries act isometrically on the orthogonal product. -/
def productPlacement (f g : ProductPlane ≃ᵢ ProductPlane) : EFour ≃ᵢ EFour where
  toEquiv := euclideanProductCoordinates.toEquiv.symm.trans
    ((f.toEquiv.prodCongr g.toEquiv).trans euclideanProductCoordinates.toEquiv)
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    obtain ⟨x,rfl⟩ := euclideanProductCoordinates.surjective x
    obtain ⟨y,rfl⟩ := euclideanProductCoordinates.surjective y
    change dist (euclideanProductCoordinates ((f.toEquiv.prodCongr g.toEquiv)
      (euclideanProductCoordinates.symm (euclideanProductCoordinates x))))
      (euclideanProductCoordinates ((f.toEquiv.prodCongr g.toEquiv)
      (euclideanProductCoordinates.symm (euclideanProductCoordinates y)))) = _
    rw [euclideanProductCoordinates.symm_apply_apply,euclideanProductCoordinates.symm_apply_apply]
    change dist (euclideanProductCoordinates (f x.1,g x.2))
      (euclideanProductCoordinates (f y.1,g y.2)) =
      dist (euclideanProductCoordinates x) (euclideanProductCoordinates y)
    have h := euclideanProductCoordinates_dist_sq (f x.1,g x.2) (f y.1,g y.2)
    rw [f.dist_eq,g.dist_eq,←euclideanProductCoordinates_dist_sq x y] at h
    nlinarith [dist_nonneg (x := euclideanProductCoordinates (f x.1,g x.2))
      (y := euclideanProductCoordinates (f y.1,g y.2)),
      dist_nonneg (x := euclideanProductCoordinates x) (y := euclideanProductCoordinates y)]

@[simp] theorem productPlacement_apply (f g : ProductPlane ≃ᵢ ProductPlane)
    (x y : ProductPlane) :
    productPlacement f g (euclideanProductCoordinates (x,y)) =
      euclideanProductCoordinates (f x,g y) := by
  change euclideanProductCoordinates ((f.toEquiv.prodCongr g.toEquiv)
    (euclideanProductCoordinates.symm (euclideanProductCoordinates (x,y)))) = _
  rw [euclideanProductCoordinates.symm_apply_apply]
  rfl

theorem euclidean_product_body :
    polygonProductBody = euclideanProductCoordinates '' (euclideanBody ×ˢ euclideanBody) := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩,⟨ha,hb⟩,rfl⟩
    exact ⟨(euclideanCoordinates a,euclideanCoordinates b),
      ⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,by simp [euclideanProductCoordinates]⟩
  · rintro ⟨⟨a,b⟩,⟨⟨a,ha,rfl⟩,⟨b,hb,rfl⟩⟩,rfl⟩
    exact ⟨(a,b),⟨ha,hb⟩,by simp [euclideanProductCoordinates]⟩

end
end SpectreGeometry
