module

public import SpectreGeometry.PolygonProductIsometries

@[expose] public section


namespace SpectreGeometry
noncomputable section

@[simp] theorem euclideanProductCoordinates_zero :
    euclideanProductCoordinates (0,0) = 0 := by
  ext i; fin_cases i <;> rfl

theorem euclideanProductCoordinates_add (a b : ProductPlane × ProductPlane) :
    euclideanProductCoordinates (a+b) =
      euclideanProductCoordinates a+euclideanProductCoordinates b := by
  ext i; fin_cases i <;> rfl

/-- Conjugating any ambient translation by a root isometry and the orthogonal
product chart gives two planar translations. Both are zero exactly when the
ambient translation is zero. No tiling or global splitting is assumed. -/
theorem ambient_translation_product_components (g : EFour ≃ᵢ EFour) (v : EFour) :
    ∃ a b : ProductPlane,
      (∀ x y : ProductPlane,
        g (euclideanProductCoordinates (a+x,b+y)) =
          v+g (euclideanProductCoordinates (x,y))) ∧
      (a = 0 ∧ b = 0 ↔ v = 0) := by
  let u := euclideanProductCoordinates.symm (g.toRealLinearIsometryEquiv.symm v)
  have hu : euclideanProductCoordinates u = g.toRealLinearIsometryEquiv.symm v :=
    euclideanProductCoordinates.apply_symm_apply _
  have hL : g.toRealLinearIsometryEquiv (euclideanProductCoordinates u) = v := by
    rw [hu,g.toRealLinearIsometryEquiv.apply_symm_apply]
  refine ⟨u.1,u.2,?_,?_⟩
  · intro x y
    change g (euclideanProductCoordinates (u+(x,y))) = _
    rw [euclideanProductCoordinates_add]
    have he := g.toRealLinearIsometryEquiv.map_add
      (euclideanProductCoordinates u) (euclideanProductCoordinates (x,y))
    rw [hL] at he
    simp only [IsometryEquiv.toRealLinearIsometryEquiv_apply] at he
    have hh := congrArg (fun z : EFour => z+g 0) he
    simpa only [add_assoc,sub_add_cancel] using hh
  · constructor
    · rintro ⟨ha,hb⟩
      have hu0 : u = (0,0) := Prod.ext ha hb
      rw [hu0,euclideanProductCoordinates_zero,map_zero] at hL
      exact hL.symm
    · intro hv
      have he : euclideanProductCoordinates u = euclideanProductCoordinates (0,0) := by
        rw [hu,hv,map_zero,euclideanProductCoordinates_zero]
      have he' := euclideanProductCoordinates.injective he
      exact ⟨congrArg Prod.fst he',congrArg Prod.snd he'⟩

end
end SpectreGeometry
