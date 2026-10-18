module

public import ProductClosure.GenericComplementaryKeys
public import ProductClosure.CreaseCompanionPropagation

@[expose] public section

/-! Actual whole-complex companions in arbitrary Euclidean physical tilings.
Dense complementary incidence is derived from physical angular conservation;
connectedness and the actual three-key exclusion prevent all switching. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Every key of every actual tile has exactly one other indexed native key
complex containing its entire closed crease complex. The only tiling fields
are coverage and disjoint actual interiors. All local matching, genericity,
and no-switching inputs are discharged by the preceding concrete modules.
Reciprocal containment equality is derived below; frame rigidity is subsequent. -/
theorem PhysicalTiling.unique_whole_crease_companion
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) :
    ∃! iv : ι × Site polyCells, iv.1 ≠ root ∧
      f root '' creaseComplex a u ⊆ f iv.1 '' creaseComplex a iv.2 := by
  apply whole_crease_companion_of_dense_matches hm a f T.interiors_disjoint root u
  · exact T.genericBaseCrease_dense_companions hm root u
  · exact T.genericSideCrease_dense_companions hm root u

/-- Reciprocal whole-companion containment is equality. A third tile would
violate the actual no-three-key bound at any root-complex point. On the
root tile, disjoint native tubes identify the returning key itself. -/
theorem PhysicalTiling.unique_equal_crease_companion
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) :
    ∃! iv : ι × Site polyCells, iv.1 ≠ root ∧
      f root '' creaseComplex a u = f iv.1 '' creaseComplex a iv.2 := by
  classical
  obtain ⟨iv, hiv, huniq⟩ := T.unique_whole_crease_companion hm root u
  obtain ⟨jv, hjv, _⟩ := T.unique_whole_crease_companion hm iv.1 iv.2
  obtain ⟨x, hx⟩ := (creaseComplex_nonempty a u).image (f root)
  have hxi := hiv.2 hx
  have hxj := hjv.2 hxi
  have hjtile : jv.1 = root := by
    by_contra hjroot
    exact no_three_distinct_key_incidents hm a f T.interiors_disjoint root iv.1 jv.1
      (Ne.symm hiv.1) (Ne.symm hjroot) (Ne.symm hjv.1) u iv.2 jv.2 x
      (image_mono (creaseComplex_subset_keyGraph a u) hx)
      (image_mono (creaseComplex_subset_keyGraph a iv.2) hxi)
      (image_mono (creaseComplex_subset_keyGraph a jv.2) hxj)
  have hjsite : jv.2 = u := by
    by_contra hju
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨z, hz, hxz⟩ := hxj
    have hyz : y = z := (f root).injective (by simpa [hjtile] using hxy.trans hxz.symm)
    subst z
    exact Set.disjoint_left.mp (creaseComplex_pairwise_disjoint hm a hju) hz hy
  have hback : f iv.1 '' creaseComplex a iv.2 ⊆ f root '' creaseComplex a u := by
    simpa [hjtile, hjsite] using hjv.2
  refine ⟨iv, ⟨hiv.1, subset_antisymm hiv.2 hback⟩, ?_⟩
  intro kv hkv
  exact huniq kv ⟨hkv.1, hkv.2.subset⟩

end
end ProductClosure.NativeCompiler
