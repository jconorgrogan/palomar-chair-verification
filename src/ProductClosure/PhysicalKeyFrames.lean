module

public import ProductClosure.WholeBaseLabelMatching
public import ProductClosure.LabelledTangentRigidity
public import ProductClosure.OppositeCarrierNormals

@[expose] public section

/-! Exact whole-key frame matching derived from arbitrary physical tilings.
No carrier-normal, tangent-frame, center, or matching condition is a tiling
input. The proof uses measured local contacts, whole-complex propagation,
prime labels, and literal native plane/height equations. -/
namespace ProductClosure.NativeCompiler
open Set PhysicalRegistration
noncomputable section
variable {m : ℕ} {polyCells : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell polyCells)]

/-- Every actual placed key has one unique whole companion. Its full keyed
tangent frame agrees, carrier outward normal opposes, center agrees, and
signed coefficient is exactly negated. Arbitrary ambient isometries are
allowed throughout. -/
theorem PhysicalTiling.unique_framed_key_companion
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients polyCells J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root : ι) (u : Site polyCells) :
    ∃! iv : ι × Site polyCells, iv.1 ≠ root ∧
      f root '' creaseComplex a u = f iv.1 '' creaseComplex a iv.2 ∧
      (∀ i, placedNormal (f iv.1) (siteAxis iv.2 i) =
        placedNormal (f root) (siteAxis u i)) ∧
      placedNormal (f iv.1) (outward iv.2.1) = -placedNormal (f root) (outward u.1) ∧
      f root (siteCenter u) = f iv.1 (siteCenter iv.2) ∧
      a.value iv.2 = -a.value u := by
  obtain ⟨iv, hiv, _⟩ := T.unique_labelled_crease_companion hm root u
  obtain ⟨haxes, hcenter⟩ :=
    labelled_baseCreases_frame_center hm a u iv.2 (f root) (f iv.1) hiv.2.2.1
  have hnormal := whole_crease_opposite_normal_of_centers hm a u iv.2 (f root) (f iv.1)
    hiv.2.2.1 hcenter hiv.2.2.2.1 hiv.2.1.subset
  refine ⟨iv, ⟨hiv.1, hiv.2.1, haxes, hnormal, hcenter, hiv.2.2.2.1⟩, ?_⟩
  intro kv hkv
  obtain ⟨jv, hjv, huniq⟩ := T.unique_equal_crease_companion hm root u
  exact (huniq kv ⟨hkv.1, hkv.2.1⟩).trans (huniq iv ⟨hiv.1, hiv.2.1⟩).symm

end
end ProductClosure.NativeCompiler
