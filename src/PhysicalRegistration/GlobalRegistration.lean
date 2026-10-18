module

public import PhysicalRegistration.ComponentLatticeCover
public import PhysicalRegistration.NativeComponentOrder

@[expose] public section

/-! Global lattice registration for actual arbitrary-isometry physical
tilings. The companion graph is proved connected using cell-neighbor closure
and retained cores, rather than assumed connected. For graph-compiled
coefficients the relative frames are additionally proved proper. -/
namespace PhysicalRegistration.NativeChair
open Set
noncomputable section

/-- No physical tile can lie outside the chosen key-companion component:
its retained ball would intersect the component's nearby retained core. -/
theorem PhysicalTiling.keyReachable_all
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root i : ι) : T.KeyReachable root i := by
  have h := carrier_cover_subfamily_eq_univ a f T.interiors_disjoint
    {j | T.KeyReachable root j} (T.component_carriers_cover hm root)
  have hi : i ∈ {j | T.KeyReachable root j} := by rw [h]; exact Set.mem_univ i
  exact hi

/-- Every actual placement is an integral signed-permutation pose relative
to any chosen physical tile. No registration or connectedness premise. -/
theorem PhysicalTiling.global_integral_registration
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root i : ι) :
    HasIntegralSignedPermutation (relativePlacement (f root) (f i)) :=
  T.keyReachable_integral hm (T.keyReachable_all hm root i)

/-- Physical coverage supplies the normalization root, so even its existence
is not a caller's extra hypothesis. -/
theorem PhysicalTiling.exists_global_integral_normalization
    {m J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients m J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) :
    ∃ e : Space m ≃ᵢ Space m, ∀ i, HasIntegralSignedPermutation ((f i).trans e) := by
  obtain ⟨root, _⟩ := T.covers 0
  exact ⟨(f root).symm, T.global_integral_registration hm root⟩

/-- Properness is the determinant of the actual relative linear map. -/
theorem IsProperPlacement.refl {m : ℕ} :
    IsProperPlacement (IsometryEquiv.refl (Space m)) := by
  have h : (IsometryEquiv.refl (Space m)).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact placedNormal_refl x
  unfold IsProperPlacement
  rw [h]
  simp

theorem IsProperPlacement.trans {m : ℕ} {e g : Space m ≃ᵢ Space m}
    (he : IsProperPlacement e) (hg : IsProperPlacement g) :
    IsProperPlacement (e.trans g) := by
  have h : (e.trans g).toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap =
      g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap.comp
        e.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact placedNormal_trans e g x
  unfold IsProperPlacement at *
  rw [h, LinearMap.det_comp, he, hg, one_mul]

theorem relative_proper_refl {m : ℕ} (f : Space m ≃ᵢ Space m) :
    IsProperPlacement (relativePlacement f f) := by
  rw [relativePlacement_self]
  exact IsProperPlacement.refl

theorem relative_proper_trans {m : ℕ} {f g h : Space m ≃ᵢ Space m}
    (hfg : IsProperPlacement (relativePlacement f g))
    (hgh : IsProperPlacement (relativePlacement g h)) :
    IsProperPlacement (relativePlacement f h) := by
  simpa only [relativePlacement_trans] using hgh.trans hfg

/-- Every actual whole-complex edge is proper for the compiled coefficients;
this follows by identifying its endpoint with the unique physical companion. -/
theorem PhysicalTiling.compiled_keyCompanionEdge_proper
    {m : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients hm A hA) f) {i j : ι}
    (h : T.KeyCompanionEdge i j) :
    IsProperPlacement (relativePlacement (f i) (f j)) := by
  obtain ⟨hij, u, v, huv⟩ := h
  obtain ⟨iv, hiv, heq, hproper, _⟩ := T.compiled_exists_proper_graph_companion hm A hA i u
  obtain ⟨kv, _, huniq⟩ := T.unique_equal_crease_companion hm i u
  have hv : (j, v) = iv :=
    (huniq (j, v) ⟨Ne.symm hij, huv⟩).trans (huniq iv ⟨hiv, heq⟩).symm
  simpa only [← hv] using hproper

/-- Properness propagates over the actual component, not an assumed graph. -/
theorem PhysicalTiling.compiled_keyReachable_proper
    {m : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients hm A hA) f) {root i : ι}
    (h : T.KeyReachable root i) :
    IsProperPlacement (relativePlacement (f root) (f i)) := by
  induction h with
  | refl => exact relative_proper_refl (f root)
  | @tail i j hij hedge ih =>
    exact relative_proper_trans ih (T.compiled_keyCompanionEdge_proper hm A hA hedge)

/-- Arbitrary physical tilings of the explicitly graph-compiled native body
are globally registered, and all relative frames are proper. Translations,
rotations and reflections were unrestricted in the tiling hypothesis. -/
theorem PhysicalTiling.compiled_global_proper_integral_registration
    {m : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients hm A hA) f) (root i : ι) :
    HasIntegralSignedPermutation (relativePlacement (f root) (f i)) ∧
      IsProperPlacement (relativePlacement (f root) (f i)) :=
  ⟨T.global_integral_registration hm root i,
    T.compiled_keyReachable_proper hm A hA (T.keyReachable_all hm root i)⟩

end
end PhysicalRegistration.NativeChair
