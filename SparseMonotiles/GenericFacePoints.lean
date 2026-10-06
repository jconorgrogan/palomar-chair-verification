module

public import SparseMonotiles.GenericRidgePoints
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Generic points of a face arrangement

A family of affine equations may contain redundant and inconsistent equations.
After deleting intersections of distinct proper hyperplanes, every surviving
point has at most one active proper hyperplane. The exceptional intersections
have codimension at least two, so their complement is path connected and dense.
-/
namespace SparseMonotiles

open Set AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An active affine level set has the kernel of its linear part as direction. -/
theorem affineFormPlane_direction {f : E →ᵃ[ℝ] ℝ} {c : ℝ} {p : E}
    (hp : f p = c) : (affineFormPlane f c).direction = LinearMap.ker f.linear := by
  ext v
  rw [← vadd_mem_iff_mem_direction v ((mem_affineFormPlane f c p).mpr hp),
    mem_affineFormPlane, f.map_vadd, hp]
  simp only [vadd_eq_add, LinearMap.mem_ker]
  exact add_eq_right

/-- Every affine equation is empty, redundant, or a genuine hyperplane.
The empty case is separate, including in dimensions zero and one. -/
theorem affineFormPlane_trichotomy [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] ℝ) (c : ℝ) :
    affineFormPlane f c = ⊥ ∨ affineFormPlane f c = ⊤ ∨
      Module.finrank ℝ (affineFormPlane f c).direction + 1 = Module.finrank ℝ E := by
  classical
  by_cases hb : affineFormPlane f c = ⊥
  · exact Or.inl hb
  have hn : (affineFormPlane f c : Set E).Nonempty :=
    (AffineSubspace.nonempty_iff_ne_bot _).mpr hb
  obtain ⟨p,hp⟩ := hn
  have hp' := (mem_affineFormPlane f c p).mp hp
  by_cases hz : f.linear = 0
  · right; left
    apply top_unique
    intro x _
    apply (mem_affineFormPlane f c x).mpr
    have h := f.linearMap_vsub x p
    simpa [hz, hp', sub_eq_zero] using h.symm
  · right; right
    rw [affineFormPlane_direction hp']
    exact Module.Dual.finrank_ker_add_one_of_ne_zero hz

/-- Strict affine inclusion between nonempty spaces strictly lowers direction rank. -/
theorem affineSubspace_finrank_lt_of_lt [FiniteDimensional ℝ E]
    {A B : AffineSubspace ℝ E} (hne : (A : Set E).Nonempty) (h : A < B) :
    Module.finrank ℝ A.direction < Module.finrank ℝ B.direction := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (direction_le h.le) ?_
  intro heq
  exact h.ne (eq_of_direction_eq_of_nonempty_of_le heq hne h.le)

/-- Distinct affine hyperplanes cannot properly contain one another. -/
theorem affineHyperplanes_not_le [FiniteDimensional ℝ E]
    {A B : AffineSubspace ℝ E} (hne : (A : Set E).Nonempty)
    (hA : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ E)
    (hB : Module.finrank ℝ B.direction + 1 = Module.finrank ℝ E)
    (hneAB : A ≠ B) : ¬ A ≤ B := by
  intro hle
  have hlt := affineSubspace_finrank_lt_of_lt hne (lt_of_le_of_ne hle hneAB)
  omega

/-- A nonempty intersection of two distinct hyperplanes has codimension at least two. -/
theorem affineHyperplanes_inf_codimension_two [FiniteDimensional ℝ E]
    {A B : AffineSubspace ℝ E} (hne : (A ⊓ B : Set E).Nonempty)
    (hA : Module.finrank ℝ A.direction + 1 = Module.finrank ℝ E)
    (hB : Module.finrank ℝ B.direction + 1 = Module.finrank ℝ E)
    (hneAB : A ≠ B) :
    Module.finrank ℝ (A ⊓ B).direction + 2 ≤ Module.finrank ℝ E := by
  have hAn : (A : Set E).Nonempty := hne.mono (show (A ⊓ B : Set E) ⊆ A from inf_le_left)
  have hlt : A ⊓ B < A := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact affineHyperplanes_not_le hAn hA hB hneAB (heq ▸ inf_le_right)
  have hr := affineSubspace_finrank_lt_of_lt hne hlt
  omega

/-- At a generic arrangement point all active proper planes coincide. -/
def genericPlanePoints {ι : Type*} (H : ι → AffineSubspace ℝ E) : Set E :=
  {x | ∀ i j, x ∈ H i → x ∈ H j → H i ≠ ⊤ → H j ≠ ⊤ → H i = H j}

/-- Only nonempty intersections enter the exceptional family. In particular,
empty or parallel pairs do not impose spurious low-dimensional rank bounds. -/
abbrev ExceptionalPlanePair {ι : Type*} (H : ι → AffineSubspace ℝ E) :=
  {ij : ι × ι // H ij.1 ≠ ⊤ ∧ H ij.2 ≠ ⊤ ∧ H ij.1 ≠ H ij.2 ∧
    (H ij.1 ⊓ H ij.2 : Set E).Nonempty}

theorem genericPlanePoints_eq_avoid {ι : Type*} (H : ι → AffineSubspace ℝ E) :
    genericPlanePoints H =
      Set.univ \ ⋃ ij : ExceptionalPlanePair H, (H ij.1.1 ⊓ H ij.1.2 : Set E) := by
  classical
  ext x
  simp only [genericPlanePoints, Set.mem_setOf_eq, Set.mem_diff, Set.mem_univ,
    true_and, Set.mem_iUnion, SetLike.mem_coe, not_exists]
  constructor
  · intro hx ij hij
    exact ij.2.2.2.1 (hx _ _ hij.1 hij.2 ij.2.1 ij.2.2.1)
  · intro hx i j hi hj hit hjt
    by_contra hne
    exact hx ⟨(i,j), hit, hjt, hne, ⟨x,hi,hj⟩⟩ ⟨hi,hj⟩

/-- The remaining points of an arrangement are path connected and dense.
Empty and all-space members are explicitly allowed. -/
theorem genericPlanePoints_pathConnected_dense [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (H : ι → AffineSubspace ℝ E)
    (hH : ∀ i, H i = ⊥ ∨ H i = ⊤ ∨
      Module.finrank ℝ (H i).direction + 1 = Module.finrank ℝ E) :
    IsPathConnected (genericPlanePoints H) ∧ Dense (genericPlanePoints H) := by
  classical
  let L : ExceptionalPlanePair H → AffineSubspace ℝ E := fun ij => H ij.1.1 ⊓ H ij.1.2
  have hL : ∀ ij, Module.finrank ℝ (L ij).direction + 2 ≤ Module.finrank ℝ E := by
    intro ij
    have hi : H ij.1.1 ≠ ⊥ := by
      intro he; obtain ⟨x,hx⟩ := ij.2.2.2.2; simpa [he] using hx.1
    have hj : H ij.1.2 ≠ ⊥ := by
      intro he; obtain ⟨x,hx⟩ := ij.2.2.2.2; simpa [he] using hx.2
    exact affineHyperplanes_inf_codimension_two ij.2.2.2.2
      ((hH _).resolve_left hi |>.resolve_left ij.2.1)
      ((hH _).resolve_left hj |>.resolve_left ij.2.2.1) ij.2.2.2.1
  rw [genericPlanePoints_eq_avoid]
  refine ⟨isPathConnected_diff_affineSubspaces isOpen_univ convex_univ
    Set.univ_nonempty L hL, ?_⟩
  have hd := affineSubspaces_dense_avoid L
    (fun ij => affineSubspace_ne_top_of_codim_two (L ij) (hL ij))
  convert hd using 1
  ext x
  simp only [Set.mem_diff, Set.mem_univ, true_and, Set.mem_iUnion, not_exists,
    Set.mem_setOf_eq, SetLike.mem_coe, L]
  rfl

/-- Every generic point either has only redundant active equations or selects
one active hyperplane contained in every active equation plane. -/
theorem genericPlanePoint_selects_hyperplane [FiniteDimensional ℝ E]
    {ι : Type*} (H : ι → AffineSubspace ℝ E)
    (hH : ∀ i, H i = ⊥ ∨ H i = ⊤ ∨
      Module.finrank ℝ (H i).direction + 1 = Module.finrank ℝ E)
    {x : E} (hx : x ∈ genericPlanePoints H) :
    (∀ i, x ∈ H i → H i = ⊤) ∨
      ∃ R : AffineSubspace ℝ E, x ∈ R ∧
        Module.finrank ℝ R.direction + 1 = Module.finrank ℝ E ∧
        ∀ i, x ∈ H i → R ≤ H i := by
  classical
  by_cases hall : ∀ i, x ∈ H i → H i = ⊤
  · exact Or.inl hall
  push_neg at hall
  obtain ⟨j,hj,hjt⟩ := hall
  have hjb : H j ≠ ⊥ :=
    (AffineSubspace.nonempty_iff_ne_bot (H j)).mp ⟨x, hj⟩
  right
  refine ⟨H j, hj, (hH j).resolve_left hjb |>.resolve_left hjt, ?_⟩
  intro i hi
  by_cases hit : H i = ⊤
  · rw [hit]; exact le_top
  · exact le_of_eq (hx j i hj hi hjt hit)


/-- The same avoidance statement on any nonempty open convex chart domain. -/
theorem genericPlanePoints_inter_open_pathConnected_dense [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (H : ι → AffineSubspace ℝ E)
    (hH : ∀ i, H i = ⊥ ∨ H i = ⊤ ∨
      Module.finrank ℝ (H i).direction + 1 = Module.finrank ℝ E)
    {O : Set E} (hO : IsOpen O) (hconv : Convex ℝ O) (hne : O.Nonempty) :
    IsPathConnected (O ∩ genericPlanePoints H) ∧
      closure (O ∩ genericPlanePoints H) = closure O := by
  classical
  let L : ExceptionalPlanePair H → AffineSubspace ℝ E := fun ij => H ij.1.1 ⊓ H ij.1.2
  have hL : ∀ ij, Module.finrank ℝ (L ij).direction + 2 ≤ Module.finrank ℝ E := by
    intro ij
    have hi : H ij.1.1 ≠ ⊥ := by
      intro he; obtain ⟨x,hx⟩ := ij.2.2.2.2; simpa [he] using hx.1
    have hj : H ij.1.2 ≠ ⊥ := by
      intro he; obtain ⟨x,hx⟩ := ij.2.2.2.2; simpa [he] using hx.2
    exact affineHyperplanes_inf_codimension_two ij.2.2.2.2
      ((hH _).resolve_left hi |>.resolve_left ij.2.1)
      ((hH _).resolve_left hj |>.resolve_left ij.2.2.1) ij.2.2.2.1
  have heq : O ∩ genericPlanePoints H = O \ ⋃ ij, (L ij : Set E) := by
    rw [genericPlanePoints_eq_avoid]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_univ, true_and, L]
    rfl
  rw [heq]
  exact affineAvoidance_pathConnected_dense hO hconv hne L hL

/-- Face-relative generic-point bridge for a fixed countable (in particular finite)
family of affine equations. No ridge is supplied as a hypothesis: each surviving
point either has only equations containing the whole face or selects a genuine
ambient codimension-two ridge contained in every active equation plane.

The open convex patch is an ambient convex set with relatively open preimage in
`P`. The output topology and density are intrinsic to the face. -/
theorem exists_genericFacePoints [FiniteDimensional ℝ E]
    {ι : Type*} [Countable ι] (P : AffineSubspace ℝ E)
    (hP : (P : Set E).Nonempty)
    (hcodim : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ E)
    (f : ι → E →ᵃ[ℝ] ℝ) (c : ι → ℝ)
    (O : Set E) (hO : IsOpen (Subtype.val ⁻¹' O : Set P))
    (hconv : Convex ℝ O) (hne : (Subtype.val ⁻¹' O : Set P).Nonempty) :
    ∃ G : Set P, G ⊆ Subtype.val ⁻¹' O ∧ IsPathConnected G ∧
      closure G = closure (Subtype.val ⁻¹' O : Set P) ∧
      ∀ x ∈ G,
        (∀ i, f i x = c i → P ≤ affineFormPlane (f i) (c i)) ∨
        ∃ R : AffineSubspace ℝ E, (x : E) ∈ R ∧ R ≤ P ∧
          Module.finrank ℝ R.direction + 2 = Module.finrank ℝ E ∧
          ∀ i, f i x = c i → R ≤ affineFormPlane (f i) (c i) := by
  classical
  letI : Nonempty P := hP.to_subtype
  let p : P := Classical.choice inferInstance
  let e : P.direction ≃ᵃⁱ[ℝ] P := AffineIsometryEquiv.vaddConst ℝ p
  let F : P.direction →ᵃ[ℝ] E := P.subtype.comp e.toAffineMap
  let H : ι → AffineSubspace ℝ P.direction := fun i =>
    affineFormPlane ((f i).comp F) (c i)
  let U : Set P.direction := e ⁻¹' (Subtype.val ⁻¹' O : Set P)
  have hH : ∀ i, H i = ⊥ ∨ H i = ⊤ ∨
      Module.finrank ℝ (H i).direction + 1 = Module.finrank ℝ P.direction :=
    fun i => affineFormPlane_trichotomy ((f i).comp F) (c i)
  have hUopen : IsOpen U := hO.preimage e.continuous
  have hUconv : Convex ℝ U := hconv.affine_preimage F
  have hUne : U.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    exact ⟨e.symm x, by simpa [U] using hx⟩
  obtain ⟨hpath,hclosure⟩ :=
    genericPlanePoints_inter_open_pathConnected_dense H hH hUopen hUconv hUne
  let G : Set P := e '' (U ∩ genericPlanePoints H)
  refine ⟨G, ?_, hpath.image e.continuous, ?_, ?_⟩
  · rintro x ⟨v,hv,rfl⟩
    exact hv.1
  · change closure (e.toHomeomorph '' (U ∩ genericPlanePoints H)) = _
    rw [← e.toHomeomorph.image_closure, hclosure]
    rw [e.toHomeomorph.image_closure]
    change closure (e '' (e ⁻¹' (Subtype.val ⁻¹' O : Set P))) = _
    rw [e.surjective.image_preimage]
  · rintro x ⟨v,hv,rfl⟩
    rcases genericPlanePoint_selects_hyperplane H hH hv.2 with hall | ⟨S,hvS,hS,ha⟩
    · left
      intro i hi y hy
      apply (mem_affineFormPlane (f i) (c i) y).mpr
      have hactive : v ∈ H i := (mem_affineFormPlane _ _ _).mpr hi
      have hmem : e.symm ⟨y,hy⟩ ∈ H i := by
        rw [hall i hactive]
        exact mem_top _ _ _
      have heq := (mem_affineFormPlane _ _ _).mp hmem
      simpa [F] using heq
    · right
      have hFinj : Function.Injective F := Subtype.val_injective.comp e.injective
      have hrank : Module.finrank ℝ (S.map F).direction =
          Module.finrank ℝ S.direction := by
        rw [map_direction]
        exact (S.direction.equivMapOfInjective F.linear
          (F.linear_injective_iff.mpr hFinj)).finrank_eq.symm
      refine ⟨S.map F, mem_map.mpr ⟨v,hvS,rfl⟩, ?_, ?_, ?_⟩
      · rintro y ⟨w,hw,rfl⟩
        exact (e w).property
      · omega
      · intro i hi y hy
        rcases mem_map.mp hy with ⟨w,hw,rfl⟩
        apply (mem_affineFormPlane _ _ _).mpr
        exact (mem_affineFormPlane _ _ _).mp
          (ha i ((mem_affineFormPlane _ _ _).mpr hi) hw)

#print axioms affineFormPlane_trichotomy
#print axioms genericPlanePoints_pathConnected_dense
#print axioms genericPlanePoint_selects_hyperplane
#print axioms genericPlanePoints_inter_open_pathConnected_dense
#print axioms exists_genericFacePoints

end SparseMonotiles
