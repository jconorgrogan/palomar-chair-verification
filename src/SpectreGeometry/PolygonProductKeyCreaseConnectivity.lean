module

public import SpectreGeometry.PolygonProductKeyBranches
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section


/-!
# Connectedness of the actual optimized 4D product-key crease complex

The pieces here are the actual max-min graph pieces defined in
`PolygonProductKeyBranches`. Their convexity, a common apex, and explicit footprint
vertices supply all incidence facts used in the connectedness proof.
-/

namespace SpectreGeometry.ProductCrease
open SpectreGeometry PhysicalRegistration
open scoped InnerProductSpace
open Set
noncomputable section

def normalCoord (u : ProductKeySite) (x : EFour) : ℝ :=
  inner ℝ (productKeyOutwardNormal u) (x-productKeyCenter u)
def tangentCoord (u : ProductKeySite) (x : EFour) (i : Fin 3) : ℝ :=
  inner ℝ (productKeyTangent u i) (x-productKeyCenter u)
private theorem tangentCoord_eq (u : ProductKeySite) (x : EFour) (i : Fin 3) :
    tangentCoord u x i = inner ℝ (productKeyTangent u i) (x-productKeyCenter u) := rfl
def baseCrease (u : ProductKeySite) (s : ProductKeySide) : Set EFour :=
  productKeySideFace u s ∩ {x | normalCoord u x = 0}
def sideCrease (u : ProductKeySite) (s t : ProductKeySide) : Set EFour :=
  productKeySideFace u s ∩ productKeySideFace u t
def creaseComplex (u : ProductKeySite) : Set EFour :=
  (⋃ s, baseCrease u s) ∪ (⋃ s, ⋃ t : {t : ProductKeySide // s.1 ≠ t.1}, sideCrease u s t.val)
private theorem eta_pos : 0 < productKeyEta := by norm_num [productKeyEta]
private theorem prime_pos (i : Fin 3) (b : Bool) : 0 < (productKeyPrime i b : ℝ) := by
  linarith [(product_key_prime_bounds i b).1]

private theorem centered_combination (u : ProductKeySite) (x y : EFour)
    (r q : ℝ) (hrq : r + q = 1) :
    r • x + q • y - productKeyCenter u =
      r • (x - productKeyCenter u) + q • (y - productKeyCenter u) := by
  rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hrq, one_smul]

theorem normalCoord_combination (u : ProductKeySite) (x y : EFour)
    (r q : ℝ) (hrq : r + q = 1) :
    normalCoord u (r • x + q • y) = r * normalCoord u x + q * normalCoord u y := by
  simp only [normalCoord, centered_combination u x y r q hrq,
    inner_add_right, real_inner_smul_right]

theorem tangentCoord_combination (u : ProductKeySite) (x y : EFour)
    (r q : ℝ) (hrq : r + q = 1) (i : Fin 3) :
    tangentCoord u (r • x + q • y) i =
      r * tangentCoord u x i + q * tangentCoord u y i := by
  simp only [tangentCoord, centered_combination u x y r q hrq,
    inner_add_right, real_inner_smul_right]

theorem branchProfile_combination (u : ProductKeySite) (s : ProductKeySide)
    (x y : EFour) (r q : ℝ) (hrq : r + q = 1) :
    productKeyBranchProfile u s (r • x + q • y) =
      r * productKeyBranchProfile u s x + q * productKeyBranchProfile u s y := by
  unfold productKeyBranchProfile
  change _ = _
  simp only [← tangentCoord_eq] at *
  rw [tangentCoord_combination u x y r q hrq]
  have hq : q = 1 - r := by linarith
  rw [hq]
  ring

theorem sideHeight_combination (u : ProductKeySite)
    (s : ProductKeySide) (x y : EFour) (r q : ℝ) (hrq : r + q = 1) :
    productKeySideHeight u s (r • x + q • y) =
      r * productKeySideHeight u s x + q * productKeySideHeight u s y := by
  unfold productKeySideHeight
  change _ = _
  simp only [← tangentCoord_eq] at *
  rw [tangentCoord_combination u x y r q hrq]
  have hq : q = 1 - r := by linarith
  rw [hq]
  ring

theorem branchRegion_convex (u : ProductKeySite) (s : ProductKeySide) :
    Convex ℝ (productKeyBranchRegion u s) := by
  intro x hx y hy r q hr hq hrq
  constructor
  · rw [branchProfile_combination u s x y r q hrq]
    exact add_nonneg (mul_nonneg hr hx.1) (mul_nonneg hq hy.1)
  · intro t
    rw [branchProfile_combination u s x y r q hrq,
      branchProfile_combination u t x y r q hrq]
    exact add_le_add (mul_le_mul_of_nonneg_left (hx.2 t) hr)
      (mul_le_mul_of_nonneg_left (hy.2 t) hq)

theorem sideFace_convex (u : ProductKeySite) (s : ProductKeySide) :
    Convex ℝ (productKeySideFace u s) := by
  intro x hx y hy r q hr hq hrq
  have hreg := branchRegion_convex u s hx.2 hy.2 hr hq hrq
  refine ⟨?_, hreg⟩
  change normalCoord u (r • x + q • y) = _
  rw [product_key_height_eq_side_height u s _ hreg,
    normalCoord_combination u x y r q hrq,
    sideHeight_combination u s x y r q hrq]
  have hxx : normalCoord u x = productKeySideHeight u s x :=
    hx.1.trans (product_key_height_eq_side_height u s x hx.2)
  have hyy : normalCoord u y = productKeySideHeight u s y :=
    hy.1.trans (product_key_height_eq_side_height u s y hy.2)
  rw [hxx,hyy]

theorem baseCrease_convex 
    (u : ProductKeySite) (s : ProductKeySide) : Convex ℝ (baseCrease u s) := by
  apply (sideFace_convex u s).inter
  intro x hx y hy r q _ _ hrq
  change normalCoord u (r • x + q • y) = 0
  rw [normalCoord_combination u x y r q hrq, hx, hy]
  simp

theorem sideCrease_convex 
    (u : ProductKeySite) (s t : ProductKeySide) : Convex ℝ (sideCrease u s t) :=
  (sideFace_convex u s).inter (sideFace_convex u t)

/-- The ambient point with the supplied native tangent and normal coordinates. -/
def keyCoordinatePoint (u : ProductKeySite) (v : Fin 3 → ℝ) (z : ℝ) : EFour :=
  productKeyCenter u + (∑ i, v i • productKeyTangent u i) + z • productKeyOutwardNormal u

@[simp] theorem keyCoordinatePoint_normal (u : ProductKeySite)
    (v : Fin 3 → ℝ) (z : ℝ) : normalCoord u (keyCoordinatePoint u v z) = z := by
  have horth : ∀ i, ⟪productKeyOutwardNormal u, productKeyTangent u i⟫_ℝ = 0 := by
    intro i
    exact productKeyOutwardNormal_inner_tangent u i
  have hsub : keyCoordinatePoint u v z - productKeyCenter u =
      (∑ i, v i • productKeyTangent u i) + z • productKeyOutwardNormal u := by
    unfold keyCoordinatePoint
    abel
  simp [normalCoord, hsub, inner_add_right, inner_sum,
    real_inner_smul_right, horth, real_inner_self_eq_norm_sq, productKeyOutwardNormal_norm]

@[simp] theorem keyCoordinatePoint_tangent (u : ProductKeySite)
    (v : Fin 3 → ℝ) (z : ℝ) (i : Fin 3) :
    tangentCoord u (keyCoordinatePoint u v z) i = v i := by
  have hsub : keyCoordinatePoint u v z - productKeyCenter u =
      (∑ j, v j • productKeyTangent u j) + z • productKeyOutwardNormal u := by
    unfold keyCoordinatePoint
    abel
  have horth : inner ℝ (productKeyTangent u i) (productKeyOutwardNormal u) = 0 := by
    rw [real_inner_comm]
    exact productKeyOutwardNormal_inner_tangent u i
  simp [tangentCoord, hsub, inner_add_right, inner_sum,
    real_inner_smul_right, productKeyTangent_inner,horth]

/-- The actual signed apex, valid for either sign of the nonzero coefficient. -/
def keyApex (u : ProductKeySite) : EFour :=
  keyCoordinatePoint u (fun _ => 0) (productKeyEta * (productKeySignedLabel u : ℝ) / productKeyN)

theorem keyApex_mem_sideFace (u : ProductKeySite) (s : ProductKeySide) :
    keyApex u ∈ productKeySideFace u s := by
  have hp : ∀ t : ProductKeySide, productKeyBranchProfile u t (keyApex u) = 1 := by
    intro t
    simp [keyApex, productKeyBranchProfile, ← tangentCoord_eq]
  have hreg : keyApex u ∈ productKeyBranchRegion u s :=
    ⟨by rw [hp]; norm_num, fun t => by rw [hp,hp]⟩
  refine ⟨?_,hreg⟩
  change normalCoord u (keyApex u) = _
  rw [product_key_height_eq_side_height u s _ hreg]
  simp [productKeySideHeight,keyApex,← tangentCoord_eq]

/-- A selected signed endpoint of a native footprint interval. -/
def sideEndpoint (s : ProductKeySide) : ℝ :=
  if s.2 then productKeyEta / (productKeyPrime s.1 true : ℝ) else -productKeyEta / (productKeyPrime s.1 false : ℝ)

/-- An explicit footprint vertex on the chosen side. Other axes use their
negative endpoints, so every distinct axis supplies an incident side crease. -/
def keyBaseVertex (u : ProductKeySite) (s : ProductKeySide) : EFour :=
  keyCoordinatePoint u
    (fun i => if i = s.1 then sideEndpoint s else -productKeyEta / (productKeyPrime i false : ℝ)) 0

theorem keyBaseVertex_footprint (u : ProductKeySite) (s : ProductKeySide) (i : Fin 3) :
    -productKeyEta/(productKeyPrime i false : ℝ) ≤ tangentCoord u (keyBaseVertex u s) i ∧
    tangentCoord u (keyBaseVertex u s) i ≤ productKeyEta/(productKeyPrime i true : ℝ) := by
  simp only [keyBaseVertex,keyCoordinatePoint_tangent]
  have hlo : -productKeyEta/(productKeyPrime i false : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr eta_pos.le) (prime_pos i false).le
  have hhi : 0 ≤ productKeyEta/(productKeyPrime i true : ℝ) :=
    div_nonneg eta_pos.le (prime_pos i true).le
  by_cases hi : i = s.1
  · subst i
    simp only [ite_true,sideEndpoint]
    split_ifs <;> exact ⟨by first | exact hlo.trans hhi | rfl,
      by first | exact hlo.trans hhi | rfl⟩
  · simp only [hi,ite_false]
    exact ⟨le_rfl,hlo.trans hhi⟩

theorem keyBaseVertex_profile_nonneg (u : ProductKeySite) (s t : ProductKeySide) :
    0 ≤ productKeyBranchProfile u t (keyBaseVertex u s) := by
  have hf := keyBaseVertex_footprint u s t.1
  have hp := prime_pos t.1 t.2
  unfold productKeyBranchProfile
  change 0 ≤ 1 + (if t.2 then -1 else 1) * (productKeyPrime t.1 t.2 : ℝ) *
    tangentCoord u (keyBaseVertex u s) t.1 / productKeyEta
  cases ht : t.2
  · simp only [ht, Bool.false_eq_true, ite_false,one_mul]
    have h := (div_le_iff₀ (prime_pos t.1 false)).mp hf.1
    have hh : -1 ≤ (productKeyPrime t.1 false : ℝ) * tangentCoord u (keyBaseVertex u s) t.1 / productKeyEta :=
      (le_div_iff₀ eta_pos).mpr (by nlinarith)
    linarith
  · simp only [ht,ite_true,neg_one_mul]
    have h := (le_div_iff₀ (prime_pos t.1 true)).mp hf.2
    have hh : -1 ≤ -(productKeyPrime t.1 true : ℝ) * tangentCoord u (keyBaseVertex u s) t.1 / productKeyEta :=
      (le_div_iff₀ eta_pos).mpr (by nlinarith)
    linarith

theorem keyBaseVertex_branch_zero (u : ProductKeySite) (s : ProductKeySide) :
    productKeyBranchProfile u s (keyBaseVertex u s) = 0 := by
  rcases s with ⟨i,b⟩
  cases b <;> simp [productKeyBranchProfile,← tangentCoord_eq,keyBaseVertex,sideEndpoint,
    eta_pos.ne',(prime_pos i false).ne',(prime_pos i true).ne'] <;>
    field_simp [eta_pos.ne',(prime_pos i false).ne',(prime_pos i true).ne'] <;> ring

theorem keyBaseVertex_other_branch_zero (u : ProductKeySite) (s : ProductKeySide)
    (j : Fin 3) (hj : j ≠ s.1) :
    productKeyBranchProfile u (j,false) (keyBaseVertex u s) = 0 := by
  simp [productKeyBranchProfile,← tangentCoord_eq,keyBaseVertex,hj,
    eta_pos.ne',(prime_pos j false).ne']
  field_simp [eta_pos.ne',(prime_pos j false).ne']
  norm_num

/-- A zero active branch on the zero-height footprint is a literal base crease. -/
theorem mem_baseCrease_of_branch_zero (u : ProductKeySite) (s : ProductKeySide)
    (x : EFour) (hn : normalCoord u x = 0)
    (hp : productKeyBranchProfile u s x = 0)
    (hall : ∀ t, 0 ≤ productKeyBranchProfile u t x) : x ∈ baseCrease u s := by
  have hreg : x ∈ productKeyBranchRegion u s := by
    exact ⟨by rw [hp],fun t => by rw [hp]; exact hall t⟩
  refine ⟨⟨?_,hreg⟩,hn⟩
  change normalCoord u x = _
  rw [hn]
  unfold productKeyHeight keyHeight
  rw [product_key_profile_eq_branch u s x hreg,hp,mul_zero]

theorem keyBaseVertex_mem_baseCrease (u : ProductKeySite) (s : ProductKeySide) :
    keyBaseVertex u s ∈ baseCrease u s :=
  mem_baseCrease_of_branch_zero u s _ (by simp [keyBaseVertex])
    (keyBaseVertex_branch_zero u s) (keyBaseVertex_profile_nonneg u s)

theorem keyBaseVertex_mem_other_baseCrease (u : ProductKeySite) (s : ProductKeySide)
    (j : Fin 3) (hj : j ≠ s.1) : keyBaseVertex u s ∈ baseCrease u (j,false) :=
  mem_baseCrease_of_branch_zero u (j,false) _ (by simp [keyBaseVertex])
    (keyBaseVertex_other_branch_zero u s j hj) (keyBaseVertex_profile_nonneg u s)

theorem baseCrease_nonempty 
    (u : ProductKeySite) (s : ProductKeySide) : (baseCrease u s).Nonempty :=
  ⟨keyBaseVertex u s, keyBaseVertex_mem_baseCrease u s⟩

theorem sideCrease_nonempty 
    (u : ProductKeySite) (s t : ProductKeySide) : (sideCrease u s t).Nonempty :=
  ⟨keyApex u, keyApex_mem_sideFace u s, keyApex_mem_sideFace u t⟩

theorem baseCrease_isConnected 
    (u : ProductKeySite) (s : ProductKeySide) : IsConnected (baseCrease u s) :=
  (baseCrease_convex u s).isConnected (baseCrease_nonempty u s)

theorem sideCrease_isConnected 
    (u : ProductKeySite) (s t : ProductKeySide) : IsConnected (sideCrease u s t) :=
  (sideCrease_convex u s t).isConnected (sideCrease_nonempty u s t)

/-- Every base face meets a genuine distinct-axis side crease, at a concrete
footprint vertex. No graph-incidence premise is supplied. -/
theorem baseCrease_meets_sideCrease 
    (u : ProductKeySite) (s : ProductKeySide) (j : Fin 3) (hj : j ≠ s.1) :
    (baseCrease u s ∩ sideCrease u s (j, false)).Nonempty := by
  exact ⟨keyBaseVertex u s, keyBaseVertex_mem_baseCrease u s,
    (keyBaseVertex_mem_baseCrease u s).1,
    (keyBaseVertex_mem_other_baseCrease u s j hj).1⟩


theorem baseCrease_subset_creaseComplex 
    (u : ProductKeySite) (s : ProductKeySide) : baseCrease u s ⊆ creaseComplex u := by
  intro x hx
  exact Or.inl (mem_iUnion.mpr ⟨s, hx⟩)

theorem sideCrease_subset_creaseComplex 
    (u : ProductKeySite) (s t : ProductKeySide) (hst : s.1 ≠ t.1) :
    sideCrease u s t ⊆ creaseComplex u := by
  intro x hx
  exact Or.inr (mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨⟨t, hst⟩, hx⟩⟩)

theorem creaseComplex_nonempty 
    (u : ProductKeySite) : (creaseComplex u).Nonempty := by
  let s : ProductKeySide := (0, false)
  exact (baseCrease_nonempty u s).mono (baseCrease_subset_creaseComplex u s)

private theorem exists_other_axis (i : Fin 3) :
    ∃ j : Fin 3, j ≠ i := by
  by_cases hi : i.val = 0
  · refine ⟨⟨1, by omega⟩, ?_⟩
    intro h
    have := congrArg Fin.val h
    simp [hi] at this
  · refine ⟨⟨0, by omega⟩, ?_⟩
    intro h
    apply hi
    exact (congrArg Fin.val h).symm

/-- All native closed crease pieces are connected through their computed
incidences: side creases contain the apex and base creases meet side creases. -/
theorem creaseComplex_isPreconnected 
    (u : ProductKeySite) : IsPreconnected (creaseComplex u) := by
  apply isPreconnected_of_forall (keyApex u)
  intro y hy
  rcases hy with hy | hy
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
    obtain ⟨j, hj⟩ := exists_other_axis s.1
    let t : ProductKeySide := (j, false)
    refine ⟨baseCrease u s ∪ sideCrease u s t, ?_, ?_, Or.inl hs, ?_⟩
    · exact union_subset (baseCrease_subset_creaseComplex u s)
        (sideCrease_subset_creaseComplex u s t (Ne.symm hj))
    · exact Or.inr ⟨keyApex_mem_sideFace u s, keyApex_mem_sideFace u t⟩
    · exact (baseCrease_isConnected u s).isPreconnected.union'
        (baseCrease_meets_sideCrease u s j hj)
        (sideCrease_isConnected u s t).isPreconnected
  · obtain ⟨s, hs⟩ := mem_iUnion.mp hy
    obtain ⟨t, ht⟩ := mem_iUnion.mp hs
    exact ⟨sideCrease u s t.val,
      sideCrease_subset_creaseComplex u s t.val t.property,
      ⟨keyApex_mem_sideFace u s, keyApex_mem_sideFace u t.val⟩,
      ht, (sideCrease_isConnected u s t.val).isPreconnected⟩

/-- The actual native key crease complex is nonempty and connected for each actual 4D recipe site, with no connectivity or incidence hypothesis. -/
theorem creaseComplex_isConnected 
    (u : ProductKeySite) : IsConnected (creaseComplex u) :=
  ⟨creaseComplex_nonempty u, creaseComplex_isPreconnected u⟩


end
end SpectreGeometry.ProductCrease
