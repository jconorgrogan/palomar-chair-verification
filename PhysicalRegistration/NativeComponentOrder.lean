module

public import PhysicalRegistration.NativeGraphCoefficients
public import Mathlib.Order.PiLex

@[expose] public section

/-! The source's native-site ordering: lexicographic facet center, outward
normal, and tangent free-orbit coordinates. The last coordinates are stored
as their integer numerators; the common denominator is strictly positive. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
open Set
open ComponentCoefficients

/-- The exact manuscript key, with q represented by its common-denominator
integer numerator in increasing native tangent-coordinate order. -/
abbrev SiteOrderKey (m : ℕ) :=
  Lex (Lex (Fin (m+1) → ℝ) × Lex (Lex (Fin (m+1) → ℝ) × Lex (Fin m → ℤ)))

def siteOrderKey {m : ℕ} (u : Site m) : SiteOrderKey m :=
  toLex (toLex (fun i => facetCenter u.1 i),
    toLex (toLex (fun i => outward u.1 i), toLex (orbitNumerator u.2)))

theorem siteCenter_mem_closedTube {m : ℕ} (J : ℕ) (u : Site m) :
    siteCenter u ∈ closedTube J u := by
  constructor
  · simp only [normalCoord_center, abs_zero]
    exact (rho_pos m).le
  · intro j
    simp only [tangentCoord_center]
    constructor
    · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (eta_pos m).le)
        (pMinus_pos J j).le
    · exact (div_pos (eta_pos m) (pPlus_pos J j)).le

theorem siteCenter_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (siteCenter (m := m)) := by
  intro u v he
  by_contra hne
  have hd := @closedTube_pairwise_disjoint m 1 hm u v hne
  have hu := siteCenter_mem_closedTube 1 u
  have hv := siteCenter_mem_closedTube 1 v
  rw [← he] at hv
  exact Set.disjoint_left.mp hd hu hv

theorem normalIndex_eq_of_outward_eq {m : ℕ} {f g : Facet m}
    (h : outward f = outward g) : normalIndex f = normalIndex g := by
  by_contra hne
  have hv : |outward f (normalIndex f)| = 1 := by
    simp [outward, PiLp.smul_apply]
  have hz : outward g (normalIndex f) = 0 := by
    simp [outward, PiLp.smul_apply, Ne.symm hne]
  rw [h, hz] at hv
  norm_num at hv

theorem siteOrderKey_injective {m : ℕ} (hm : 2 ≤ m) :
    Function.Injective (siteOrderKey (m := m)) := by
  intro u v he
  have hb : facetCenter u.1 = facetCenter v.1 := by
    ext i
    exact congrArg (fun k : SiteOrderKey m => ofLex (ofLex k).1 i) he
  have hn : outward u.1 = outward v.1 := by
    ext i
    exact congrArg (fun k : SiteOrderKey m => ofLex (ofLex (ofLex k).2).1 i) he
  have hq : orbitNumerator u.2 = orbitNumerator v.2 :=
    congrArg (fun k : SiteOrderKey m => ofLex (ofLex (ofLex k).2).2) he
  have hf := orbitNumerator_injective hq
  have hi := normalIndex_eq_of_outward_eq hn
  apply siteCenter_injective hm
  have ho : siteOffset u = siteOffset v := by
    simp only [siteOffset, siteAxis, tangentAxis]
    rw [hf, hi]
  simp only [siteCenter, hb, ho]

/-- The lexicographic site order is derived from actual native geometry. -/
@[instance_reducible] def nativeSiteOrder {m : ℕ} (hm : 2 ≤ m) : LinearOrder (Site m) :=
  LinearOrder.lift' siteOrderKey (siteOrderKey_injective hm)

/-- The literal coefficient assignment in the source's ordering, with J
computed as the number of connected components. -/
def compiledCoefficients {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g) :
    letI := nativeSiteOrder hm
    Coefficients m (count (contactGraph A hA)) := by
  letI := nativeSiteOrder hm
  exact graphCoefficients (contactGraph A hA)

/-- Replacing q by the stored numerator preserves each lexicographic
coordinate comparison because the scale is common and strictly positive. -/
theorem native_q_lt_iff_numerator_lt {m : ℕ} (u v : Site m) (j : Fin m) :
    siteOffset u ((normalIndex u.1).succAbove j) <
        siteOffset v ((normalIndex v.1).succAbove j) ↔
      orbitNumerator u.2 j < orbitNumerator v.2 j := by
  rw [siteOffset_eq_orbitNumerator, siteOffset_eq_orbitNumerator]
  rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
  exact_mod_cast Iff.rfl

/-- Every prescribed site equation holds for the completely constructed
coefficient assignment, including its geometric site ordering. -/
theorem compiledCoefficients_edge_neg {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    (compiledCoefficients hm A hA).value v = -(compiledCoefficients hm A hA).value u := by
  letI := nativeSiteOrder hm
  exact contactGraph_coefficients_satisfy_all_edges A hA h

/-- No ordering, coefficient, graph-legality, or properness certificate is
supplied by a physical tiling. Its recovered companion is proved proper and
in the same computed contact-graph component. -/
theorem PhysicalTiling.compiled_exists_proper_graph_companion
    {m : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients hm A hA) f) (root : ι) (u : Site m) :
    ∃ iv : ι × Site m, iv.1 ≠ root ∧
      f root '' creaseComplex (compiledCoefficients hm A hA) u =
        f iv.1 '' creaseComplex (compiledCoefficients hm A hA) iv.2 ∧
      IsProperPlacement (relativePlacement (f root) (f iv.1)) ∧
      (contactGraph A hA).Reachable u iv.2 := by
  letI := nativeSiteOrder hm
  exact T.exists_proper_graph_companion hm (contactGraph A hA) root u

end
end PhysicalRegistration.NativeChair
