module

public import ProductClosure.NativeTubeSeparation
public import Mathlib.Order.PiLex

@[expose] public section

namespace ProductClosure.NativeCompiler
noncomputable section
open Set
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- The exact manuscript key, with q represented by its common-denominator
integer numerator in increasing native tangent-coordinate order. -/
abbrev SiteOrderKey (m : ℕ) :=
  Lex (Lex (Fin (m+1) → ℝ) × Lex (Lex (Fin (m+1) → ℝ) × Lex (Fin m → ℤ)))

def siteOrderKey (u : Site S) : SiteOrderKey m :=
  toLex (toLex (fun i => facetCenter u.1 i),
    toLex (toLex (fun i => outward u.1 i), toLex (orbitNumerator u.2)))

theorem siteCenter_mem_closedTube (J : ℕ) (u : Site S) :
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

theorem siteCenter_injective (hm : 2 ≤ m) :
    Function.Injective (siteCenter (S := S)) := by
  intro u v he
  by_contra hne
  have hd := @closedTube_pairwise_disjoint m S 1 hm u v hne
  have hu := siteCenter_mem_closedTube 1 u
  have hv := siteCenter_mem_closedTube 1 v
  rw [← he] at hv
  exact Set.disjoint_left.mp hd hu hv

theorem normalIndex_eq_of_outward_eq {f g : Facet S}
    (h : outward f = outward g) : normalIndex f = normalIndex g := by
  by_contra hne
  have hv : |outward f (normalIndex f)| = 1 := by
    simp [outward, PiLp.smul_apply]
  have hz : outward g (normalIndex f) = 0 := by
    simp [outward, PiLp.smul_apply, Ne.symm hne]
  rw [h, hz] at hv
  norm_num at hv

theorem siteOrderKey_injective (hm : 2 ≤ m) :
    Function.Injective (siteOrderKey (S := S)) := by
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
@[instance_reducible] def nativeSiteOrder (hm : 2 ≤ m) : LinearOrder (Site S) :=
  LinearOrder.lift' siteOrderKey (siteOrderKey_injective hm)


end
end ProductClosure.NativeCompiler
