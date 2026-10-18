module

public import LiteralPlanar.GraphStraightening
public import Mathlib.Topology.Constructions.SumProd

@[expose] public section


/-! Actual graph windows form a local basis at every strict interior graph
point, with both connected sides kept inside any prescribed neighborhood. -/
namespace LiteralPlanar.Quintic
noncomputable section
open Set
open scoped Topology

theorem exists_graphWindow_subset (ε t lo hi : ℝ) (hlt : lo < t) (hth : t < hi)
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (htU : (t,height ε t) ∈ U) :
    ∃ a b r : ℝ, a < t ∧ t < b ∧ 0 < r ∧
      Ioo a b ⊆ Ioo lo hi ∧
      (t,height ε t) ∈ graphWindow ε a b r ∧ graphWindow ε a b r ⊆ U := by
  let V := (graphShear ε).symm ⁻¹' (U ∩ (Ioo lo hi ×ˢ (univ : Set ℝ)))
  have hV : IsOpen V := (hU.inter (isOpen_Ioo.prod isOpen_univ)).preimage
    (graphShear ε).symm.continuous
  have htV : (t,0) ∈ V := by
    change (t,0+height ε t) ∈ U ∧ (lo < t ∧ t < hi) ∧ True
    simpa only [zero_add] using And.intro htU ⟨⟨hlt,hth⟩,trivial⟩
  obtain ⟨S,hS,W,hW,hSW⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds htV)
  obtain ⟨a,b,hab,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hS
  obtain ⟨c,d,hcd,hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp hW
  let r := min (-c) d / 2
  have hr : 0 < r := by dsimp [r]; exact div_pos (lt_min (by linarith [hcd.1]) hcd.2) (by norm_num)
  have hrc : c < -r := by
    have hm := min_le_left (-c) d
    dsimp [r] at hr ⊢
    linarith
  have hrd : r < d := by
    have hm := min_le_right (-c) d
    dsimp [r] at hr ⊢
    linarith
  refine ⟨a,b,r,hab.1,hab.2,hr,?_,?_,?_⟩
  · intro u hu
    have hh := hSW (show (u,0) ∈ S ×ˢ W from ⟨hsub hu,hsub' hcd⟩)
    exact hh.2.1
  · refine ⟨(t,0),⟨hab,by constructor <;> linarith⟩,?_⟩
    change (t,0+height ε t) = (t,height ε t)
    simp
  · rintro x ⟨y,⟨hy1,hy2⟩,rfl⟩
    have hw : y.2 ∈ Ioo c d := ⟨lt_trans hrc hy2.1,lt_trans hy2.2 hrd⟩
    exact (hSW (show y ∈ S ×ˢ W from ⟨hsub hy1,hsub' hw⟩)).1

end
end LiteralPlanar.Quintic
