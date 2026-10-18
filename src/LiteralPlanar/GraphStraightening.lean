module

public import LiteralPlanar.QuinticArc
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section


/-! Explicit graph straightening and the two connected sides of a local
quintic-graph window. No body-frontier identification is built into this file. -/
namespace LiteralPlanar.Quintic
noncomputable section
open Set

def graphShear (ε : ℝ) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) where
  toFun p := (p.1,p.2-height ε p.1)
  invFun p := (p.1,p.2+height ε p.1)
  left_inv p := by apply Prod.ext <;> simp
  right_inv p := by apply Prod.ext <;> simp
  continuous_toFun := by
    apply Continuous.prodMk continuous_fst
    unfold height
    fun_prop
  continuous_invFun := by
    apply Continuous.prodMk continuous_fst
    unfold height
    fun_prop

def wholeGraph (ε : ℝ) : Set (ℝ × ℝ) := {p | p.2 = height ε p.1}
def graphWindow (ε a b r : ℝ) : Set (ℝ × ℝ) :=
  (graphShear ε).symm '' (Ioo a b ×ˢ Ioo (-r) r)
def graphLower (ε a b r : ℝ) : Set (ℝ × ℝ) :=
  (graphShear ε).symm '' (Ioo a b ×ˢ Ioo (-r) 0)
def graphUpper (ε a b r : ℝ) : Set (ℝ × ℝ) :=
  (graphShear ε).symm '' (Ioo a b ×ˢ Ioo 0 r)

theorem graphWindow_open (ε a b r : ℝ) : IsOpen (graphWindow ε a b r) :=
  (graphShear ε).symm.isOpenMap _ (isOpen_Ioo.prod isOpen_Ioo)

theorem graphLower_connected (ε a b r : ℝ) (hab : a < b) (hr : 0 < r) :
    IsConnected (graphLower ε a b r) :=
  ((isConnected_Ioo hab).prod (isConnected_Ioo (by linarith : -r < 0))).image _
    (graphShear ε).symm.continuous.continuousOn

theorem graphUpper_connected (ε a b r : ℝ) (hab : a < b) (hr : 0 < r) :
    IsConnected (graphUpper ε a b r) :=
  ((isConnected_Ioo hab).prod (isConnected_Ioo hr)).image _
    (graphShear ε).symm.continuous.continuousOn

theorem graphWindow_sides (ε a b r : ℝ) :
    graphWindow ε a b r \ wholeGraph ε =
      graphLower ε a b r ∪ graphUpper ε a b r := by
  ext z
  obtain ⟨p,rfl⟩ := (graphShear ε).symm.surjective z
  simp only [graphWindow,graphLower,graphUpper,mem_sdiff,mem_union,
    (graphShear ε).symm.injective.mem_set_image,mem_prod,mem_Ioo]
  have hgraph : (graphShear ε).symm p ∈ wholeGraph ε ↔ p.2 = 0 := by
    change p.2+height ε p.1=height ε p.1 ↔ p.2=0
    simp
  rw [hgraph]
  constructor
  · rintro ⟨⟨hp,hv⟩,hn⟩
    rcases lt_or_gt_of_ne hn with h | h
    · exact Or.inl ⟨hp,hv.1,h⟩
    · exact Or.inr ⟨hp,h,hv.2⟩
  · rintro (⟨hp,hv⟩ | ⟨hp,hv⟩)
    · exact ⟨⟨hp,hv.1,by linarith [hv.1,hv.2]⟩,ne_of_lt hv.2⟩
    · exact ⟨⟨hp,by linarith [hv.1,hv.2],hv.2⟩,ne_of_gt hv.1⟩

end
end LiteralPlanar.Quintic
