module

public import SpectreGeometry.ReverseClusterNeighborCellsCertificates

@[expose] public section


/-! Sound center-box pruning for the same finite interface certificate. -/
namespace SpectreGeometry.ReverseClusterNeighborCells
open SpectreClusters

def centerNear (a b : Cell) : Prop :=
  -2 ≤ b.center.1-a.center.1 ∧ b.center.1-a.center.1 ≤ 2 ∧
  -2 ≤ b.center.2-a.center.2 ∧ b.center.2-a.center.2 ≤ 2
instance (a b : Cell) : Decidable (centerNear a b) := by
  unfold centerNear
  infer_instance

def cellPairFastB (path : List Point) (a b : Cell) : Bool :=
  if centerNear a b then cellPairCheckedB path a b else decide (a ≠ b)

def configurationFastB (c : Configuration) : Bool :=
  decide (pathEdges c.sharedPath ≠ []) &&
    (rootCells c).all fun a => (neighborCells c).all (cellPairFastB c.sharedPath a)

theorem cellPairCheckedB_complete (path : List Point) (a b : Cell)
    (hne : a ≠ b) (edge : Point × Point) (he : edge ∈ pathEdges path)
    (hs : ∀ v ∈ cellVertices a, v ∈ cellVertices b → v = edge.1 ∨ v = edge.2) :
    cellPairCheckedB path a b = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hne,List.any_eq_true.mpr ⟨edge,he,?_⟩⟩
  apply List.all_eq_true.mpr
  intro v hv
  apply decide_eq_true
  by_cases hb : v ∈ cellVertices b
  · exact Or.inr (hs v hv hb)
  · exact Or.inl hb

theorem cellPairFastB_sound (path : List Point) (hpath : pathEdges path ≠ [])
    (a b : Cell) (hfast : cellPairFastB path a b = true) :
    cellPairCheckedB path a b = true := by
  by_cases hn : centerNear a b
  · simpa [cellPairFastB,hn] using hfast
  have hne : a ≠ b := of_decide_eq_true (by simpa [cellPairFastB,hn] using hfast)
  obtain ⟨edge,he⟩ := List.exists_mem_of_ne_nil _ hpath
  apply cellPairCheckedB_complete path a b hne edge he
  intro v hva hvb
  exact (hn (contact_center_bounds a b ⟨v,hva,hvb⟩)).elim

theorem configurationFastB_sound (c : Configuration)
    (hc : configurationFastB c = true) : configurationCheckedB c = true := by
  have h := Bool.and_eq_true_iff.mp hc
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact cellPairFastB_sound c.sharedPath (of_decide_eq_true h.1) a b
    (List.all_eq_true.mp (List.all_eq_true.mp h.2 a ha) b hb)

end SpectreGeometry.ReverseClusterNeighborCells
