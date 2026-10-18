module

public import SpectreGeometry.ReverseClusterNeighborCellsCertificates
public import SpectreGeometry.GridKiteCommonFaces
public import SpectreGeometry.ReverseClusterTriangulationScaleReal

@[expose] public section


/-! Soundness of the finite neighboring-cluster interface certificates for the
actual unions of closed grid-kite bodies. -/
namespace SpectreGeometry.ReverseClusterNeighborCells
noncomputable section
open Set SpectreClusters ReverseClusterTriangulation

def edgeCarrier (edge : Point × Point) : Set RealPoint :=
  convexHull ℝ {integerPoint edge.1,integerPoint edge.2}

theorem edgeCarrier_eq_segment (edge : Point × Point) :
    edgeCarrier edge = segment ℝ (integerPoint edge.1) (integerPoint edge.2) :=
  convexHull_pair _ _

def pathCarrier (path : List Point) : Set RealPoint :=
  ⋃ edge ∈ pathEdges path, edgeCarrier edge

def rootCarrier (c : Configuration) : Set RealPoint :=
  ⋃ a ∈ rootCells c, gridKiteBody a

def neighborCarrier (c : Configuration) : Set RealPoint :=
  ⋃ b ∈ neighborCells c, gridKiteBody b

theorem rootCarrier_eq_rawClusterBody (c : Configuration) :
    rootCarrier c = rawClusterBody c.rootKind := rfl

private theorem integerPoint_injective : Function.Injective integerPoint := by
  intro a b h
  apply Prod.ext
  · have hh : (a.1 : ℝ) = (b.1 : ℝ) := congrArg Prod.fst h
    exact_mod_cast hh
  · have hh : (a.2 : ℝ) = (b.2 : ℝ) := congrArg Prod.snd h
    exact_mod_cast hh

theorem gridKite_inter_subset_edge (a b : Cell) (edge : Point × Point)
    (h : ∀ v ∈ cellVertices a, v ∈ cellVertices b → v = edge.1 ∨ v = edge.2) :
    gridKiteBody a ∩ gridKiteBody b ⊆ edgeCarrier edge := by
  rw [gridKiteBody_inter_commonFace]
  apply convexHull_mono
  rintro x ⟨⟨v,hva,rfl⟩,⟨w,hwb,hw⟩⟩
  have hwv : w = v := integerPoint_injective hw
  subst w
  rcases h v hva hwb with he | he
  · simp [he]
  · simp [he]

/-- Every point common to the two genuine finite closed-kite carriers lies on
one segment of their prescribed shared marked boundary path. -/
theorem configurationCheckedB_carriers_inter_subset (c : Configuration)
    (hc : configurationCheckedB c = true) :
    rootCarrier c ∩ neighborCarrier c ⊆ pathCarrier c.sharedPath := by
  rintro x ⟨hroot,hneighbor⟩
  obtain ⟨a,ha,hxa⟩ := Set.mem_iUnion₂.mp hroot
  obtain ⟨b,hb,hxb⟩ := Set.mem_iUnion₂.mp hneighbor
  obtain ⟨hne,edge,hedge,hsupport⟩ := configurationCheckedB_sound c hc a ha b hb
  exact Set.mem_iUnion₂.mpr ⟨edge,hedge,gridKite_inter_subset_edge a b edge hsupport ⟨hxa,hxb⟩⟩

/-- The packet also rules out duplicate cells and interior overlap between
any constituent kites across the interface. -/
theorem configurationCheckedB_cross_cells_disjoint (c : Configuration)
    (hc : configurationCheckedB c = true) :
    ∀ a ∈ rootCells c, ∀ b ∈ neighborCells c,
      Disjoint (interior (gridKiteBody a)) (interior (gridKiteBody b)) := by
  intro a ha b hb
  exact gridKiteBody_interior_disjoint a b (configurationCheckedB_sound c hc a ha b hb).1

end
end SpectreGeometry.ReverseClusterNeighborCells
