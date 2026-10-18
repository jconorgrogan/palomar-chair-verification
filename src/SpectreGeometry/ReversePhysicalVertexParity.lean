module

public import SpectreGeometry.ReversePhysicalVertexParityData
public import SpectreGeometry.ReversePhysicalEvenRotation

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section

theorem vertexImage4_even (big : Bool) (p : SpectreClusters.Point) :
    ExactPointEven (vertexImage4 big p) := by
  unfold vertexImage4
  cases h : (vertexPairs big).find? (fun q => q.1 == p) with
  | none => simp [ExactPointEven]
  | some q =>
    have hq := List.mem_of_find?_eq_some h
    have he := (List.all_eq_true.mp (vertexPairs_even_check big)) q hq
    simpa [pointEvenCheck, ExactPointEven, Bool.and_eq_true, and_assoc] using he

theorem physicalRotate4_vertexImage4_eval (r : Fin 6) (big : Bool)
    (p : SpectreClusters.Point) :
    quarterPoint (physicalRotate4 r (vertexImage4 big p)) =
      SpectreGeometry.rotate (physicalRootTurn r) (quarterPoint (vertexImage4 big p)) :=
  physicalRotate4_even_eval r _ (vertexImage4_even big p)

end
end SpectreGeometry.ReversePhysicalCluster
