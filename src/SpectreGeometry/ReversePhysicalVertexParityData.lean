module

public import SpectreGeometry.ReversePhysicalClusterData

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

def pointEvenCheck (p : ExactPoint) : Bool :=
  p.1.1 % 2 == 0 && p.1.2 % 2 == 0 && p.2.1 % 2 == 0 && p.2.2 % 2 == 0

/-- Exact parity of all stored physical vertex coordinates. -/
theorem vertexPairs_even_check : ∀ big : Bool,
    (vertexPairs big).all (fun q => pointEvenCheck q.2) = true := by
  intro big
  cases big <;> decide

end SpectreGeometry.ReversePhysicalCluster
