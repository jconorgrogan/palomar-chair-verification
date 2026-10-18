module

public import ProductClosure.RetainedCore
public import ProductClosure.NativeAssembly

@[expose] public section

namespace ProductClosure.NativeCompiler
open Set
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}

/-- A chosen occupied cell center, used only to witness the proved uniform ball.
The only input is actual nonemptiness of the finite occupied set. -/
def referencePoint (S : Finset (Polycube.LatticeIndex (m+1)))
    [Nonempty (Polycube.Cell S)] : Space m :=
  cellCenter (Classical.choice (inferInstance : Nonempty (Polycube.Cell S)))

theorem referencePoint_ball_subset_interior_body {J : ℕ} [NeZero m]
    [Nonempty (Polycube.Cell S)] (a : Coefficients S J) :
    Metric.ball (referencePoint S) (1/4) ⊆ interior (body a) :=
  cellCenter_ball_subset_interior_body a _

end
end ProductClosure.NativeCompiler
