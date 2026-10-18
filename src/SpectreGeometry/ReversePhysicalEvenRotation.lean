module

public import SpectreGeometry.ReversePhysicalClusterPathsData
public import SpectreGeometry.ReversePhysicalClusterReal

@[expose] public section


namespace SpectreGeometry.ReversePhysicalCluster
noncomputable section

private theorem complexMulExact_add_self (p q : ExactPoint) :
    complexMulExact p (ExactPoint.add q q) =
      ExactPoint.add (complexMulExact p q) (complexMulExact p q) := by
  ext <;> simp only [complexMulExact,ExactPoint.add,Quad3.add,Quad3.sub,Quad3.mul] <;> ring

private theorem halfExactPoint_add_self (p : ExactPoint) :
    halfExactPoint (ExactPoint.add p p) = p := by
  ext <;> simp [halfExactPoint,ExactPoint.add,Quad3.add,←two_mul]

/-- No truncation occurs when the exact input is a doubled point. -/
theorem physicalRotate4_double_eval (r : Fin 6) (q : ExactPoint) :
    quarterPoint (physicalRotate4 r (ExactPoint.add q q)) =
      SpectreGeometry.rotate (physicalRootTurn r) (quarterPoint (ExactPoint.add q q)) := by
  rw [physicalRotate4,complexMulExact_add_self,halfExactPoint_add_self]
  ext <;> simp only [quarterPoint,ExactPoint.eval,complexMulExact,ExactPoint.add,
    Quad3.eval_add,Quad3.eval_sub,Quad3.eval_mul,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,SpectreGeometry.rotate,complexMulReal,
    realDirection,realize] <;> ring

def ExactPointEven (p : ExactPoint) : Prop :=
  p.1.1 % 2 = 0 ∧ p.1.2 % 2 = 0 ∧ p.2.1 % 2 = 0 ∧ p.2.2 % 2 = 0
instance (p : ExactPoint) : Decidable (ExactPointEven p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem even_point_eq_double (p : ExactPoint) (hp : ExactPointEven p) :
    p = ExactPoint.add (halfExactPoint p) (halfExactPoint p) := by
  rcases hp with ⟨h1,h2,h3,h4⟩
  ext <;> simp only [halfExactPoint,ExactPoint.add,Quad3.add] <;> omega

theorem physicalRotate4_even_eval (r : Fin 6) (p : ExactPoint) (hp : ExactPointEven p) :
    quarterPoint (physicalRotate4 r p) =
      SpectreGeometry.rotate (physicalRootTurn r) (quarterPoint p) := by
  rw [even_point_eq_double p hp]
  exact physicalRotate4_double_eval r _

end
end SpectreGeometry.ReversePhysicalCluster
