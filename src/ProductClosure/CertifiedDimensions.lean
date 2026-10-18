module

public import ProductClosure.CompilerData

@[expose] public section

/-! Actual Euclidean dimensions supported by fully proved finite compiler
world existence and universal period theorems. This predicate is not an axiom. -/
namespace ProductClosure
noncomputable section

/-- A dimension with concrete finite compiler data and both world obligations
proved. The existential keeps the ambient dimension explicit. -/
def CertifiedDimension (d : ℕ) : Prop :=
  ∃ m : ℕ, ∃ D : CompilerData m, d = m+1 ∧ D.HasWorld ∧ D.PeriodFree

/-- This is the user-facing physical meaning of every certified dimension. -/
theorem CertifiedDimension.exists_physical_monotile {d : ℕ} (h : CertifiedDimension d) :
    ∃ T : Set (EuclideanSpace ℝ (Fin d)),
      (interior T).Nonempty ∧ SparseMonotiles.IsAperiodicMonotile T := by
  obtain ⟨m,D,rfl,hw,hz⟩ := h
  exact ⟨D.material,D.physical_monotile hw hz⟩

theorem prime_three_mod_four_certified {p : ℕ} (hp : Nat.Prime p) (hmod : p%4=3) :
    CertifiedDimension p := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
  have hprime : Uniform.IsPrime (m+1) :=
    ⟨hp.two_le,fun d hd => hp.eq_one_or_self_of_dvd d hd⟩
  exact ⟨m,CompilerData.chair hprime hmod,rfl,
    CompilerData.chair_hasWorld hprime hmod,CompilerData.chair_periodFree hprime hmod⟩

theorem three_certified : CertifiedDimension 3 :=
  prime_three_mod_four_certified (by decide) (by decide)
theorem seven_certified : CertifiedDimension 7 :=
  prime_three_mod_four_certified (by decide) (by decide)
theorem eleven_certified : CertifiedDimension 11 :=
  prime_three_mod_four_certified (by decide) (by decide)

end
end ProductClosure
