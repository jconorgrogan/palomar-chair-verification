module

public import ProductClosure.NativeSiteOrder
public import ProductClosure.NativeGraphCoefficients

@[expose] public section

namespace ProductClosure.NativeCompiler
noncomputable section
open PhysicalRegistration.ComponentCoefficients
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- The literal coefficient assignment in the source's ordering, with J
computed as the number of connected components. -/
def compiledCoefficients (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g) :
    letI := nativeSiteOrder (S := S) hm
    Coefficients S (count (contactGraph (S := S) A hA)) := by
  letI := nativeSiteOrder (S := S) hm
  exact graphCoefficients (contactGraph (S := S) A hA)

/-- Replacing q by the stored numerator preserves each lexicographic
coordinate comparison because the scale is common and strictly positive. -/
theorem native_q_lt_iff_numerator_lt (u v : Site S) (j : Fin m) :
    siteOffset u ((normalIndex u.1).succAbove j) <
        siteOffset v ((normalIndex v.1).succAbove j) ↔
      orbitNumerator u.2 j < orbitNumerator v.2 j := by
  rw [siteOffset_eq_orbitNumerator, siteOffset_eq_orbitNumerator]
  rw [div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * ((m : ℝ) + 1))]
  exact_mod_cast Iff.rfl

/-- Every prescribed site equation holds for the completely constructed
coefficient assignment, including its geometric site ordering. -/
theorem compiledCoefficients_edge_neg (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site S} (h : (contactGraph (S := S) A hA).Adj u v) :
    (compiledCoefficients hm A hA).value v = -(compiledCoefficients hm A hA).value u := by
  letI := nativeSiteOrder (S := S) hm
  exact contactGraph_coefficients_satisfy_all_edges A hA h


end
end ProductClosure.NativeCompiler
