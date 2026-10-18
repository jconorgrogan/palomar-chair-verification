module

public import ProductClosure.NativeComponentOrder
public import ProductClosure.NativePhysicalFrameRegistration

@[expose] public section

namespace ProductClosure.NativeCompiler
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell S)]

/-- Specialization to an arbitrary physical tiling of the graph-compiled native
body: the genuinely recovered whole companion has proper relative pose and
its two sites lie in one graph component. No registration or graph legality
is assumed of the tiling. -/
theorem PhysicalTiling.exists_proper_graph_companion
    [NeZero m] [LinearOrder (Site S)] {ι : Type*} (hm : 2 ≤ m)
    (G : SimpleGraph (Site S)) {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (graphCoefficients G) f) (root : ι) (u : Site S) :
    ∃ iv : ι × Site S, iv.1 ≠ root ∧
      f root '' creaseComplex (graphCoefficients G) u =
        f iv.1 '' creaseComplex (graphCoefficients G) iv.2 ∧
      IsProperPlacement (relativePlacement (f root) (f iv.1)) ∧
      G.Reachable u iv.2 := by
  obtain ⟨iv, hiv, _⟩ := T.unique_framed_key_companion hm root u
  have hrel := relativePlacement_key_frame u iv.2 (f root) (f iv.1)
    hiv.2.2.1 hiv.2.2.2.1
  have hp := proper_and_connected_of_matched_coefficients G
    (relativePlacement (f root) (f iv.1)) u iv.2 hrel.1 hrel.2 hiv.2.2.2.2.2
  exact ⟨iv, hiv.1, hiv.2.1, hp.1, hp.2⟩

/-- No ordering, coefficient, graph-legality, or properness certificate is
supplied by a physical tiling. Its recovered companion is proved proper and
in the same computed contact-graph component. -/
theorem PhysicalTiling.compiled_exists_proper_graph_companion
    [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (compiledCoefficients (S := S) hm A hA) f) (root : ι) (u : Site S) :
    ∃ iv : ι × Site S, iv.1 ≠ root ∧
      f root '' creaseComplex (compiledCoefficients (S := S) hm A hA) u =
        f iv.1 '' creaseComplex (compiledCoefficients (S := S) hm A hA) iv.2 ∧
      IsProperPlacement (relativePlacement (f root) (f iv.1)) ∧
      (contactGraph (S := S) A hA).Reachable u iv.2 := by
  letI := nativeSiteOrder (S := S) hm
  exact T.exists_proper_graph_companion hm (contactGraph (S := S) A hA) root u

end
end ProductClosure.NativeCompiler
