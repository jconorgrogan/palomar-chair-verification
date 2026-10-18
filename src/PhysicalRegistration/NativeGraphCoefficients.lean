module

public import PhysicalRegistration.ComponentCoefficients
public import PhysicalRegistration.NativeOrientation
public import PhysicalRegistration.PhysicalKeyFrames
public import PhysicalRegistration.SignedPermutationRegistration

@[expose] public section

/-! Actual finite contact-graph coefficients and properness of the physically
recovered mate. Only generating contacts are assumed proper. A candidate
physical mate is never required to be proper or graph-legal. -/
namespace PhysicalRegistration.NativeChair
noncomputable section
attribute [local instance] Classical.propDecidable
open ComponentCoefficients

/-- Every paired site and its complete tangent frame, not a sampled feature. -/
def SiteTransport {m : ℕ} (g : Space m ≃ᵢ Space m) (u v : Site m) : Prop :=
  (∀ j, placedNormal g (siteAxis v j) = siteAxis u j) ∧
  placedNormal g (outward v.1) = -outward u.1 ∧
  g (siteCenter v) = siteCenter u

def IsProperPlacement {m : ℕ} (g : Space m ≃ᵢ Space m) : Prop :=
  LinearMap.det g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap = 1

theorem SiteTransport.orientation_neg {m : ℕ} {g : Space m ≃ᵢ Space m}
    {u v : Site m} (hg : IsProperPlacement g) (h : SiteTransport g u v) :
    orientation v = -orientation u := by
  have hd := frame_matching_determinant
    g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap u v h.1 h.2.1
  change LinearMap.det _ = 1 at hg
  rw [hg, one_mul] at hd
  exact_mod_cast hd

/-- The finite prescribed language produces the literal undirected site
pairing graph. Both directions are included; self-edges are ruled out by
orientation, rather than removed by definition. -/
def contactGraph {m : ℕ} (A : Finset (Space m ≃ᵢ Space m))
    (hA : ∀ g ∈ A, IsProperPlacement g) : SimpleGraph (Site m) where
  Adj u v := ∃ g ∈ A, SiteTransport g u v ∨ SiteTransport g v u
  symm := ⟨by
    rintro u v ⟨g, hg, h⟩
    exact ⟨g, hg, h.symm⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨g, hg, h⟩
    have htrans : SiteTransport g u u := h.elim id id
    have he := htrans.orientation_neg (hA g hg)
    have hn := orientation_nonzero u
    omega⟩

theorem contactGraph_edge_orientation {m : ℕ} (A : Finset (Space m ≃ᵢ Space m))
    (hA : ∀ g ∈ A, IsProperPlacement g) {u v : Site m}
    (h : (contactGraph A hA).Adj u v) : orientation v = -orientation u := by
  obtain ⟨g, hg, h⟩ := h
  rcases h with h | h
  · exact h.orientation_neg (hA g hg)
  · have := h.orientation_neg (hA g hg)
    omega

/-- Exact rank-times-orientation coefficients for an actual native-site graph.
The explicit site order determines component ranks; no labels are supplied. -/
def graphCoefficients {m : ℕ} [LinearOrder (Site m)] (G : SimpleGraph (Site m)) :
    Coefficients m (count G) where
  value := value G orientation
  bound := by
    intro u
    exact_mod_cast abs_value_le_count G orientation orientation_sign u
  nonzero := value_nonzero G orientation orientation_sign

theorem graphCoefficients_opposite_iff {m : ℕ} [LinearOrder (Site m)]
    (G : SimpleGraph (Site m)) (u v : Site m) :
    (graphCoefficients G).value v = -(graphCoefficients G).value u ↔
      G.Reachable u v ∧ orientation v = -orientation u :=
  opposite_value_iff G orientation orientation_sign u v

theorem contactGraph_coefficients_satisfy_all_edges {m : ℕ} [LinearOrder (Site m)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site m} (h : (contactGraph A hA).Adj u v) :
    (graphCoefficients (contactGraph A hA)).value v =
      -(graphCoefficients (contactGraph A hA)).value u :=
  edge_value_neg _ orientation orientation_sign
    (fun _ _ h => contactGraph_edge_orientation A hA h) h

/-- Actual full-frame matching and opposite coefficients force properness
and component equality, even when neither was known for the candidate. -/
theorem proper_and_connected_of_matched_coefficients {m : ℕ} [LinearOrder (Site m)]
    (G : SimpleGraph (Site m)) (g : Space m ≃ᵢ Space m) (u v : Site m)
    (ht : ∀ j, placedNormal g (siteAxis v j) = siteAxis u j)
    (hn : placedNormal g (outward v.1) = -outward u.1)
    (ha : (graphCoefficients G).value v = -(graphCoefficients G).value u) :
    IsProperPlacement g ∧ G.Reachable u v := by
  have hh := (graphCoefficients_opposite_iff G u v).mp ha
  exact ⟨proper_of_frame_matching g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap
    u v ht hn hh.2, hh.1⟩

/-- Specialization to an arbitrary physical tiling of the graph-compiled native
body: the genuinely recovered whole companion has proper relative pose and
its two sites lie in one graph component. No registration or graph legality
is assumed of the tiling. -/
theorem PhysicalTiling.exists_proper_graph_companion
    {m : ℕ} [NeZero m] [LinearOrder (Site m)] {ι : Type*} (hm : 2 ≤ m)
    (G : SimpleGraph (Site m)) {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling (graphCoefficients G) f) (root : ι) (u : Site m) :
    ∃ iv : ι × Site m, iv.1 ≠ root ∧
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

end
end PhysicalRegistration.NativeChair
