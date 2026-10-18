module

public import PhysicalRegistration.ComponentCoefficients
public import ProductClosure.NativeOrientation
public import ProductClosure.IsometryTransport
public import ProductClosure.NativeAngleSeparation

@[expose] public section

/-! Actual finite contact-graph coefficients and properness of the physically
recovered mate. Only generating contacts are assumed proper. A candidate
physical mate is never required to be proper or graph-legal. -/
namespace ProductClosure.NativeCompiler
noncomputable section
attribute [local instance] Classical.propDecidable
open PhysicalRegistration.ComponentCoefficients

variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}

/-- Every paired site and its complete tangent frame, not a sampled feature. -/
def SiteTransport (g : Space m ≃ᵢ Space m) (u v : Site S) : Prop :=
  (∀ j, placedNormal g (siteAxis v j) = siteAxis u j) ∧
  placedNormal g (outward v.1) = -outward u.1 ∧
  g (siteCenter v) = siteCenter u

def IsProperPlacement (g : Space m ≃ᵢ Space m) : Prop :=
  LinearMap.det g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap = 1

theorem SiteTransport.orientation_neg {g : Space m ≃ᵢ Space m}
    {u v : Site S} (hg : IsProperPlacement g) (h : SiteTransport g u v) :
    orientation v = -orientation u := by
  have hd := frame_matching_determinant
    g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap u v h.1 h.2.1
  change LinearMap.det _ = 1 at hg
  rw [hg, one_mul] at hd
  exact_mod_cast hd

/-- The finite prescribed language produces the literal undirected site
pairing graph. Both directions are included; self-edges are ruled out by
orientation, rather than removed by definition. -/
def contactGraph (A : Finset (Space m ≃ᵢ Space m))
    (hA : ∀ g ∈ A, IsProperPlacement g) : SimpleGraph (Site S) where
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

theorem contactGraph_edge_orientation (A : Finset (Space m ≃ᵢ Space m))
    (hA : ∀ g ∈ A, IsProperPlacement g) {u v : Site S}
    (h : (contactGraph (S := S) A hA).Adj u v) : orientation v = -orientation u := by
  obtain ⟨g, hg, h⟩ := h
  rcases h with h | h
  · exact h.orientation_neg (hA g hg)
  · have := h.orientation_neg (hA g hg)
    omega

/-- Exact rank-times-orientation coefficients for an actual native-site graph.
The explicit site order determines component ranks; no labels are supplied. -/
def graphCoefficients [LinearOrder (Site S)] (G : SimpleGraph (Site S)) :
    Coefficients S (count G) where
  value := value G orientation
  bound := by
    intro u
    exact_mod_cast abs_value_le_count G orientation orientation_sign u
  nonzero := value_nonzero G orientation orientation_sign

theorem graphCoefficients_opposite_iff [LinearOrder (Site S)]
    (G : SimpleGraph (Site S)) (u v : Site S) :
    (graphCoefficients G).value v = -(graphCoefficients G).value u ↔
      G.Reachable u v ∧ orientation v = -orientation u :=
  opposite_value_iff G orientation orientation_sign u v

theorem contactGraph_coefficients_satisfy_all_edges [LinearOrder (Site S)]
    (A : Finset (Space m ≃ᵢ Space m)) (hA : ∀ g ∈ A, IsProperPlacement g)
    {u v : Site S} (h : (contactGraph (S := S) A hA).Adj u v) :
    (graphCoefficients (contactGraph (S := S) A hA)).value v =
      -(graphCoefficients (contactGraph (S := S) A hA)).value u :=
  edge_value_neg _ orientation orientation_sign
    (fun _ _ h => contactGraph_edge_orientation A hA h) h

/-- Actual full-frame matching and opposite coefficients force properness
and component equality, even when neither was known for the candidate. -/
theorem proper_and_connected_of_matched_coefficients [LinearOrder (Site S)]
    (G : SimpleGraph (Site S)) (g : Space m ≃ᵢ Space m) (u v : Site S)
    (ht : ∀ j, placedNormal g (siteAxis v j) = siteAxis u j)
    (hn : placedNormal g (outward v.1) = -outward u.1)
    (ha : (graphCoefficients G).value v = -(graphCoefficients G).value u) :
    IsProperPlacement g ∧ G.Reachable u v := by
  have hh := (graphCoefficients_opposite_iff G u v).mp ha
  exact ⟨proper_of_frame_matching g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearMap
    u v ht hn hh.2, hh.1⟩


end
end ProductClosure.NativeCompiler
