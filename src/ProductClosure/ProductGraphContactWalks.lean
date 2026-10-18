module

public import ProductClosure.ProductGraphTransport
public import ProductClosure.NativeGraphCoefficients
public import ProductClosure.IntegralPoseAlgebra

@[expose] public section

/-! Odd paths in the actual finite contact graph compose actual generator
isometries and their inverses, yielding complete native transports. -/
namespace ProductClosure.ProductGraphContactWalks
noncomputable section
open NativeCompiler ProductGraph ProductGraphTransport
open PhysicalRegistration.ComponentCoefficients
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m+1))}

theorem inverse_siteTransport {g : Space m ≃ᵢ Space m} {u v : Site S}
    (h : SiteTransport g u v) : SiteTransport g.symm v u := by
  constructor
  · intro j
    apply g.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
    change placedNormal g (placedNormal g.symm (siteAxis u j)) = placedNormal g (siteAxis v j)
    rw [placedNormal_apply_symm, h.1]
  · constructor
    · apply g.toRealAffineIsometryEquiv.linearIsometryEquiv.injective
      change placedNormal g (placedNormal g.symm (outward u.1)) = placedNormal g (-outward v.1)
      rw [placedNormal_apply_symm]
      have hneg : placedNormal g (-outward v.1) = -placedNormal g (outward v.1) :=
        g.toRealAffineIsometryEquiv.linearIsometryEquiv.map_neg _
      rw [hneg, h.2.1, neg_neg]
    · rw [← h.2.2, g.symm_apply_apply]

/-- Edge witnesses are genuine generators or genuine inverses. -/
theorem edge_transport_exists (E : Finset (Space m ≃ᵢ Space m))
    (hE : ∀ g ∈ E, IsProperPlacement g) {u v : Site S}
    (h : (contactGraph E hE).Adj u v) :
    ∃ g : Space m ≃ᵢ Space m, (g ∈ E ∨ g.symm ∈ E) ∧ SiteTransport g u v := by
  obtain ⟨g, hg, h⟩ := h
  rcases h with h | h
  · exact ⟨g, Or.inl hg, h⟩
  · exact ⟨g.symm, Or.inr (by simpa using hg), inverse_siteTransport h⟩

def edgePlacement (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    (u v : Site S) (h : (contactGraph E hE).Adj u v) : Space m ≃ᵢ Space m :=
  Classical.choose (edge_transport_exists E hE h)

theorem edgePlacement_spec (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)
    (u v : Site S) (h : (contactGraph E hE).Adj u v) :
    (edgePlacement E hE u v h ∈ E ∨ (edgePlacement E hE u v h).symm ∈ E) ∧
      SiteTransport (edgePlacement E hE u v h) u v :=
  Classical.choose_spec (edge_transport_exists E hE h)

variable (E : Finset (Space m ≃ᵢ Space m)) (hE : ∀ g ∈ E, IsProperPlacement g)

/-- A path from u to v transports v back to u. -/
def walkPlacement {u v : Site S} : (contactGraph E hE).Walk u v → Space m ≃ᵢ Space m
  | .nil => IsometryEquiv.refl _
  | .cons h w => (walkPlacement w).trans (edgePlacement E hE _ _ h)

theorem walkPlacement_tangents {u v : Site S} (w : (contactGraph E hE).Walk u v) (j : Fin m) :
    placedNormal (walkPlacement E hE w) (siteAxis v j) = siteAxis u j := by
  induction w with
  | nil => exact placedNormal_refl _
  | @cons u v z h w ih =>
    change placedNormal ((walkPlacement E hE w).trans (edgePlacement E hE u v h)) _ = _
    rw [placedNormal_trans, ih]
    exact (edgePlacement_spec E hE u v h).2.1 j

theorem walkPlacement_normals {u v : Site S} (w : (contactGraph E hE).Walk u v) :
    placedNormal (walkPlacement E hE w) (outward v.1) = (-1 : ℝ)^w.length • outward u.1 := by
  induction w with
  | nil => simp [walkPlacement]
  | @cons u v z h w ih =>
    change placedNormal ((walkPlacement E hE w).trans (edgePlacement E hE u v h)) _ = _
    rw [placedNormal_trans, ih]
    change (edgePlacement E hE u v h).toRealAffineIsometryEquiv.linearIsometryEquiv
      ((-1 : ℝ)^w.length • outward v.1) = _
    rw [map_smul]
    change (-1 : ℝ)^w.length • placedNormal (edgePlacement E hE u v h) (outward v.1) = _
    rw [(edgePlacement_spec E hE u v h).2.2.1]
    simp [SimpleGraph.Walk.length_cons, pow_succ, mul_smul]

theorem walkPlacement_centers {u v : Site S} (w : (contactGraph E hE).Walk u v) :
    walkPlacement E hE w (siteCenter v) = siteCenter u := by
  induction w with
  | nil => rfl
  | @cons u v z h w ih =>
    change edgePlacement E hE u v h (walkPlacement E hE w (siteCenter z)) = _
    rw [ih]
    exact (edgePlacement_spec E hE u v h).2.2.2

theorem odd_walk_siteTransport {u v : Site S} (w : (contactGraph E hE).Walk u v)
    (hw : Odd w.length) : SiteTransport (walkPlacement E hE w) u v := by
  refine ⟨walkPlacement_tangents E hE w, ?_, walkPlacement_centers E hE w⟩
  rw [walkPlacement_normals, hw.neg_one_pow, neg_one_smul]

/-- Opposite computed coefficients give an actual odd generator/inverse walk,
whose composed Euclidean isometry matches the entire native frame and site. -/
theorem opposite_coefficients_odd_transport [LinearOrder (Site S)] (u v : Site S)
    (hcoeff : (graphCoefficients (contactGraph E hE)).value v =
      -(graphCoefficients (contactGraph E hE)).value u) :
    ∃ w : (contactGraph E hE).Walk u v, Odd w.length ∧
      SiteTransport (walkPlacement E hE w) u v ∧ IsProperPlacement (walkPlacement E hE w) := by
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk (contactGraph E hE)
    orientation orientation_sign (fun _ _ h => contactGraph_edge_orientation E hE h) u v hcoeff
  have ht := odd_walk_siteTransport E hE w hw
  refine ⟨w, hw, ht, ?_⟩
  exact (proper_and_connected_of_matched_coefficients (contactGraph E hE)
    (walkPlacement E hE w) u v ht.1 ht.2.1 hcoeff).1

/-- Existential form convenient for lifting the recovered active isometry
into the physical product block. No candidate pose is supplied. -/
theorem opposite_coefficients_exists_transport [LinearOrder (Site S)] (u v : Site S)
    (hcoeff : (graphCoefficients (contactGraph E hE)).value v =
      -(graphCoefficients (contactGraph E hE)).value u) :
    ∃ g : Space m ≃ᵢ Space m, SiteTransport g u v ∧ IsProperPlacement g := by
  obtain ⟨w, _, ht, hp⟩ := opposite_coefficients_odd_transport E hE u v hcoeff
  exact ⟨walkPlacement E hE w, ht, hp⟩

#print axioms opposite_coefficients_odd_transport
#print axioms opposite_coefficients_exists_transport
end
end ProductClosure.ProductGraphContactWalks
