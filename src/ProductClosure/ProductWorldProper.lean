module

public import ProductClosure.ProductWorldBlockChart
public import WorldExistence.ProperFrames

@[expose] public section

/-!
# Proper factor charts from proper relative contacts

Block preservation alone does not establish determinant +1 for either
factor: both blocks could be improper. Instead, after complete factor
worlds are decoded, their own proper relative contact languages imply a
proper root-normalized chart in each factor separately.
-/
namespace ProductClosure.World

open Set
noncomputable section

/-- Same handedness is defined by the properness of the complete relative
pose, and not by the determinant of any larger ambient product pose. -/
def properFrameSetoid (d : ℕ) : Setoid (RegisteredPrime.Pose d) where
  r q r := (q.relative r).frame.IsProper
  iseqv := by
    constructor
    · intro q
      change (q.inv.comp q).frame.IsProper
      rw [RegisteredPrime.Pose.inv_comp]
      exact RegisteredPrime.identity_frame_proper d
    · intro q r h
      have h' := h.inv
      have he : (q.relative r).inv = r.relative q := by
        simp only [RegisteredPrime.Pose.relative, RegisteredPrime.Pose.inv_compose,
          RegisteredPrime.Pose.inv_inv]
      change (q.relative r).inv.frame.IsProper at h'
      rwa [he] at h'
    · intro q r s hqr hrs
      have h := RegisteredPrime.RegisteredFrame.IsProper.comp hqr hrs
      have he : (q.relative r).comp (r.relative s) = q.relative s := by
        simp only [RegisteredPrime.Pose.relative]
        rw [RegisteredPrime.Pose.comp_assoc, ← RegisteredPrime.Pose.comp_assoc r,
          RegisteredPrime.Pose.comp_inv, RegisteredPrime.Pose.identity_comp]
      change ((q.relative r).comp (r.relative s)).frame.IsProper at h
      rwa [he] at h

/-- Every factor pose is proper after normalization at a single root,
provided every actual relative factor contact belongs to a proper language.
This is derived by connectivity, not assumed for all absolute tile poses. -/
theorem common_proper_frame_chart {d : ℕ}
    {cells : RegisteredPrime.Pose d → Set (Lattice d)}
    (W : CompleteTiling cells)
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => (q.relative r).frame.IsProper))
    {root : RegisteredPrime.Pose d} (hroot : root ∈ W.tiles) :
    ∀ q ∈ W.tiles, (root.relative q).frame.IsProper := by
  intro q hq
  exact W.all_tiles_equivalent (properFrameSetoid d) hlocal hroot hq

/-- A proper chart exists without a chosen external orientation or root. -/
theorem exists_proper_frame_chart {d : ℕ}
    {cells : RegisteredPrime.Pose d → Set (Lattice d)}
    (W : CompleteTiling cells)
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => (q.relative r).frame.IsProper)) :
    ∃ root ∈ W.tiles, ∀ q ∈ W.tiles, (root.relative q).frame.IsProper :=
  ⟨W.owner 0, W.owner_mem 0, common_proper_frame_chart W hlocal (W.owner_mem 0)⟩

/-- Any legal factor language consisting of proper relative poses supplies
the proper chart needed by the factor hierarchy. -/
theorem proper_chart_of_legal_language {d : ℕ}
    {cells : RegisteredPrime.Pose d → Set (Lattice d)}
    {M : RegisteredPrime.Pose d → RegisteredPrime.Pose d → Prop}
    (W : CompleteTiling cells) (hlegal : W.IsLegal LatticeAdjacent M)
    (hproper : ∀ q r, M q r → (q.relative r).frame.IsProper) :
    ∃ root ∈ W.tiles, ∀ q ∈ W.tiles, (root.relative q).frame.IsProper := by
  apply exists_proper_frame_chart W
  intro x y hadj hne
  exact hproper _ _ (hlegal x y hadj hne)

#print axioms common_proper_frame_chart
#print axioms proper_chart_of_legal_language

end
end ProductClosure.World
