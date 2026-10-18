module

public import ProductClosure.ProductWorldDecoding
public import AtlasPeriods.Translation

@[expose] public section

/-!
# Actual ambient translation periods descend through decoding

The period is the original full-pose translation action. Reframing changes
its vector by the root's inverse signed linear frame; splitting projects
that exact vector into the two factor blocks. Zero factor periods therefore
force the original ambient vector to be zero.
-/
namespace ProductClosure.World
open Set
open RegisteredPrime
noncomputable section

/-- Translation commutes with root normalization by the inverse root frame,
including all affine anchor terms. -/
theorem relative_translate (root q : Pose d) (v : Lattice d) :
    root.relative (AtlasPeriods.translate v q) =
      AtlasPeriods.translate (root.frame.inv.linear v) (root.relative q) := by
  apply Pose.Same.eq
  constructor
  · intro i; rfl
  constructor
  · intro i; rfl
  · intro i
    simp only [Pose.relative, Pose.comp, Pose.inv, AtlasPeriods.translate, RegisteredFrame.linear]
    ring

/-- The inverse signed frame is injective on actual integer vectors. -/
theorem inverse_linear_eq_zero {d : ℕ} (F : RegisteredFrame d) (v : Lattice d)
    (h : F.inv.linear v = 0) : v = 0 := by
  funext i
  have hi := congrFun h (F.perm i)
  simp only [RegisteredFrame.linear, RegisteredFrame.inv, F.left_inverse, Pi.zero_apply] at hi
  cases hn : F.negative i <;> simpa [RegisteredFrame.sign, F.left_inverse, hn] using hi

namespace CompleteTiling
variable {d : ℕ} {S : Finset (Lattice d)}

/-- The actual reframed tile set is the image under root-relative pose
normalization, including the entire frame state. -/
theorem reframe_tiles_image (W : CompleteTiling (placedCells S)) (root : Pose d) :
    (W.reframe root).tiles = root.relative '' W.tiles := by
  ext q
  constructor
  · intro hq
    refine ⟨root.comp q, hq, ?_⟩
    simp only [Pose.relative, ← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp]
  · rintro ⟨r, hr, rfl⟩
    change root.comp (root.relative r) ∈ W.tiles
    simpa only [Pose.comp_relative] using hr

/-- An ambient period survives actual root normalization with its correctly
conjugated vector, rather than with the unrotated original vector. -/
theorem reframe_hasStatePeriod (W : CompleteTiling (placedCells S)) (root : Pose d)
    (v : Lattice d) (hperiod : W.HasStatePeriod (AtlasPeriods.translate v)) :
    (W.reframe root).HasStatePeriod (AtlasPeriods.translate (root.frame.inv.linear v)) := by
  change AtlasPeriods.translate (root.frame.inv.linear v) '' (W.reframe root).tiles =
    (W.reframe root).tiles
  rw [reframe_tiles_image, Set.image_image]
  have hf : (fun q => AtlasPeriods.translate (root.frame.inv.linear v) (root.relative q)) =
      (fun q => root.relative (AtlasPeriods.translate v q)) := by
    funext q
    exact (relative_translate root q v).symm
  rw [hf, ← Set.image_image]
  exact congrArg (fun s => root.relative '' s) hperiod

end CompleteTiling

variable {m n : ℕ}

theorem PreservesBlocks.translate {q : Pose (m + n)} (hq : PreservesBlocks q)
    (v : Lattice (m + n)) : PreservesBlocks (AtlasPeriods.translate v q) := hq

@[simp] theorem leftPose_translate (q : Pose (m + n)) (hq : PreservesBlocks q)
    (v : Lattice (m + n)) :
    leftPose (AtlasPeriods.translate v q) (hq.translate v) =
      AtlasPeriods.translate (Polycube.leftIndex v) (leftPose q hq) := by
  apply Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem rightPose_translate (q : Pose (m + n)) (hq : PreservesBlocks q)
    (v : Lattice (m + n)) :
    rightPose (AtlasPeriods.translate v q) (hq.translate v) =
      AtlasPeriods.translate (Polycube.rightIndex v) (rightPose q hq) := by
  apply Pose.Same.eq
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

namespace CompleteTiling
variable {S : Finset (Lattice m)} {T : Finset (Lattice n)}
variable (W : CompleteTiling (placedCells (Polycube.productCells S T)))
variable (hblock : ∀ q ∈ W.tiles, PreservesBlocks q)

/-- Splitting actual translated tile states projects the exact translation
vector and leaves every factor frame unchanged. -/
theorem splitState_translate (v : Lattice (m + n)) (q : {q // q ∈ W.tiles})
    (ht : AtlasPeriods.translate v q.val ∈ W.tiles) :
    W.splitState hblock ⟨AtlasPeriods.translate v q.val, ht⟩ =
      Prod.map (AtlasPeriods.translate (Polycube.leftIndex v))
        (AtlasPeriods.translate (Polycube.rightIndex v)) (W.splitState hblock q) := by
  apply Prod.ext
  · exact leftPose_translate q.val (hblock _ q.property) v
  · exact rightPose_translate q.val (hblock _ q.property) v

/-- A genuine normalized ambient period induces a period of the whole split
pair-state world under the two projected full-pose translations. -/
theorem splitWorld_hasStatePeriod (v : Lattice (m + n))
    (hperiod : W.HasStatePeriod (AtlasPeriods.translate v)) :
    (W.splitWorld hblock).HasStatePeriod
      (Prod.map (AtlasPeriods.translate (Polycube.leftIndex v))
        (AtlasPeriods.translate (Polycube.rightIndex v))) := by
  change Prod.map _ _ '' Set.range (W.splitState hblock) = Set.range (W.splitState hblock)
  ext p
  constructor
  · rintro ⟨p₀, ⟨q, rfl⟩, rfl⟩
    have ht : AtlasPeriods.translate v q.val ∈ W.tiles := by
      have hi : AtlasPeriods.translate v q.val ∈ AtlasPeriods.translate v '' W.tiles :=
        ⟨q.val, q.property, rfl⟩
      rw [show AtlasPeriods.translate v '' W.tiles = W.tiles from hperiod] at hi
      exact hi
    exact ⟨⟨AtlasPeriods.translate v q.val, ht⟩, W.splitState_translate hblock v q ht⟩
  · rintro ⟨q, rfl⟩
    have hq : q.val ∈ AtlasPeriods.translate v '' W.tiles := hperiod.symm ▸ q.property
    obtain ⟨r, hr, he⟩ := hq
    let r' : {q // q ∈ W.tiles} := ⟨r, hr⟩
    have ht : AtlasPeriods.translate v r ∈ W.tiles := he.symm ▸ q.property
    refine ⟨W.splitState hblock r', ⟨r', rfl⟩, ?_⟩
    calc
      _ = W.splitState hblock ⟨AtlasPeriods.translate v r, ht⟩ :=
        (W.splitState_translate hblock v r' ht).symm
      _ = W.splitState hblock q := congrArg (W.splitState hblock) (Subtype.ext he)

/-- Final actual period connector: every complete legal factor world has
zero translation periods, therefore the original ambient registered world
has no nonzero period under the exact AtlasPeriods.translate action. -/
theorem ambient_period_zero_of_factor_worlds
    {MA : Pose m → Prop} {MB : Pose n → Prop}
    (hlocal : W.IsLegal LatticeAdjacent (fun q r => RelativeProductLanguage MA MB (q.relative r)))
    (hsepA : Separates (placedCells S) (fun a b => MA (a.relative b)))
    (hsepB : Separates (placedCells T) (fun a b => MB (a.relative b)))
    (hzeroA : ∀ WA : CompleteTiling (placedCells S),
      WA.IsLegal LatticeAdjacent (fun a b => MA (a.relative b)) →
      ∀ u, WA.HasStatePeriod (AtlasPeriods.translate u) → u = 0)
    (hzeroB : ∀ WB : CompleteTiling (placedCells T),
      WB.IsLegal LatticeAdjacent (fun a b => MB (a.relative b)) →
      ∀ v, WB.HasStatePeriod (AtlasPeriods.translate v) → v = 0)
    (v : Lattice (m + n)) (hperiod : W.HasStatePeriod (AtlasPeriods.translate v)) : v = 0 := by
  let root := W.owner 0
  have hr : root ∈ W.tiles := W.owner_mem 0
  have hblocks : W.IsLegal LatticeAdjacent (fun q r => PreservesBlocks (q.relative r)) := by
    intro x y hadj hne
    exact (hlocal x y hadj hne).choose
  let N := W.reframe root
  have hb : ∀ q ∈ N.tiles, PreservesBlocks q := W.reframe_preservesBlocks hblocks hr
  let C := N.splitWorld hb
  have hl := N.splitWorld_relative_legal hb (W.reframe_legal root hlocal)
  have hNperiod := W.reframe_hasStatePeriod root v hperiod
  have hCperiod := N.splitWorld_hasStatePeriod hb (root.frame.inv.linear v) hNperiod
  have ha := hzeroA (C.activeFactor hl hsepA hsepB) (C.activeFactor_legal hl hsepA hsepB)
  have hbzero := hzeroB (C.passiveFactor hl hsepA hsepB) (C.passiveFactor_legal hl hsepA hsepB)
  obtain ⟨hleft, hright⟩ := C.product_period_zero hl hsepA hsepB
    AtlasPeriods.translate AtlasPeriods.translate ha hbzero
    (Polycube.leftIndex (root.frame.inv.linear v))
    (Polycube.rightIndex (root.frame.inv.linear v)) hCperiod
  apply inverse_linear_eq_zero root.frame v
  rw [← Polycube.append_leftIndex_rightIndex (root.frame.inv.linear v), hleft, hright]
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

#print axioms reframe_hasStatePeriod
#print axioms splitWorld_hasStatePeriod
#print axioms ambient_period_zero_of_factor_worlds

end CompleteTiling
end
end ProductClosure.World
