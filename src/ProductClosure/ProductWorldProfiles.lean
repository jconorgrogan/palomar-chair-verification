module

public import ProductClosure.ProductGraphFullProfiles
public import ProductClosure.ProductWorldGraphPose
public import ProductClosure.WorldProfileContacts
public import ProductClosure.NativeProfileSelf
public import ProductClosure.ProductWorldGenerators
public import ProductClosure.ProductWorldDimensionCast

@[expose] public section

/-! Literal full coefficient profiles on actual Cartesian registered worlds. -/
namespace ProductClosure.ProductWorldProfiles
open Set NativeCompiler
open PhysicalRegistration.NativeChair (poseIsometry)
open ProductGraphSites ProductGraphPlacements ProductGraphSiteCoproduct
open ProductGraphBinding ProductGraphExact ProductGraphFullProfiles
noncomputable section

/-- Reindexing an actual registered pose equals reindexing its entire isometry. -/
theorem poseIsometry_castPose {m n : ℕ} (h : m = n)
    (q : RegisteredPrime.Pose (m + 1)) :
    poseIsometry (World.castPose (congrArg (fun d => d + 1) h) q) =
      poseCast h (poseIsometry q) := by
  subst n
  rfl

theorem castPose_trans {d e f : ℕ} (h : d = e) (k : e = f)
    (q : RegisteredPrime.Pose d) :
    World.castPose k (World.castPose h q) = World.castPose (h.trans k) q := by
  subst e
  subst f
  rfl

/-- The passive-left registered block is exactly the common-dimension right
isometry used by the literal product graph compiler. -/
theorem poseIsometry_commonRightBlock {a b : ℕ} (q : RegisteredPrime.Pose (b + 1)) :
    poseIsometry (World.castPose (productDim a (b + 1))
      (World.blockPose (RegisteredPrime.identityPose (a + 1)) q)) =
      commonLiftRight (a := a) (poseIsometry q) := by
  rw [commonLiftRight, ← World.poseIsometry_nativeRightPose, ← poseIsometry_castPose]
  unfold World.nativeRightPose
  rw [castPose_trans]

variable {a b : ℕ}
variable {SA : Finset (Polycube.LatticeIndex (a + 1))}
    {SB : Finset (Polycube.LatticeIndex (b + 1))}
variable [LinearOrder (Site SA)] [LinearOrder (Site SB)] [LinearOrder (Site (nativeProduct SA SB))]

/-- Every relative product-language generator with factor full profiles has
the actual all-site profile of the literal product coefficient assignment. -/
theorem fullProfile_of_relativeProductLanguage
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (cA : Polycube.Cell SA) (cB : Polycube.Cell SB)
    (e : RegisteredPrime.Pose ((a + 1) + (b + 1)))
    (h : World.RelativeProductLanguage
      (fun q => FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA)) (poseIsometry q))
      (fun q => FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB)) (poseIsometry q)) e) :
    FullProfileMating (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))
      (poseIsometry (World.castPose (productDim a (b + 1)) e)) := by
  obtain ⟨he, h | h⟩ := h
  · rw [← World.blockPose_left_right e he, h.2]
    change FullProfileMating _ (poseIsometry (World.nativeLeftPose (b + 1) (World.leftPose e he)))
    rw [World.poseIsometry_nativeLeftPose]
    exact (fullProfile_liftLeft_iff A B hA hB cB _).mpr h.1
  · rw [← World.blockPose_left_right e he, h.1, poseIsometry_commonRightBlock]
    exact (fullProfile_liftRight_iff A B hA hB cA _).mpr h.2

/-- The literal complete registered Cartesian world in the compiler's exact
common dimension, retaining every full placed frame and integer anchor. -/
def nativeProductWorld
    (WA : World.CompleteTiling (World.placedCells SA))
    (WB : World.CompleteTiling (World.placedCells SB)) :
    World.CompleteTiling (World.placedCells (nativeProduct SA SB)) :=
  (WA.ambientProduct WB).castDimension (productDim a (b + 1))

/-- Full factor profiles imply every actual full profile of the Cartesian
product world. Distinct noncontact pairs are handled using actual site-cell
adjacency; the self case is excluded by exposed-facet occupancy geometry. -/
theorem nativeProductWorld_fullProfile
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (cA : Polycube.Cell SA) (cB : Polycube.Cell SB)
    (WA : World.CompleteTiling (World.placedCells SA))
    (WB : World.CompleteTiling (World.placedCells SB))
    (hFA : CellWorldFullProfile (graphCoefficients (contactGraph (S := SA) A hA)) WA)
    (hFB : CellWorldFullProfile (graphCoefficients (contactGraph (S := SB) B hB)) WB) :
    CellWorldFullProfile (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))
      (nativeProductWorld WA WB) := by
  have hla : WA.IsLegal World.LatticeAdjacent (fun q r =>
      FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA))
        (poseIsometry (q.relative r))) := by
    intro x y _ _
    exact hFA _ _ (WA.owner_mem x) (WA.owner_mem y)
  have hlb : WB.IsLegal World.LatticeAdjacent (fun q r =>
      FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB))
        (poseIsometry (q.relative r))) := by
    intro x y _ _
    exact hFB _ _ (WB.owner_mem x) (WB.owner_mem y)
  let MA := fun q : RegisteredPrime.Pose (a + 1) =>
    FullProfileMating (graphCoefficients (contactGraph (S := SA) A hA)) (poseIsometry q)
  let MB := fun q : RegisteredPrime.Pose (b + 1) =>
    FullProfileMating (graphCoefficients (contactGraph (S := SB) B hB)) (poseIsometry q)
  have hp := WA.ambientProduct_legal (MA := MA) (MB := MB) WB hla hlb
  have hl := (WA.ambientProduct WB).castDimension_legal_of_map (productDim a (b + 1))
    (N := fun q => FullProfileMating
      (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB)) (poseIsometry q))
    hp (fullProfile_of_relativeProductLanguage A B hA hB cA cB)
  apply CellWorldFullProfile_of_distinct
  intro q r hq hr hne
  exact fullProfiles_of_neighbor_profiles _ (nativeProductWorld WA WB) hl q hq r hr hne

/-- Actual product material tiling existence follows from two complete factor
profile worlds, using the literal graph coefficients and proved tube gluing. -/
theorem nativeProduct_body_hasTiling
    [NeZero (a + (b + 1))]
    (hm : 2 ≤ a + (b + 1))
    (A : Finset (Space a ≃ᵢ Space a)) (B : Finset (Space b ≃ᵢ Space b))
    (hA : ∀ g ∈ A, IsProperPlacement g) (hB : ∀ g ∈ B, IsProperPlacement g)
    (cA : Polycube.Cell SA) (cB : Polycube.Cell SB)
    (WA : World.CompleteTiling (World.placedCells SA))
    (WB : World.CompleteTiling (World.placedCells SB))
    (hFA : CellWorldFullProfile (graphCoefficients (contactGraph (S := SA) A hA)) WA)
    (hFB : CellWorldFullProfile (graphCoefficients (contactGraph (S := SB) B hB)) WB) :
    SparseMonotiles.HasTiling
      (body (graphCoefficients (actualProductGraph (SA := SA) (SB := SB) A B hA hB))) := by
  let c : Polycube.Cell (Polycube.productCells SA SB) :=
    (Polycube.productCellEquiv SA SB).symm (cA, cB)
  letI : Nonempty (Polycube.Cell (nativeProduct SA SB)) :=
    ⟨Polycube.castCellEquiv (productDim a (b + 1)) _ c⟩
  exact body_hasTiling_of_profile_world hm _ (nativeProductWorld WA WB)
    (nativeProductWorld_fullProfile A B hA hB cA cB WA WB hFA hFB)

#print axioms fullProfile_of_relativeProductLanguage
#print axioms nativeProductWorld_fullProfile
#print axioms nativeProduct_body_hasTiling
end
end ProductClosure.ProductWorldProfiles
