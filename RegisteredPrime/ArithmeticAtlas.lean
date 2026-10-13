module
public import WeakRecognition.CoarseWorld
public import closure_analysis.ZeroOrigin
@[expose] public section
namespace RegisteredPrime

/-- A concrete enlarged local atlas. It records only arithmetic/per-contact
conditions, with no parent, hierarchy, coarsening or closure assertion. -/
structure ArithmeticAtlasContact (P : Parameters) (e : Pose P.p) : Prop extends RecognitionContact P e where
  affine : e.AffineIndex
  zero_origin : (∀ i, e.anchor i = 0) → e.ZeroOrigin P

theorem generated_arithmetic_atlas_contact (P : Parameters) (e : Pose P.p)
    (he : GeneratedContact P e) : ArithmeticAtlasContact P e :=
  ⟨generated_recognition_contact P e he, generated_contact_affine_index P e he,
    generated_contact_zero_origin P e he⟩

def ArithmeticAtlasLegal (P : Parameters) (W : RegisteredWorld P.p) : Prop :=
  ∀ q r, W.tiles q → W.tiles r → FaceContact q r → ArithmeticAtlasContact P (q.relative r)

theorem arithmetic_atlas_legal_of_E (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) : ArithmeticAtlasLegal P W :=
  fun q r hq hr hc => generated_arithmetic_atlas_contact P _ (hl q r hq hr hc)

theorem ArithmeticAtlasLegal.recognition (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) : WeakRecognition.Legal P W :=
  fun q r hq hr hc => (hl q r hq hr hc).toRecognitionContact

/-- Universal fine testing of the concrete atlas, without silently asserting
that the tested parents are themselves atlas contacts. -/
def ChildArithmeticAtlas (P : Parameters) (t u : Pose P.p) : Prop :=
  ∀ a b : Role P.p,
    FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) →
    ArithmeticAtlasContact P ((t.comp (arithmeticChild P a)).relative
      (u.comp (arithmeticChild P b)))

theorem ChildArithmeticAtlas.recognition (P : Parameters) (t u : Pose P.p)
    (hl : ChildArithmeticAtlas P t u) : WeakRecognition.ChildRecognition P t u :=
  fun a b hc => (hl a b hc).toRecognitionContact

theorem ChildArithmeticAtlas.reframe (P : Parameters) (g t u : Pose P.p)
    (hl : ChildArithmeticAtlas P t u) : ChildArithmeticAtlas P (g.comp t) (g.comp u) := by
  intro a b hc
  have hc' : FaceContact (t.comp (arithmeticChild P a)) (u.comp (arithmeticChild P b)) := by
    have h := g.inv.face_contact _ _ hc
    simpa only [← Pose.comp_assoc, Pose.inv_comp, Pose.identity_comp] using h
  rw [Pose.comp_assoc, Pose.comp_assoc, Pose.relative_left_cancel]
  exact hl a b hc'

/-- Coarse affine permutations are already a theorem of fine atlas testing. -/
theorem child_arithmetic_atlas_parent_affine (P : Parameters) (t u : Pose P.p)
    (hc : DoubledFaceContact t u) (hl : ChildArithmeticAtlas P t u) :
    (t.relative u).AffineIndex :=
  child_affine_parent_affine_index P t u hc (fun a b h => (hl a b h).affine)

end RegisteredPrime
