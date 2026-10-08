module
public import RegisteredPrime.ArithmeticAtlasClosure
@[expose] public section
namespace RegisteredPrime

/-- Complete parents in an actual atlas world inherit all directional fine
atlas tests. This is immediate actual tile membership, not a coarse premise. -/
theorem complete_parent_child_arithmetic_atlas (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) (t u : Pose P.p)
    (ht : CompleteParent P W t) (hu : CompleteParent P W u) : ChildArithmeticAtlas P t u :=
  fun a b hc => hl _ _ (ht a) (hu b) hc

/-- The concrete normalized coarse world preserves the explicit arithmetic
atlas. Both directional tests are obtained from actual complete-parent tiles
and common-reference full-pose cancellation. -/
theorem coarsenAt_arithmetic_atlas_legal (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) (t : Pose P.p) (ht : CompleteParent P W t) :
    ArithmeticAtlasLegal P
      (WeakRecognition.coarsenAt P W (ArithmeticAtlasLegal.recognition P W hl) t ht) := by
  intro q r hq hr hc
  let T := t.comp (doubleAnchor q)
  let U := t.comp (doubleAnchor r)
  have hT : CompleteParent P W T := hq
  have hU : CompleteParent P W U := hr
  have hf := complete_parent_child_arithmetic_atlas P W hl T U hT hU
  have hb := complete_parent_child_arithmetic_atlas P W hl U T hU hT
  have he : T.relative U = doubleAnchor (q.relative r) := by
    simp only [T, U, Pose.relative_left_cancel, ← doubleAnchor_relative]
  have hfn := ChildArithmeticAtlas.reframe P T.inv T U hf
  rw [Pose.inv_comp] at hfn
  change ChildArithmeticAtlas P (identityPose P.p) (T.relative U) at hfn
  rw [he] at hfn
  have hbn := ChildArithmeticAtlas.reframe P T.inv U T hb
  rw [Pose.inv_comp] at hbn
  change ChildArithmeticAtlas P (T.relative U) (identityPose P.p) at hbn
  rw [he] at hbn
  have hcn := q.inv.face_contact q r hc
  rw [Pose.inv_comp] at hcn
  change FaceContact (identityPose P.p) (q.relative r) at hcn
  exact arithmetic_atlas_coarse_closed P (q.relative r) hcn hfn hbn

/-- One actual coarse atlas world exists for each already given full atlas
world. This theorem does not assert existence of an initial tiling. -/
theorem arithmetic_atlas_coarse_world_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) :
    ∃ V : RegisteredWorld P.p, ArithmeticAtlasLegal P V := by
  obtain ⟨t, ht, _⟩ := WeakRecognition.complete_parent_cover P W
    (ArithmeticAtlasLegal.recognition P W hl) (fun _ => 0)
  exact ⟨WeakRecognition.coarsenAt P W (ArithmeticAtlasLegal.recognition P W hl) t ht,
    coarsenAt_arithmetic_atlas_legal P W hl t ht⟩

/-- An atlas-legal full world, used only as the state of the constructed
iteration. Its fields describe an existing world and its proved local law. -/
structure AtlasWorld (P : Parameters) where
  world : RegisteredWorld P.p
  legal : ArithmeticAtlasLegal P world

namespace AtlasWorld

/-- Choose an actual complete parent covering one fixed cell to set the next
coordinate origin. This does not assume any hierarchy data. -/
noncomputable def origin (P : Parameters) (V : AtlasWorld P) : Pose P.p :=
  Classical.choose (WeakRecognition.complete_parent_cover P V.world
    (ArithmeticAtlasLegal.recognition P V.world V.legal) (fun _ => 0))

theorem origin_parent (P : Parameters) (V : AtlasWorld P) :
    CompleteParent P V.world (origin P V) :=
  (Classical.choose_spec (WeakRecognition.complete_parent_cover P V.world
    (ArithmeticAtlasLegal.recognition P V.world V.legal) (fun _ => 0))).1

theorem origin_covers_zero (P : Parameters) (V : AtlasWorld P) :
    DoubledOccupies (origin P V) (fun _ => 0) :=
  (Classical.choose_spec (WeakRecognition.complete_parent_cover P V.world
    (ArithmeticAtlasLegal.recognition P V.world V.legal) (fun _ => 0))).2

/-- The actual next full world, with atlas legality proved by the closure
theorem rather than supplied as a step hypothesis. -/
noncomputable def step (P : Parameters) (V : AtlasWorld P) : AtlasWorld P where
  world := WeakRecognition.coarsenAt P V.world
    (ArithmeticAtlasLegal.recognition P V.world V.legal) (origin P V) (origin_parent P V)
  legal := coarsenAt_arithmetic_atlas_legal P V.world V.legal (origin P V) (origin_parent P V)

theorem step_tiles (P : Parameters) (V : AtlasWorld P) (q : Pose P.p) :
    (step P V).world.tiles q ↔
      CompleteParent P V.world ((origin P V).comp (doubleAnchor q)) := Iff.rfl

theorem step_reconstruct (P : Parameters) (V : AtlasWorld P) (q : Pose P.p) :
    V.world.tiles q ↔ ∃ r, (step P V).world.tiles r ∧
      ∃ a : Role P.p, q = (origin P V).comp (refine P r a) :=
  WeakRecognition.coarsenAt_reconstruct P V.world
    (ArithmeticAtlasLegal.recognition P V.world V.legal) (origin P V) (origin_parent P V) q

/-- Ordinary recursion constructs every finite stage of one infinite sequence
of actual full registered worlds. -/
noncomputable def iterate (P : Parameters) (V : AtlasWorld P) : Nat → AtlasWorld P
  | 0 => V
  | n + 1 => step P (iterate P V n)

end AtlasWorld

/-- A fully constructed hierarchy output. The parent partitions are unique
within each world. The normalized coordinate-origin choices are recorded,
without claiming that all coordinate-normalized world sequences are equal. -/
structure AtlasHierarchy (P : Parameters) (W : RegisteredWorld P.p) where
  worlds : Nat → RegisteredWorld P.p
  origins : Nat → Pose P.p
  initial : worlds 0 = W
  atlas_legal : ∀ n, ArithmeticAtlasLegal P (worlds n)
  origin_parent : ∀ n, CompleteParent P (worlds n) (origins n)
  origin_covers_zero : ∀ n, DoubledOccupies (origins n) (fun _ => 0)
  coarse_tiles : ∀ n q, (worlds (n + 1)).tiles q ↔
    CompleteParent P (worlds n) ((origins n).comp (doubleAnchor q))
  reconstruction : ∀ n q, (worlds n).tiles q ↔
    ∃ r, (worlds (n + 1)).tiles r ∧ ∃ a : Role P.p, q = (origins n).comp (refine P r a)
  unique_parent : ∀ n q, (worlds n).tiles q →
    ∃ t : Pose P.p, CompleteParent P (worlds n) t ∧ ParentChild P t q ∧
      ∀ u : Pose P.p, CompleteParent P (worlds n) u → ParentChild P u q → u = t
  parents_cover : ∀ n c, ∃ t : Pose P.p,
    CompleteParent P (worlds n) t ∧ DoubledOccupies t c
  parents_disjoint : ∀ n t u, CompleteParent P (worlds n) t →
    CompleteParent P (worlds n) u → t ≠ u → DoubledDisjoint t u

/-- Every hierarchy field is built from actual weak recognition, concrete
coarsening, and the proved arithmetic-atlas closure. There is no closure
oracle or hierarchy existence premise. -/
noncomputable def buildAtlasHierarchy (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) : AtlasHierarchy P W := by
  let V : AtlasWorld P := ⟨W, hl⟩
  let S : Nat → AtlasWorld P := AtlasWorld.iterate P V
  refine {
    worlds := fun n => (S n).world
    origins := fun n => AtlasWorld.origin P (S n)
    initial := rfl
    atlas_legal := fun n => (S n).legal
    origin_parent := fun n => AtlasWorld.origin_parent P (S n)
    origin_covers_zero := fun n => AtlasWorld.origin_covers_zero P (S n)
    coarse_tiles := ?_
    reconstruction := ?_
    unique_parent := ?_
    parents_cover := ?_
    parents_disjoint := ?_
  }
  · intro n q
    exact AtlasWorld.step_tiles P (S n) q
  · intro n q
    exact AtlasWorld.step_reconstruct P (S n) q
  · intro n q hq
    exact WeakRecognition.registered_unique_parent_pose P (S n).world
      (ArithmeticAtlasLegal.recognition P (S n).world (S n).legal) q hq
  · intro n c
    exact WeakRecognition.complete_parent_cover P (S n).world
      (ArithmeticAtlasLegal.recognition P (S n).world (S n).legal) c
  · intro n t u ht hu hne
    exact WeakRecognition.complete_parent_doubled_disjoint P (S n).world
      (ArithmeticAtlasLegal.recognition P (S n).world (S n).legal) t u ht hu hne

/-- Infinite legal coarsening for every given full arithmetic-atlas world. -/
theorem arithmetic_atlas_hierarchy_exists (P : Parameters) (W : RegisteredWorld P.p)
    (hl : ArithmeticAtlasLegal P W) : Nonempty (AtlasHierarchy P W) :=
  ⟨buildAtlasHierarchy P W hl⟩

/-- An actual E-legal world has an infinite hierarchy of actual registered
worlds legal for the explicit coarsening-closed atlas. Generated E itself is
not identified with that atlas or claimed for the higher levels. -/
theorem registered_infinite_atlas_hierarchy (P : Parameters) (W : RegisteredWorld P.p)
    (hl : W.Legal P) : Nonempty (AtlasHierarchy P W) :=
  arithmetic_atlas_hierarchy_exists P W (arithmetic_atlas_legal_of_E P W hl)

end RegisteredPrime
