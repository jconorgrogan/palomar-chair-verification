module

public import SparseMonotiles.CompactTranslationFrames
public import SparseMonotiles.KeyCovariance
public import SparseMonotiles.CarrierHierarchyPeriods
public import Mathlib.Analysis.Normed.Affine.MazurUlam

@[expose] public section

/-!
# Physical periods in registered, translation-equivariant frames

The registration premise is explicit: one ambient affine isometry normalizes
all chosen physical frames to signed integral poses. Compactness supplies frames
that commute with every physical period. This module transports a physical
period to an integer period of their pose range; it does not assert registration
or carrier coverage for the concrete bodies.
-/
namespace SparseMonotiles
open Set Contact CarrierHierarchy

noncomputable def integerVectorPoint {d : ℕ} (v : Cell d) : Point d :=
  rationalPoint (fun i => (v i : ℚ))

@[simp] theorem integerVectorPoint_apply {d : ℕ} (v : Cell d) (i : Fin d) :
    integerVectorPoint v i = (v i : ℝ) := by
  simp [integerVectorPoint, rationalPoint]

@[simp] theorem integerVectorPoint_zero {d : ℕ} : integerVectorPoint (0 : Cell d) = 0 := by
  ext i
  simp

/-- The integer pose encoding is faithful to its actual Euclidean isometry. -/
theorem Contact.Pose.euclidean_injective {d : ℕ} :
    Function.Injective (fun p : Pose d => p.euclidean) := by
  intro p q hpq
  have hfun : ∀ (x : Point d) (i : Fin d), (p.sign i : ℝ) * x (p.perm i) + (p.shift i : ℝ) =
      (q.sign i : ℝ) * x (q.perm i) + (q.shift i : ℝ) := by
    intro x i
    simpa only [Pose.euclidean_apply] using congrArg (fun f : Point d ≃ᵃⁱ[ℝ] Point d => f x i) hpq
  have hshift : p.shift = q.shift := by
    funext i
    have h := hfun (0 : Point d) i
    simp only [PiLp.zero_apply, mul_zero, zero_add] at h
    exact_mod_cast h
  have hperm : p.perm = q.perm := by
    apply Equiv.ext
    intro i
    by_contra hi
    let x : Point d := SparseMonotiles.rationalPoint (Pi.single (p.perm i) 1)
    have h := hfun x i
    have hp : x (p.perm i) = 1 := by simp [x, SparseMonotiles.rationalPoint]
    have hq : x (q.perm i) = 0 := by simp [x, SparseMonotiles.rationalPoint, Ne.symm hi]
    rw [hp,hq,hshift] at h
    cases hb : p.negative i <;> simp [Pose.sign,hb] at h
  have hneg : p.negative = q.negative := by
    funext i
    let x : Point d := SparseMonotiles.rationalPoint (fun _ => 1)
    have h := hfun x i
    have hx : ∀ j, x j = 1 := by intro j; simp [x,SparseMonotiles.rationalPoint]
    rw [hx,hx,hshift] at h
    cases hp : p.negative i <;> cases hq : q.negative i <;>
      simp only [Pose.sign,hp,hq,Bool.false_eq_true,if_false,if_true,
        Int.cast_one,Int.cast_neg,one_mul,neg_one_mul] at h <;> first | rfl | linarith
  cases p
  cases q
  simp_all only [Pose.mk.injEq]

theorem translatePose_euclidean {d : ℕ} (v : Cell d) (p : Pose d) (x : Point d) :
    (translatePose v p).euclidean x = p.euclidean x + integerVectorPoint v := by
  ext i
  simp [Pose.euclidean_apply,translatePose,Pose.sign,Int.cast_add,add_assoc]

@[simp] theorem translate_neg_cancel {d : ℕ} (v : Point d) (A : Set (Point d)) :
    translate (-v) (translate v A) = A := by
  simp only [translate, Set.image_image]
  have hf : (fun x : Point d => (x+v)+ -v) = id := by funext x; simp
  rw [hf,Set.image_id]

@[simp] theorem translate_add_neg_cancel {d : ℕ} (v : Point d) (A : Set (Point d)) :
    translate v (translate (-v) A) = A := by
  simpa only [neg_neg] using translate_neg_cancel (-v) A

theorem IsPeriod.neg {d : ℕ} {tiles : Set (Set (Point d))} {v : Point d}
    (hv : IsPeriod tiles v) : IsPeriod tiles (-v) := by
  intro A
  simpa only [translate_add_neg_cancel] using (hv (translate (-v) A)).symm

noncomputable def periodTile {d : ℕ} {tiles : Set (Set (Point d))}
    {v : Point d} (hv : IsPeriod tiles v) (A : tiles) : tiles :=
  ⟨translate v A,(hv A).mp A.property⟩

@[simp] theorem periodTile_neg {d : ℕ} {tiles : Set (Set (Point d))}
    {v : Point d} (hv : IsPeriod tiles v) (A : tiles) :
    periodTile hv (periodTile hv.neg A) = A := by
  apply Subtype.ext
  exact translate_add_neg_cancel v A

private theorem affine_translation {d : ℕ} (e : Point d ≃ᵃⁱ[ℝ] Point d)
    (x v : Point d) : e (x+v) = e x + e.linearIsometryEquiv v := by
  have h : e (x+v) - e x = e.linearIsometryEquiv ((x+v)-x) :=
    (e.map_vsub (x+v) x).symm
  simp only [add_sub_cancel_left] at h
  exact eq_add_of_sub_eq' h

/-- Any period becomes an integral vector in a globally registered frame. The
pose range is exactly invariant under that integer translation. -/
theorem physical_period_lifts_to_integer_pose_period {d : ℕ}
    {tiles : Set (Set (Point d))} (hne : tiles.Nonempty)
    (g : tiles → Point d ≃ᵢ Point d)
    (hequiv : ∀ v, ∀ hv : IsPeriod tiles v, ∀ A : tiles,
      g (periodTile hv A) = (g A).trans (translationIsometry v))
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x)
    {v : Point d} (hv : IsPeriod tiles v) :
    ∃ w : Cell d, e.linearIsometryEquiv v = integerVectorPoint w ∧
      ∀ p, p ∈ Set.range q ↔ translatePose w p ∈ Set.range q := by
  obtain ⟨A,hA⟩ := hne
  let A₀ : tiles := ⟨A,hA⟩
  let w : Cell d := fun i => (q (periodTile hv A₀)).shift i - (q A₀).shift i
  have hmove : ∀ B : tiles, ∀ x,
      (q (periodTile hv B)).euclidean x =
        (q B).euclidean x + e.linearIsometryEquiv v := by
    intro B x
    rw [← hreg,hequiv]
    change e (g B x+v) = _
    rw [affine_translation,hreg]
  have hw : e.linearIsometryEquiv v = integerVectorPoint w := by
    ext i
    have h := congrArg (fun x : Point d => x i) (hmove A₀ 0)
    simp only [Pose.euclidean_apply,PiLp.zero_apply,mul_zero,zero_add,PiLp.add_apply] at h
    simp only [integerVectorPoint_apply,w,Int.cast_sub]
    linarith
  have hqmove : ∀ B : tiles, q (periodTile hv B) = translatePose w (q B) := by
    intro B
    apply Contact.Pose.euclidean_injective
    apply DFunLike.ext
    intro x
    rw [hmove,hw,translatePose_euclidean]
  refine ⟨w,hw,?_⟩
  intro p
  constructor
  · rintro ⟨B,rfl⟩
    exact ⟨periodTile hv B,hqmove B⟩
  · rintro ⟨B,hB⟩
    refine ⟨periodTile hv.neg B,?_⟩
    have h := hqmove (periodTile hv.neg B)
    rw [periodTile_neg,hB] at h
    have h' := congrArg (translatePose (-w)) h
    simpa only [translatePose_neg] using h'.symm

/-- A zero integer-period endpoint applies to the physical period once its
registered-world range has been established. -/
theorem physical_period_zero_of_registered_frame_world {d : ℕ}
    {tiles : Set (Set (Point d))} (hne : tiles.Nonempty)
    (g : tiles → Point d ≃ᵢ Point d)
    (hequiv : ∀ v, ∀ hv : IsPeriod tiles v, ∀ A : tiles,
      g (periodTile hv A) = (g A).trans (translationIsometry v))
    (e : Point d ≃ᵃⁱ[ℝ] Point d) (q : tiles → Pose d)
    (hreg : ∀ A x, e (g A x) = (q A).euclidean x)
    (W : RegisteredWorld d) (hW : W.tiles = Set.range q)
    (hzero : ∀ w, W.IsPeriod w → w=0)
    {v : Point d} (hv : IsPeriod tiles v) : v=0 := by
  obtain ⟨w,hw,hperiod⟩ := physical_period_lifts_to_integer_pose_period hne g hequiv e q hreg hv
  have hw0 : w=0 := hzero w (by simpa only [RegisteredWorld.IsPeriod,hW] using hperiod)
  rw [hw0,integerVectorPoint_zero] at hw
  exact e.linearIsometryEquiv.injective (by simpa using hw)

#print axioms Contact.Pose.euclidean_injective
#print axioms physical_period_lifts_to_integer_pose_period
#print axioms physical_period_zero_of_registered_frame_world
end SparseMonotiles
