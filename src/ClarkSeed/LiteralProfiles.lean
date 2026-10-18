module

public import ClarkSeed.PoseAdapter
public import ClarkSeed.ProfileEmbedding

@[expose] public section

/-! Faithful binding of the recovered integer-vertex CLARK profiles to actual
Euclidean finite vertex sets. The original mating action flips bump exactly
once; no assumption of a group action on the old keys is made. -/
namespace ClarkSeed.LiteralProfiles
noncomputable section
open SparseMonotiles ProductClosure.NativeCompiler
open ProfileMating PoseAdapter
variable {m : ℕ}

def scaledVertex (den : ℤ) (x : Contact.ScaledPoint (m+1)) : Space m :=
  WithLp.toLp 2 (fun i => (x i : ℝ) / (den : ℝ))

@[simp] theorem scaledVertex_apply (den : ℤ) (x : Contact.ScaledPoint (m+1))
    (i : Fin (m+1)) : scaledVertex den x i = (x i : ℝ) / (den : ℝ) := rfl

theorem scaledVertex_injective (den : ℤ) (hden : den ≠ 0) :
    Function.Injective (scaledVertex (m := m) den) := by
  intro x y h
  funext i
  have he := congrArg (fun z : Space m => z i) h
  change (x i : ℝ) / (den : ℝ) = (y i : ℝ) / (den : ℝ) at he
  have hd : (den : ℝ) ≠ 0 := by exact_mod_cast hden
  have hi : (x i : ℝ) = (y i : ℝ) := (div_left_inj' hd).mp he
  exact_mod_cast hi

theorem scaledVertex_pose (p : Contact.Pose (m+1)) (den : ℤ) (hden : den ≠ 0)
    (x : Contact.ScaledPoint (m+1)) :
    scaledVertex den (p.scaledPoint den x) =
      PhysicalRegistration.NativeChair.poseIsometry (toRegistered p) (scaledVertex den x) := by
  ext i
  exact (scaledPoint_realizes p den hden x i).symm

def literalKey (den : ℤ) (k : Contact.VertexKey (m+1)) : Key (Space m) := by
  classical
  exact (k.vertices.image (scaledVertex den), k.bump)

def literalProfile (den : ℤ) (P : Finset (Contact.VertexKey (m+1))) : Profile (Space m) := by
  classical
  exact P.image (literalKey den)

theorem literalKey_injective (den : ℤ) (hden : den ≠ 0) :
    Function.Injective (literalKey (m := m) den) := by
  classical
  rintro ⟨V,b⟩ ⟨W,c⟩ h
  have hV : V = W := Finset.image_injective (scaledVertex_injective den hden) (congrArg Prod.fst h)
  have hb : b = c := congrArg Prod.snd h
  cases hV
  cases hb
  rfl

theorem literalProfile_injective (den : ℤ) (hden : den ≠ 0) :
    Function.Injective (literalProfile (m := m) den) := by
  classical
  exact Finset.image_injective (literalKey_injective den hden)

/-- Exact original key mating, including its one Boolean coefficient flip. -/
theorem literalKey_mate (den : ℤ) (hden : den ≠ 0)
    (p : Contact.Pose (m+1)) (k : Contact.VertexKey (m+1)) :
    literalKey den (p.key den k) =
      moveKey (PhysicalRegistration.NativeChair.poseIsometry (toRegistered p)).toEquiv
        (flipKey (literalKey den k)) := by
  classical
  apply Prod.ext
  · simp only [literalKey, Contact.Pose.key, moveKey, flipKey, Finset.image_image]
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,(scaledVertex_pose p den hden x).symm⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,scaledVertex_pose p den hden x⟩
  · rfl

theorem literalProfile_mate (den : ℤ) (hden : den ≠ 0)
    (p : Contact.Pose (m+1)) (P : Finset (Contact.VertexKey (m+1))) :
    literalProfile den (P.image (p.key den)) =
      mate (PhysicalRegistration.NativeChair.poseIsometry (toRegistered p)).toEquiv
        (literalProfile den P) := by
  classical
  simp only [literalProfile, mate, move, ProfileMating.flip, Finset.image_image]
  ext y
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k,hk,(literalKey_mate den hden p k).symm⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨k,hk,literalKey_mate den hden p k⟩

/-- Full Euclidean profile equality is equivalent to the recovered exact
integer-vertex mating equation, preserving all sparse profile information. -/
theorem literalProfile_mating_iff (den : ℤ) (hden : den ≠ 0)
    (p : Contact.Pose (m+1)) (P Q : Finset (Contact.VertexKey (m+1))) :
    literalProfile den P =
      mate (PhysicalRegistration.NativeChair.poseIsometry (toRegistered p)).toEquiv
        (literalProfile den Q) ↔ P = Q.image (p.key den) := by
  rw [← literalProfile_mate den hden p Q]
  exact (literalProfile_injective den hden).eq_iff

#print axioms scaledVertex_injective
#print axioms literalKey_mate
#print axioms literalProfile_mating_iff
end
end ClarkSeed.LiteralProfiles
