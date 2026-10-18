module

public import ClarkSeed.ProfileMating

@[expose] public section

/-! Faithful change of coordinates for literal sparse profiles. In particular,
integer vertices scaled into Euclidean space retain their full finite profile,
including the bump bit, without identifying unlike labels or shapes. -/
namespace ClarkSeed.ProfileMating
noncomputable section
variable {X Y : Type*}

def embedKey (f : X → Y) (k : Key X) : Key Y := by
  classical
  exact (k.1.image f, k.2)

def embed (f : X → Y) (P : Profile X) : Profile Y := by
  classical
  exact P.image (embedKey f)

theorem embedKey_injective (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (embedKey f) := by
  classical
  rintro ⟨V,b⟩ ⟨W,c⟩ h
  have hV : V = W := Finset.image_injective hf (congrArg Prod.fst h)
  have hb : b = c := congrArg Prod.snd h
  exact Prod.ext hV hb

theorem embed_injective (f : X → Y) (hf : Function.Injective f) :
    Function.Injective (embed f) := by
  classical
  exact Finset.image_injective (embedKey_injective f hf)

theorem embedKey_move (f : X → Y) (g : X ≃ X) (h : Y ≃ Y)
    (commute : ∀ x, f (g x) = h (f x)) (k : Key X) :
    embedKey f (moveKey g k) = moveKey h (embedKey f k) := by
  classical
  apply Prod.ext
  · simp only [embedKey, moveKey, Finset.image_image]
    congr 1
    funext x
    exact commute x
  · rfl

@[simp] theorem embedKey_flip (f : X → Y) (k : Key X) :
    embedKey f (flipKey k) = flipKey (embedKey f k) := rfl

theorem embed_move (f : X → Y) (g : X ≃ X) (h : Y ≃ Y)
    (commute : ∀ x, f (g x) = h (f x)) (P : Profile X) :
    embed f (move g P) = move h (embed f P) := by
  classical
  simp only [embed, move, Finset.image_image]
  congr 1
  funext k
  exact embedKey_move f g h commute k

@[simp] theorem embed_flip (f : X → Y) (P : Profile X) :
    embed f (flip P) = flip (embed f P) := by
  classical
  simp only [embed, flip, Finset.image_image]
  rfl

theorem embed_mate (f : X → Y) (g : X ≃ X) (h : Y ≃ Y)
    (commute : ∀ x, f (g x) = h (f x)) (P : Profile X) :
    embed f (mate g P) = mate h (embed f P) := by
  rw [mate, embed_move f g h commute, embed_flip]
  rfl

/-- Euclidean literal-profile equality reflects back to the complete original
integer vertex profile, once the coordinate map is proved injective. -/
theorem embedded_mating_iff (f : X → Y) (hf : Function.Injective f)
    (g : X ≃ X) (h : Y ≃ Y) (commute : ∀ x, f (g x) = h (f x))
    (P Q : Profile X) :
    embed f P = mate h (embed f Q) ↔ P = mate g Q := by
  rw [← embed_mate f g h commute]
  exact (embed_injective f hf).eq_iff

#print axioms embed_injective
#print axioms embedded_mating_iff
end
end ClarkSeed.ProfileMating
