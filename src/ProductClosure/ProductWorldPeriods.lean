module

public import ProductClosure.ProductWorldExistence

@[expose] public section

/-!
# Product periods project to the complete factor worlds

The state maps here can be actual translations of full Euclidean placed
poses. Nothing in the projection theorem restricts a period to an integer
vector or forgets frame states. The geometric period-transfer theorem must
supply the registered world and its actual state translation map.
-/
namespace ProductClosure.World

open Set
noncomputable section
universe u v w z

/-- A block map preserves a nonempty Cartesian product precisely when its
factor maps preserve both factor state sets. -/
theorem block_image_eq_iff {A : Type u} {B : Type v}
    (s : Set A) (t : Set B) (hs : s.Nonempty) (ht : t.Nonempty)
    (f : A → A) (g : B → B) :
    Prod.map f g '' (s ×ˢ t) = s ×ˢ t ↔ f '' s = s ∧ g '' t = t := by
  constructor
  · intro h
    constructor
    · ext a
      constructor
      · rintro ⟨a₀, ha₀, rfl⟩
        obtain ⟨b, hb⟩ := ht
        have hab : (f a₀, g b) ∈ Prod.map f g '' (s ×ˢ t) :=
          ⟨(a₀, b), ⟨ha₀, hb⟩, rfl⟩
        rw [h] at hab
        exact hab.1
      · intro ha
        obtain ⟨b, hb⟩ := ht
        have hab : (a, b) ∈ Prod.map f g '' (s ×ˢ t) := by rw [h]; exact ⟨ha, hb⟩
        obtain ⟨p, hp, heq⟩ := hab
        exact ⟨p.1, hp.1, congrArg Prod.fst heq⟩
    · ext b
      constructor
      · rintro ⟨b₀, hb₀, rfl⟩
        obtain ⟨a, ha⟩ := hs
        have hab : (f a, g b₀) ∈ Prod.map f g '' (s ×ˢ t) :=
          ⟨(a, b₀), ⟨ha, hb₀⟩, rfl⟩
        rw [h] at hab
        exact hab.2
      · intro hb
        obtain ⟨a, ha⟩ := hs
        have hab : (a, b) ∈ Prod.map f g '' (s ×ˢ t) := by rw [h]; exact ⟨ha, hb⟩
        obtain ⟨p, hp, heq⟩ := hab
        exact ⟨p.2, hp.2, congrArg Prod.snd heq⟩
  · rintro ⟨hf, hg⟩
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hf ▸ Set.mem_image_of_mem f hq.1, hg ▸ Set.mem_image_of_mem g hq.2⟩
    · intro hp
      have ha : p.1 ∈ f '' s := hf.symm ▸ hp.1
      have hb : p.2 ∈ g '' t := hg.symm ▸ hp.2
      obtain ⟨a, ha, hea⟩ := ha
      obtain ⟨b, hb, heb⟩ := hb
      exact ⟨(a, b), ⟨ha, hb⟩, Prod.ext hea heb⟩

namespace CompleteTiling
variable {X : Type u} {A : Type v} {cells : A → Set X}

/-- A period as equality of the actual set of full placed tile states. -/
def HasStatePeriod (W : CompleteTiling cells) (translate : A → A) : Prop :=
  translate '' W.tiles = W.tiles

/-- A tile-set period induces owner equivariance whenever the state map has
the stated genuine action on occupied cells. This requires no preferred
labeling of unmarked physical tile copies. -/
theorem owner_equivariant (W : CompleteTiling cells)
    (translate : A → A) (move : X → X)
    (hperiod : W.HasStatePeriod translate)
    (hmove : ∀ a x, x ∈ cells a → move x ∈ cells (translate a)) (x : X) :
    W.owner (move x) = translate (W.owner x) := by
  apply W.owner_eq_of_mem
  · exact hperiod ▸ Set.mem_image_of_mem translate (W.owner_mem x)
  · exact hmove _ _ (W.mem_owner x)

/-- Aperiodicity parameterized by the genuine translation action on states. -/
def Aperiodic {V : Type w} [Zero V] (W : CompleteTiling cells)
    (translate : V → A → A) : Prop :=
  ∀ v, W.HasStatePeriod (translate v) → v = 0

variable {m n : ℕ} {A : Type u} {B : Type v}
  {cellsA : A → Set (Lattice m)} {cellsB : B → Set (Lattice n)}
  {MA : A → A → Prop} {MB : B → B → Prop}
variable (W : CompleteTiling (productCells cellsA cellsB))

/-- Any block translation period projects to both complete factor worlds,
and the converse holds as well. -/
theorem period_iff_factor_periods
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    (translateA : A → A) (translateB : B → B) :
    W.HasStatePeriod (Prod.map translateA translateB) ↔
      (W.activeFactor hlegal hsepA hsepB).HasStatePeriod translateA ∧
      (W.passiveFactor hlegal hsepA hsepB).HasStatePeriod translateB := by
  unfold HasStatePeriod
  change Prod.map translateA translateB '' W.tiles = W.tiles ↔
    translateA '' Set.range W.activeOwner = Set.range W.activeOwner ∧
    translateB '' Set.range W.passiveOwner = Set.range W.passiveOwner
  rw [W.tiles_cartesian hlegal hsepA hsepB]
  exact block_image_eq_iff (Set.range W.activeOwner) (Set.range W.passiveOwner)
    ⟨W.activeOwner 0, 0, rfl⟩ ⟨W.passiveOwner 0, 0, rfl⟩ translateA translateB

/-- Factor aperiodicity kills both components of every product period.
The parameter spaces may be full real Euclidean spaces. -/
theorem product_period_zero {VA : Type w} {VB : Type z} [Zero VA] [Zero VB]
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    (translateA : VA → A → A) (translateB : VB → B → B)
    (hA : (W.activeFactor hlegal hsepA hsepB).Aperiodic translateA)
    (hB : (W.passiveFactor hlegal hsepA hsepB).Aperiodic translateB)
    (u : VA) (v : VB)
    (hperiod : W.HasStatePeriod (Prod.map (translateA u) (translateB v))) :
    u = 0 ∧ v = 0 := by
  obtain ⟨hu, hv⟩ := (W.period_iff_factor_periods hlegal hsepA hsepB
    (translateA u) (translateB v)).mp hperiod
  exact ⟨hA u hu, hB v hv⟩

/-- The complete product world is aperiodic under the product translation
action whenever both decoded factor worlds are aperiodic. -/
theorem product_aperiodic {VA : Type w} {VB : Type z} [Zero VA] [Zero VB]
    (hlegal : W.IsLegal ProductAdjacent (ProductLanguage MA MB))
    (hsepA : Separates cellsA MA) (hsepB : Separates cellsB MB)
    (translateA : VA → A → A) (translateB : VB → B → B)
    (hA : (W.activeFactor hlegal hsepA hsepB).Aperiodic translateA)
    (hB : (W.passiveFactor hlegal hsepA hsepB).Aperiodic translateB) :
    W.Aperiodic (fun uv : VA × VB => Prod.map (translateA uv.1) (translateB uv.2)) := by
  intro uv huv
  obtain ⟨hu, hv⟩ := W.product_period_zero hlegal hsepA hsepB
    translateA translateB hA hB uv.1 uv.2 huv
  exact Prod.ext hu hv

#print axioms period_iff_factor_periods
#print axioms product_period_zero
#print axioms product_aperiodic

end CompleteTiling
end
end ProductClosure.World
