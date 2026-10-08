module


@[expose] public section

/-!
# Definitions for the uniform (all-dimension) theorems

Core Lean 4 only (no Mathlib). Axes / residues are natural numbers `i < n`;
functions `Nat → _` are only ever evaluated below the stated bound.
-/
namespace Uniform

/-- `n` is prime. Core Lean has no `Nat.Prime`. -/
def IsPrime (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

/-- `σ` restricts to a permutation of `{0, …, n-1}` (maps into it, injective on it). -/
def IsPermOn (n : Nat) (σ : Nat → Nat) : Prop :=
  (∀ i, i < n → σ i < n) ∧ (∀ i j, i < n → j < n → σ i = σ j → i = j)

/-- The ordered pairs `(i, j)` with `i < j < n`. -/
def pairs : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => pairs n ++ (List.range n).map (fun i => (i, n))

/-- Number of inversions of `σ` on `{0, …, n-1}`. -/
def invCount (n : Nat) (σ : Nat → Nat) : Nat :=
  (pairs n).countP (fun q => decide (σ q.2 < σ q.1))

/-- Sign of a permutation: `(-1)^(number of inversions)`. -/
def permSign (n : Nat) (σ : Nat → Nat) : Int := (-1) ^ invCount n σ

/-- A frame = signed permutation matrix `M` with `M[i, perm i] = (if neg i then -1 else 1)`,
i.e. `(M x)_i = ± x_(perm i)` (convention `(P_f x)_i = x_(f i)`). -/
structure Frame where
  perm : Nat → Nat
  neg  : Nat → Bool

/-- Matrix product `M_F * M_C`. -/
def Frame.comp (F C : Frame) : Frame :=
  ⟨fun i => C.perm (F.perm i), fun i => xor (F.neg i) (C.neg (F.perm i))⟩

/-- Identity frame. -/
def Frame.id : Frame := ⟨fun i => i, fun _ => false⟩

/-- Number of negative signs among the first `d` rows. -/
def negCount (d : Nat) (s : Nat → Bool) : Nat := (List.range d).countP s

/-- Product of the `d` signs, as `±1`. -/
def signProd (d : Nat) (s : Nat → Bool) : Int :=
  ((List.range d).map (fun i => if s i then (-1 : Int) else 1)).prod

/-- A rotation: `sign(perm) * prod(signs) = +1` (determinant `+1`). -/
def IsRotation (d : Nat) (F : Frame) : Prop :=
  IsPermOn d F.perm ∧ permSign d F.perm * signProd d F.neg = 1

/-! ## Descent through outer children (U2) -/

/-- Translation (doubled coordinates) of the outer child at corner `b`: `4 * 1_b`. -/
def cornerT (b : Nat → Bool) (j : Nat) : Int := if b j then 4 else 0

/-- One substitution step into the outer child at corner `b`.
State = (frame, translation in doubled coordinates); `T' = 2 T + M_F (4 * 1_b)`. -/
def step (child : (Nat → Bool) → Frame) (st : Frame × (Nat → Int)) (b : Nat → Bool) :
    Frame × (Nat → Int) :=
  (st.1.comp (child b),
   fun i => 2 * st.2 i + (if st.1.neg i then -1 else 1) * cornerT b (st.1.perm i))

/-- The tile reached from the level-0 tile through the outer children `bs` (top level first). -/
def descend (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool)) : Frame × (Nat → Int) :=
  bs.foldl (step child) (Frame.id, fun _ => 0)

/-- Unit-cell coordinate `x_i` of the tile: `(T_i - 2 [row i negative]) / 2`. -/
def cell (st : Frame × (Nat → Int)) (i : Nat) : Int :=
  (st.2 i - 2 * (if st.1.neg i then 1 else 0)) / 2

/-- `x_0 xor x_1 xor … xor x_(d-1)`. -/
def xorAll (d : Nat) (x : Nat → Nat) : Nat :=
  (List.range d).foldl (fun acc i => acc ^^^ x i) 0

/-- World digit of axis `i` when the parent frame is `F` and the child is at corner `b`. -/
def worldDigit (F : Frame) (b : Nat → Bool) (i : Nat) : Bool := xor (b (F.perm i)) (F.neg i)

/-- Every child used is a rotation whose sign mask is its corner support. -/
def ProperChildren (d : Nat) (child : (Nat → Bool) → Frame) (bs : List (Nat → Bool)) : Prop :=
  ∀ b ∈ bs, IsRotation d (child b) ∧ ∀ i, i < d → (child b).neg i = b i

/-! ## Supports of `F_p` and the substitution `Λ(μ, g)` (U1, U3, U4) -/

/-- A nonempty proper support of `Fin n`. -/
def NonemptyProper {n : Nat} (A : Fin n → Bool) : Prop :=
  (∃ i, A i = true) ∧ (∃ i, A i = false)

/-- A nonempty proper support of `{0, …, p-1}`. -/
def NonemptyProperOn (p : Nat) (A : Nat → Bool) : Prop :=
  (∃ i, i < p ∧ A i = true) ∧ (∃ i, i < p ∧ A i = false)

/-- `|A|`. -/
def suppCard (p : Nat) (A : Nat → Bool) : Nat := (List.range p).countP A

/-- `sum A` (as a natural number). -/
def suppSum (p : Nat) (A : Nat → Bool) : Nat := ((List.range p).filter A).sum

/-- `z_A`: the least `z < p` with `|A| * z ≡ sum A (mod p)` (0 if none). -/
def zA (p : Nat) (A : Nat → Bool) : Nat :=
  ((List.range p).find? (fun z => (suppCard p A * z) % p == suppSum p A % p)).getD 0

/-- `f_A(i) = μ g^k (i - z_A)` in `F_p`, `k = |A|`. -/
def lamPerm (p mu g : Nat) (A : Nat → Bool) (i : Nat) : Nat :=
  (mu * g ^ suppCard p A * (i + p - zA p A)) % p

/-- Child frame `h_A = D_A P_(f_A)` of `Λ(μ, g)`: permutation `f_A`, sign mask `A`. -/
def lamChild (p mu g : Nat) (A : Nat → Bool) : Frame := ⟨lamPerm p mu g A, A⟩

/-- `g` is a square mod `p`. -/
def IsSquareMod (p g : Nat) : Prop := ∃ x, (x * x) % p = g % p

/-- Multiplication by `a` on `Z/p`. -/
def mulMap (p a : Nat) : Nat → Nat := fun i => (a * i) % p

/-- `A + 1 = {a + 1 : a ∈ A}` in `F_p`. -/
def shiftSupp (p : Nat) (A : Nat → Bool) : Nat → Bool := fun j => A ((j + p - 1) % p)

/-- `ρ A = {ρ a : a ∈ A}`, given `ρ'` with `ρ ρ' ≡ 1`: `j ∈ ρA ↔ ρ' j ∈ A`. -/
def scaleSupp (p ρ' : Nat) (A : Nat → Bool) : Nat → Bool := fun j => A ((ρ' * j) % p)

/-- The positive scalar frame `M_ρ`: `(M_ρ x)_i = x_(ρ i)`. -/
def scalarFrame (p ρ : Nat) : Frame := ⟨fun i => (ρ * i) % p, fun _ => false⟩

end Uniform
