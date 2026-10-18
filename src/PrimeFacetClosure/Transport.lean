module
public import RegisteredPrime.RegisteredLanguage
@[expose] public section

/-!
New incremental facet-transport algebra.  The bridge is D_{k} P_f in the
existing row convention.  No claim about an actual physical tiling, profile
compiler, or existence of a corresponding graph path is assumed or asserted.
-/
namespace RegisteredPrime.PrimeFacetClosure

private theorem frame_ext {p : Nat} (F G : RegisteredFrame p)
    (hp : F.perm = G.perm) (hn : F.negative = G.negative) : F = G := by
  have hi : F.inverse = G.inverse := by
    funext i
    calc
      F.inverse i = F.inverse (G.perm (G.inverse i)) := by rw [G.right_inverse]
      _ = F.inverse (F.perm (G.inverse i)) := by rw [hp]
      _ = G.inverse i := F.left_inverse _
  cases F
  cases G
  cases hp
  cases hn
  cases hi
  rfl

/-- Keep the index permutation and flip only the specified output normal. -/
def bridge {p : Nat} (F : RegisteredFrame p) (k : Fin p) : RegisteredFrame p :=
  { F with negative := fun i => decide (i = k) }

/-- Keep the index permutation, with no coordinate sign reversals. -/
def unsigned {p : Nat} (F : RegisteredFrame p) : RegisteredFrame p :=
  { F with negative := fun _ => false }

/-- Two composable odd bridges cancel their normal signs, but retain the
complete composed index permutation.  They need not give the identity. -/
theorem bridge_comp_bridge {p : Nat} (F G : RegisteredFrame p) (k : Fin p) :
    (bridge F k).comp (bridge G (F.perm k)) = unsigned (F.comp G) := by
  apply frame_ext
  · rfl
  · funext i
    have he : F.perm i = F.perm k ↔ i = k := by
      constructor
      · intro h
        have hh := congrArg F.inverse h
        simpa only [F.left_inverse] using hh
      · intro h
        exact congrArg F.perm h
    simp only [RegisteredFrame.comp, bridge, unsigned, he]
    cases decide (i = k) <;> rfl

/-- The inverse bridge has the expected exact cancellation. -/
theorem bridge_comp_inverse {p : Nat} (F : RegisteredFrame p) (k : Fin p) :
    (bridge F k).comp (bridge F.inv (F.perm k)) = (identityPose p).frame := by
  rw [bridge_comp_bridge]
  apply frame_ext
  · funext i
    exact F.left_inverse i
  · rfl

/-- For involutive index maps, the two same-map bridges cancel.  This is the
specific algebra used by the g=-1 dense-family argument. -/
theorem involutive_bridge_cancellation {p : Nat} (F : RegisteredFrame p)
    (hF : ∀ i, F.perm (F.perm i) = i) (k : Fin p) :
    (bridge F k).comp (bridge F (F.perm k)) = (identityPose p).frame := by
  rw [bridge_comp_bridge]
  apply frame_ext
  · funext i
    exact hF i
  · rfl

/-- Multiplication by 2 on F_5, with inverse multiplication by 3. -/
def mulTwoFive : RegisteredFrame 5 where
  perm := fun i => ⟨(2 * i.val) % 5, Nat.mod_lt _ (by decide)⟩
  inverse := fun i => ⟨(3 * i.val) % 5, Nat.mod_lt _ (by decide)⟩
  left_inverse := by decide
  right_inverse := by decide
  negative := fun _ => false

/-- An explicit nonidentity even transport already occurs algebraically at
p=5: two g=2 bridges have unsigned slope 4, not slope 1. -/
theorem two_bridges_five_not_identity :
    (bridge mulTwoFive 0).comp (bridge mulTwoFive (mulTwoFive.perm 0)) ≠
      (identityPose 5).frame := by
  intro h
  have he := congrArg (fun F : RegisteredFrame 5 => (F.perm 1).val) h
  change 4 = 1 at he
  contradiction

/-- The exact unsigned result, to prevent a sign-only interpretation. -/
theorem two_bridges_five_unsigned :
    (bridge mulTwoFive 0).comp (bridge mulTwoFive (mulTwoFive.perm 0)) =
      unsigned (mulTwoFive.comp mulTwoFive) :=
  bridge_comp_bridge _ _ _

#print axioms bridge_comp_bridge
#print axioms bridge_comp_inverse
#print axioms involutive_bridge_cancellation
#print axioms two_bridges_five_not_identity
#print axioms two_bridges_five_unsigned
end RegisteredPrime.PrimeFacetClosure
