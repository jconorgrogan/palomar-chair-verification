module

public import ProductClosure.IntegralPoseAlgebra
public import ProductClosure.NativePhysicalFrameRegistration

@[expose] public section

namespace ProductClosure.NativeCompiler
open scoped InnerProductSpace
noncomputable section
variable {m : ℕ} {S : Finset (Polycube.LatticeIndex (m + 1))}
variable [Nonempty (Polycube.Cell S)]

/-- An actual key-companion edge: distinct tiles carry equal whole native
crease complexes. There is no registration or frame premise in this relation. -/
def PhysicalTiling.KeyCompanionEdge {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (_T : PhysicalTiling a f) (i j : ι) : Prop :=
  i ≠ j ∧ ∃ u v : Site S, f i '' creaseComplex a u = f j '' creaseComplex a v

/-- Reachability from the root by a finite path of actual key companions. -/
def PhysicalTiling.KeyReachable {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (root i : ι) : Prop :=
  Relation.ReflTransGen T.KeyCompanionEdge root i

theorem PhysicalTiling.keyCompanionEdge_symm {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (h : T.KeyCompanionEdge i j) :
    T.KeyCompanionEdge j i := by
  obtain ⟨hij, u, v, huv⟩ := h
  exact ⟨Ne.symm hij, v, u, huv.symm⟩

theorem PhysicalTiling.keyReachable_refl {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) (i : ι) : T.KeyReachable i i :=
  Relation.ReflTransGen.refl

theorem PhysicalTiling.keyReachable_of_edge {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (h : T.KeyCompanionEdge i j) :
    T.KeyReachable i j := Relation.ReflTransGen.single h

theorem PhysicalTiling.keyReachable_trans {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j k : ι}
    (hij : T.KeyReachable i j) (hjk : T.KeyReachable j k) : T.KeyReachable i k :=
  hij.trans hjk

theorem PhysicalTiling.keyReachable_symm {J : ℕ} [NeZero m] {ι : Type*}
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (h : T.KeyReachable i j) :
    T.KeyReachable j i := by
  induction h with
  | refl => exact T.keyReachable_refl i
  | tail _ hedge ih => exact ih.head (T.keyCompanionEdge_symm hedge)

/-- Every actual equal-complex contact has the registration already forced by
the unique physical companion. -/
theorem PhysicalTiling.integral_of_equal_crease_complex
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (hji : j ≠ i) (u v : Site S)
    (huv : f i '' creaseComplex a u = f j '' creaseComplex a v) :
    HasIntegralSignedPermutation (relativePlacement (f i) (f j)) := by
  obtain ⟨iv, hiv, heq, hreg⟩ := T.exists_integrally_registered_companion hm i u
  obtain ⟨kv, _, huniq⟩ := T.unique_equal_crease_companion hm i u
  have hv : (j, v) = iv :=
    (huniq (j, v) ⟨hji, huv⟩).trans (huniq iv ⟨hiv, heq⟩).symm
  simpa only [← hv] using hreg

theorem PhysicalTiling.keyCompanionEdge_integral
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {i j : ι} (h : T.KeyCompanionEdge i j) :
    HasIntegralSignedPermutation (relativePlacement (f i) (f j)) := by
  obtain ⟨hij, u, v, huv⟩ := h
  exact T.integral_of_equal_crease_complex hm (Ne.symm hij) u v huv

/-- Registration propagates along every finite path of actual whole-key
companions. The theorem does not assert that all tiles lie in this component. -/
theorem PhysicalTiling.keyReachable_integral
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root i : ι} (h : T.KeyReachable root i) :
    HasIntegralSignedPermutation (relativePlacement (f root) (f i)) := by
  induction h with
  | refl => exact relative_integral_refl (f root)
  | @tail i j hij hedge ih =>
    exact relative_integral_trans ih (T.keyCompanionEdge_integral hm hedge)

/-- Every native key of a reachable tile has a reachable companion. -/
theorem PhysicalTiling.exists_keyReachable_companion
    {J : ℕ} [NeZero m] {ι : Type*} (hm : 2 ≤ m)
    {a : Coefficients S J} {f : ι → Space m ≃ᵢ Space m}
    (T : PhysicalTiling a f) {root i : ι} (h : T.KeyReachable root i) (u : Site S) :
    ∃ iv : ι × Site S, iv.1 ≠ i ∧ T.KeyReachable root iv.1 ∧
      f i '' creaseComplex a u = f iv.1 '' creaseComplex a iv.2 := by
  obtain ⟨iv, hiv, _⟩ := T.unique_equal_crease_companion hm i u
  exact ⟨iv, hiv.1, h.tail ⟨Ne.symm hiv.1, u, iv.2, hiv.2⟩, hiv.2⟩


#print axioms HasIntegralSignedPermutation.refl
#print axioms HasIntegralSignedPermutation.trans
#print axioms HasIntegralSignedPermutation.symm
#print axioms integral_signed_permutation_apply
#print axioms PhysicalTiling.keyCompanionEdge_integral
#print axioms PhysicalTiling.keyReachable_integral
#print axioms PhysicalTiling.exists_keyReachable_companion

end
end ProductClosure.NativeCompiler
