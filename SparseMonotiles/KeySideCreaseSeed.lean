module

public import SparseMonotiles.KeySideFacePatch

@[expose] public section

/-! An explicit relative-interior point of every distinct-axis side-side crease.
Only the actual positive key height and apex-to-base-side distances are used.
There is no generic-point, rank, or nonempty-face premise. -/
namespace SparseMonotiles

noncomputable def keySideCreasePoint {n : ℕ} (k : KeyData (n+1))
    (i j : Fin n) (b c : Bool) : Point (n+1) :=
  (pointPyramidEquiv n).symm
    ((fun r => if r=i then ((if b then keyPyramidHi k i else keyPyramidLo k i)+keyPyramidApex k i)/2
      else if r=j then ((if c then keyPyramidHi k j else keyPyramidLo k j)+keyPyramidApex k j)/2
      else keyPyramidApex k r), keyPyramidHeight k/2)

@[simp] theorem keySideCreasePoint_last {n : ℕ} (k : KeyData (n+1))
    (i j : Fin n) (b c : Bool) :
    keySideCreasePoint k i j b c (Fin.last n) = keyPyramidHeight k/2 :=
  congrArg Prod.snd ((pointPyramidEquiv n).apply_symm_apply _)

@[simp] theorem keySideCreasePoint_tangent {n : ℕ} (k : KeyData (n+1))
    (i j r : Fin n) (b c : Bool) :
    keySideCreasePoint k i j b c r.castSucc =
      if r=i then ((if b then keyPyramidHi k i else keyPyramidLo k i)+keyPyramidApex k i)/2
      else if r=j then ((if c then keyPyramidHi k j else keyPyramidLo k j)+keyPyramidApex k j)/2
      else keyPyramidApex k r :=
  congrArg (fun z : PyramidPoint n => z.1 r) ((pointPyramidEquiv n).apply_symm_apply _)

theorem keySideCreasePoint_side_slack {n : ℕ} (k : KeyData (n+1))
    (i j r : Fin n) (hij : i ≠ j) (b c s : Bool) :
    keyPyramidHalfspaceSlack k (.inr (r,s)) (keySideCreasePoint k i j b c) =
      (keyPyramidHeight k/2) *
        (if r=i then if s=b then 0 else keyPyramidHi k i-keyPyramidLo k i
          else if r=j then if s=c then 0 else keyPyramidHi k j-keyPyramidLo k j
          else keySideDistance k r s) := by
  by_cases hri : r=i
  · subst r
    cases b <;> cases c <;> cases s <;>
      simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
        keyPyramidHalfspaceNormal_apply,keySideCreasePoint_tangent,keySideDistance,hij] <;> ring
  · by_cases hrj : r=j
    · subst r
      cases b <;> cases c <;> cases s <;>
        simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideCreasePoint_tangent,keySideDistance,hri] <;> ring
    · cases b <;> cases c <;> cases s <;>
        simp [keyPyramidHalfspaceSlack,keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideCreasePoint_tangent,keySideDistance,hri,hrj] <;> ring

theorem keySideCreasePoint_full_slacks {n : ℕ} (k : KeyData (n+1))
    (hh : 0 < keyPyramidHeight k) (hd : ∀ r s, 0 < keySideDistance k r s)
    (i j : Fin n) (hij : i ≠ j) (b c : Bool) :
    keyPyramidHalfspaceSlack k (.inr (i,b)) (keySideCreasePoint k i j b c) = 0 ∧
    keyPyramidHalfspaceSlack k (.inr (j,c)) (keySideCreasePoint k i j b c) = 0 ∧
    ∀ l : PyramidHalfspaceIndex n, l ≠ .inr (i,b) → l ≠ .inr (j,c) →
      0 < keyPyramidHalfspaceSlack k l (keySideCreasePoint k i j b c) := by
  have hwidth (r : Fin n) : 0 < keyPyramidHi k r-keyPyramidLo k r := by
    have hlo := hd r false
    have hhi := hd r true
    simp only [keySideDistance,Bool.false_eq_true,if_false,if_true] at hlo hhi
    linarith
  refine ⟨?_,?_,?_⟩
  · rw [keySideCreasePoint_side_slack k i j i hij]
    simp
  · rw [keySideCreasePoint_side_slack k i j j hij]
    simp [Ne.symm hij]
  · intro l hli hlj
    rcases l with s | ⟨r,s⟩
    · cases s <;> change 0 < _ - _
      · simp only [keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideCreasePoint_last]
        linarith
      · simp only [keyPyramidHalfspaceBound,pyramidHalfspaceBound,
          keyPyramidHalfspaceNormal_apply,keySideCreasePoint_last]
        linarith
    · rw [keySideCreasePoint_side_slack k i j r hij]
      apply mul_pos (by linarith)
      by_cases hri : r=i
      · subst r
        have hsb : s ≠ b := fun h => hli (by rw [h])
        simpa only [if_pos (Eq.refl i),if_neg hsb,ite_true] using hwidth i
      · by_cases hrj : r=j
        · subst r
          have hsc : s ≠ c := fun h => hlj (by rw [h])
          simpa only [if_neg hri,if_pos (Eq.refl j),if_neg hsc,ite_true] using hwidth j
        · simpa only [if_neg hri,if_neg hrj] using hd r s

theorem keySideCreasePoint_mem_solid {n : ℕ} (k : KeyData (n+1))
    (hc : k.centre (Fin.last n)=0) (hr : k.radius (Fin.last n)=0)
    (hh : 0 < keyPyramidHeight k) (hd : ∀ r s, 0 < keySideDistance k r s)
    (i j : Fin n) (hij : i ≠ j) (b c : Bool) :
    keySideCreasePoint k i j b c ∈ keySolid k := by
  obtain ⟨hi,hj,ho⟩ := keySideCreasePoint_full_slacks k hh hd i j hij b c
  apply (mem_keySolid_iff_nonneg_slacks k hc hr hh _).mpr
  intro l
  by_cases hli : l=.inr (i,b)
  · subst l; exact hi.ge
  · by_cases hlj : l=.inr (j,c)
    · subst l; exact hj.ge
    · exact (ho l hli hlj).le

#print axioms keySideCreasePoint_full_slacks
#print axioms keySideCreasePoint_mem_solid
end SparseMonotiles
