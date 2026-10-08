module
public import MeanObstruction.RegisteredBinding
@[expose] public section
namespace RegisteredPrime
open Uniform
namespace MeanObstruction

/-- The mean obstruction is valid on either coordinate face. Complementing
the test masks reduces the false face to the true face without endpoint gaps. -/
theorem mean_obstruction_side {p j : Nat} (hp : IsPrime p) (hp2 : p ≠ 2)
    (hj : j < p) (L : Nat → Bool) (side : Bool)
    (hstable : ∀ A : Nat → Bool, NonemptyProperOn p A → A j = side →
      NonemptyProperOn p (symmDiff A L) → zA p A = zA p (symmDiff A L)) :
    (∀ i, i < p → L i = false) ∨ (∀ i, i < p → L i = true) := by
  cases side with
  | true => exact mean_obstruction hp hp2 hj L hstable
  | false =>
    apply mean_obstruction hp hp2 hj L
    intro A hA hAj hD
    have he : symmDiff (complement A) L = complement (symmDiff A L) := by
      funext i
      rcases Bool.eq_false_or_eq_true (A i) with hAi | hAi <;>
        rcases Bool.eq_false_or_eq_true (L i) with hLi | hLi <;>
        simp [symmDiff, complement, hAi, hLi]
    have hCD : NonemptyProperOn p (symmDiff (complement A) L) := by
      rw [he]
      exact complement_proper hD
    have h := hstable (complement A) (complement_proper hA)
      (by simp [complement, hAj]) hCD
    rw [he, mean_complement hp hp2 A hA,
      mean_complement hp hp2 (symmDiff A L) hD] at h
    exact h

end MeanObstruction

/-- Finite-mask mean obstruction on either chosen side of a coordinate face. -/
theorem registered_mean_obstruction_side (P : Parameters) (j : Fin P.p) (L : Mask P.p)
    (side : Bool)
    (hstable : ∀ A : Mask P.p, NonemptyMask A → Proper A → A j = side →
      NonemptyMask (fun i => xor (A i) (L i)) →
      Proper (fun i => xor (A i) (L i)) →
      zA P.p (extendMask A) = zA P.p (extendMask (fun i => xor (A i) (L i)))) :
    L = (fun _ => false) ∨ L = (fun _ => true) := by
  have hnat : ∀ A : Nat → Bool, NonemptyProperOn P.p A → A j.val = side →
      NonemptyProperOn P.p (MeanObstruction.symmDiff A (extendMask L)) →
      zA P.p A = zA P.p (MeanObstruction.symmDiff A (extendMask L)) := by
    intro A hA hAj hD
    let B : Mask P.p := fun i => A i.val
    have hB : NonemptyMask B := by
      obtain ⟨i, hi, hAi⟩ := hA.1
      exact ⟨⟨i, hi⟩, hAi⟩
    have hBp : Proper B := by
      obtain ⟨i, hi, hAi⟩ := hA.2
      exact ⟨⟨i, hi⟩, hAi⟩
    have hBj : B j = side := hAj
    have hDB : NonemptyMask (fun i => xor (B i) (L i)) := by
      obtain ⟨i, hi, hDi⟩ := hD.1
      refine ⟨⟨i, hi⟩, ?_⟩
      simpa [MeanObstruction.symmDiff, extendMask, hi, B] using hDi
    have hDBp : Proper (fun i => xor (B i) (L i)) := by
      obtain ⟨i, hi, hDi⟩ := hD.2
      refine ⟨⟨i, hi⟩, ?_⟩
      simpa [MeanObstruction.symmDiff, extendMask, hi, B] using hDi
    have h := hstable B hB hBp hBj hDB hDBp
    have eA : zA P.p (extendMask B) = zA P.p A :=
      MeanObstruction.mean_congr (fun i hi => by simp [extendMask, hi, B])
    have eD : zA P.p (extendMask (fun i => xor (B i) (L i))) =
        zA P.p (MeanObstruction.symmDiff A (extendMask L)) :=
      MeanObstruction.mean_congr (fun i hi => by
        simp [extendMask, hi, B, MeanObstruction.symmDiff])
    exact eA.symm.trans (h.trans eD)
  rcases MeanObstruction.mean_obstruction_side P.prime P.odd j.isLt (extendMask L) side hnat with
    hempty | hfull
  · left
    funext i
    simpa only [extendMask_at] using hempty i.val i.isLt
  · right
    funext i
    simpa only [extendMask_at] using hfull i.val i.isLt

end RegisteredPrime
