module
public import MeanObstruction.Obstruction
public import RegisteredPrime.CompletedRules
@[expose] public section
namespace RegisteredPrime
open Uniform

/-- The mean obstruction in the finite-coordinate mask interface of the
registered prime family. It is independent of μ and g, but applies to every
admissible Parameters value. It does not assert any E/CL identification. -/
theorem registered_mean_obstruction (P : Parameters) (j : Fin P.p) (L : Mask P.p)
    (hstable : ∀ A : Mask P.p, NonemptyMask A → Proper A → A j = true →
      NonemptyMask (fun i => xor (A i) (L i)) →
      Proper (fun i => xor (A i) (L i)) →
      zA P.p (extendMask A) = zA P.p (extendMask (fun i => xor (A i) (L i)))) :
    L = (fun _ => false) ∨ L = (fun _ => true) := by
  have hnat : MeanObstruction.MeanStableAt P.p j.val (extendMask L) := by
    intro A hA hAj hD
    let B : Mask P.p := fun i => A i.val
    have hB : NonemptyMask B := by
      obtain ⟨i, hi, hAi⟩ := hA.1
      exact ⟨⟨i, hi⟩, hAi⟩
    have hBp : Proper B := by
      obtain ⟨i, hi, hAi⟩ := hA.2
      exact ⟨⟨i, hi⟩, hAi⟩
    have hBj : B j = true := hAj
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
  rcases MeanObstruction.mean_obstruction P.prime P.odd j.isLt (extendMask L) hnat with
    hempty | hfull
  · left
    funext i
    simpa only [extendMask_at] using hempty i.val i.isLt
  · right
    funext i
    simpa only [extendMask_at] using hfull i.val i.isLt

end RegisteredPrime
