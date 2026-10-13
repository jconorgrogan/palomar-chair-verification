module

public import PrimeFacetClosure.FiniteGeneratedCompiler
public import PrimeFacetClosure.NativeGeneratedGauge

@[expose] public section

/-!
# Concrete original-E finite compiler holonomy

All native gauges, labels, local edge classifications, generator properness,
and edge-frame realizations are now proved for the actual original generated
language. Candidate conclusions below assume only literal native site transport
and opposite coefficients from the constructed compiler, never generated
membership or a closure certificate for the candidate.
-/
namespace PhysicalRegistration.NativeChair.GeneratedCompiler
noncomputable section
open RegisteredPrime
open RegisteredPrime.PrimeFacetClosure
open RegisteredPrime.PrimeFacetClosure.StarHolonomy
open NativeWalkTransport

variable {m : ℕ}

/-- The concrete star gauge on the actual finite original-E compiler graph.
There is no remaining geometric-classification argument to supply. -/
def starGauge (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3) :
    StarGauge (graph hp hmod) (reflectionFrame (minusParameters (m+1) hp hmod)) :=
  nativeStarGauge (generators hp hmod) (generators_proper hp hmod)
    (reflectionFrame (minusParameters (m+1) hp hmod))
    (negIndex_involutive (minusParameters (m+1) hp hmod))
    (fun u => facetStarLabel hp hmod u.1) (fun u => isOuter u.1)
    (fun u => facetStarGauge hp hmod u.1)
    (fun {u v} h => generated_native_classification hp hmod
      (edgePose (generators hp hmod) (generators_proper hp hmod) h)
      (edgePose_generated hp hmod (generators_proper hp hmod) h) u v
      (edgePose_transport hp hmod (generators_proper hp hmod) h))

theorem starGauge_realizes (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {u v : Site m} (h : (graph hp hmod).Adj u v) :
    RegisteredFrameRealizes ((starGauge hp hmod).edgeFrame h)
      (edgePlacement (generators hp hmod) (generators_proper hp hmod) h) :=
  poseRealizes_frame (edgePose_realizes (generators hp hmod) (generators_proper hp hmod) h)

/-- Literal opposite coefficients force the same-type candidate's complete
matrix into the reflection bridge normal form in the concrete star gauges. -/
theorem candidate_same_type_gauged
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} {u v : Site m} (ht : SiteTransport (poseIsometry q) u v)
    (ha : (coefficients hp hmod).value v = -(coefficients hp hmod).value u)
    (htype : isOuter u.1 = isOuter v.1) :
    facetStarLabel hp hmod v.1 =
        (reflectionFrame (minusParameters (m+1) hp hmod)).perm (facetStarLabel hp hmod u.1) ∧
      gauged (facetStarGauge hp hmod u.1) q.frame (facetStarGauge hp hmod v.1) =
        bridge (reflectionFrame (minusParameters (m+1) hp hmod)) (facetStarLabel hp hmod u.1) := by
  let := nativeSiteOrder (nativeDimension_ge_two hmod)
  obtain ⟨w, hw⟩ := opposite_coefficients_odd_walk
    (generators hp hmod) (generators_proper hp hmod) ha
  have hf := odd_walk_candidate_frame (generators hp hmod) (generators_proper hp hmod)
    (starGauge hp hmod) (starGauge_realizes hp hmod) w hw (poseIsometry_realizes q) ht
  have hh := (starGauge hp hmod).odd_same_type w htype hw
  refine ⟨hh.1, ?_⟩
  exact (congrArg (fun R => gauged (facetStarGauge hp hmod u.1) R
    (facetStarGauge hp hmod v.1)) hf).trans hh.2

/-- Unlike endpoint types give the exact hole gauge normal form for the
candidate, including equality of the two concrete star labels. -/
theorem candidate_different_type_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} {u v : Site m} (ht : SiteTransport (poseIsometry q) u v)
    (ha : (coefficients hp hmod).value v = -(coefficients hp hmod).value u)
    (htype : isOuter u.1 ≠ isOuter v.1) :
    facetStarLabel hp hmod v.1 = facetStarLabel hp hmod u.1 ∧
      q.frame = (facetStarGauge hp hmod u.1).comp (facetStarGauge hp hmod v.1).inv := by
  let := nativeSiteOrder (nativeDimension_ge_two hmod)
  exact opposite_coefficients_candidate_hole_frame
    (generators hp hmod) (generators_proper hp hmod)
    (starGauge hp hmod) (starGauge_realizes hp hmod) (poseIsometry_realizes q) ht ha htype


/-- Same-type ungauged counterpart, retaining the complete original candidate
matrix in ambient coordinates. -/
theorem candidate_same_type_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} {u v : Site m} (ht : SiteTransport (poseIsometry q) u v)
    (ha : (coefficients hp hmod).value v = -(coefficients hp hmod).value u)
    (htype : isOuter u.1 = isOuter v.1) :
    q.frame = ((facetStarGauge hp hmod u.1).comp
      (bridge (reflectionFrame (minusParameters (m+1) hp hmod)) (facetStarLabel hp hmod u.1))).comp
      (facetStarGauge hp hmod v.1).inv :=
  ungauge _ _ _ _ (candidate_same_type_gauged hp hmod ht ha htype).2

/-- Unlike endpoint types have identity gauged candidate transport. -/
theorem candidate_different_type_gauged
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} {u v : Site m} (ht : SiteTransport (poseIsometry q) u v)
    (ha : (coefficients hp hmod).value v = -(coefficients hp hmod).value u)
    (htype : isOuter u.1 ≠ isOuter v.1) :
    facetStarLabel hp hmod v.1 = facetStarLabel hp hmod u.1 ∧
      gauged (facetStarGauge hp hmod u.1) q.frame (facetStarGauge hp hmod v.1) = oneFrame (m+1) := by
  have hf := candidate_different_type_frame hp hmod ht ha htype
  refine ⟨hf.1, (congrArg (fun R => gauged (facetStarGauge hp hmod u.1) R
    (facetStarGauge hp hmod v.1)) hf.2).trans ?_⟩
  simp only [gauged, frame_comp_assoc, frame_inv_comp, frame_comp_one]

/-- Unified local candidate law consumed by exact facet-to-atlas closure.
Everything except the actual paired-site equation is constructed and proved. -/
theorem candidate_gauged
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    {q : Pose (m+1)} {u v : Site m} (ht : SiteTransport (poseIsometry q) u v)
    (ha : (coefficients hp hmod).value v = -(coefficients hp hmod).value u) :
    gauged (facetStarGauge hp hmod u.1) q.frame (facetStarGauge hp hmod v.1) =
      if isOuter u.1 = isOuter v.1 then
        bridge (reflectionFrame (minusParameters (m+1) hp hmod)) (facetStarLabel hp hmod u.1)
      else oneFrame (m+1) := by
  by_cases hh : isOuter u.1 = isOuter v.1
  · exact (candidate_same_type_gauged hp hmod ht ha hh).2.trans (if_pos hh).symm
  · exact (candidate_different_type_gauged hp hmod ht ha hh).2.trans (if_neg hh).symm

/-- The outer/inner candidate has exactly its original incoming hole frame. -/
theorem candidate_outer_inner_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : Pose (m+1)) (A : Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inl (A,j), U) (.inr k, V))
    (ha : (coefficients hp hmod).value (.inr k, V) =
      -(coefficients hp hmod).value (.inl (A,j), U)) :
    q.frame = (arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame := by
  have hf := (candidate_different_type_frame hp hmod ht ha (by change true ≠ false; decide)).2
  change q.frame = ((arithmeticChild (minusParameters (m+1) hp hmod)
    (.outer A.val (nativeCell_proper A))).frame).comp (oneFrame (m+1)) at hf
  exact hf.trans (frame_comp_one _)

private theorem frame_inv_inv (F : RegisteredFrame (m+1)) : F.inv.inv = F := by
  apply frame_ext
  · rfl
  · funext i
    simp [RegisteredFrame.inv, F.left_inverse]

/-- The inner/outer candidate has exactly the inverse incoming hole frame. -/
theorem candidate_inner_outer_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : Pose (m+1)) (A : Cell m) (k j : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inr k, U) (.inl (A,j), V))
    (ha : (coefficients hp hmod).value (.inl (A,j), V) =
      -(coefficients hp hmod).value (.inr k, U)) :
    q.inv.frame = (arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame := by
  have hf := (candidate_different_type_frame hp hmod ht ha (by change false ≠ true; decide)).2
  change q.frame = (oneFrame (m+1)).comp
    (arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame.inv at hf
  have hf' := hf.trans (frame_one_comp _)
  exact (congrArg RegisteredFrame.inv hf').trans (frame_inv_inv _)

/-- The inner/inner candidate's entire matrix is the unique odd bridge. -/
theorem candidate_inner_inner_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : Pose (m+1)) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inr j, U) (.inr k, V))
    (ha : (coefficients hp hmod).value (.inr k, V) =
      -(coefficients hp hmod).value (.inr j, U)) :
    q.frame = bridge (reflectionFrame (minusParameters (m+1) hp hmod)) j := by
  have hf := (candidate_same_type_gauged hp hmod ht ha rfl).2
  change ((oneFrame (m+1)).comp q.frame).comp (oneFrame (m+1)) = _ at hf
  exact ((frame_comp_one _).trans (frame_one_comp q.frame)).symm.trans hf

/-- The exact outer/outer equation consumed by the uniform mean obstruction.
It holds for each actual paired full-orbit site and retains every frame entry. -/
theorem candidate_outer_outer_frame
    (hp : Uniform.IsPrime (m+1)) (hmod : (m+1) % 4 = 3)
    (q : Pose (m+1)) (A B : Cell m) (j k : Fin (m+1)) (U V : Frame m)
    (ht : SiteTransport (poseIsometry q) (.inl (A,j), U) (.inl (B,k), V))
    (ha : (coefficients hp hmod).value (.inl (B,k), V) =
      -(coefficients hp hmod).value (.inl (A,j), U)) :
    (((arithmeticChild (minusParameters (m+1) hp hmod)
      (.outer A.val (nativeCell_proper A))).frame.inv.comp q.frame).comp
      (arithmeticChild (minusParameters (m+1) hp hmod)
        (.outer B.val (nativeCell_proper B))).frame) =
      bridge (reflectionFrame (minusParameters (m+1) hp hmod))
        ((arithmeticChild (minusParameters (m+1) hp hmod)
          (.outer A.val (nativeCell_proper A))).frame.perm j) :=
  (candidate_same_type_gauged hp hmod ht ha rfl).2

#print axioms starGauge
#print axioms candidate_gauged
#print axioms candidate_same_type_frame
#print axioms candidate_different_type_gauged
#print axioms candidate_same_type_gauged
#print axioms candidate_different_type_frame
#print axioms candidate_outer_inner_frame
#print axioms candidate_inner_outer_frame
#print axioms candidate_inner_inner_frame
#print axioms candidate_outer_outer_frame
end
end PhysicalRegistration.NativeChair.GeneratedCompiler
