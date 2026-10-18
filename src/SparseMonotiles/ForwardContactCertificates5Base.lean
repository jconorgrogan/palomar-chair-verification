module

public import SparseMonotiles.ForwardContactCertificatesFields
public import SparseMonotiles.CoarseContactCertificates5PackedBase
public import SparseMonotiles.CoarseContactCertificates5SymmetryData

@[expose] public section

namespace SparseMonotiles.CarrierHierarchy.ForwardContactCertificates5
open Contact CoarseContactCertificates5 CoarseContactCertificates5Symmetry

def childFields (i : Fin 32) : CoarseFields := .packed (packedChild i)
def registryFields (i : Fin 284) : CoarseFields := .packed (packedRegistry i)
theorem child_fields (i : Fin 32) : (childFields i).Represents (child i) := child_packed i
theorem registry_fields (i : Fin 284) : (registryFields i).Represents (registry i) := registry_packed i

def SiblingImplication (a : Fin 280) : Prop :=
  child (representativePair a).1 ≠ child (representativePair a).2 →
  CellContact (child (representativePair a).1) (child (representativePair a).2) →
  normalize (child (representativePair a).1) (child (representativePair a).2) ∈ L

def CrossImplication (a : Fin 280) (k : Fin 284) : Prop :=
  CellContact (child (representativePair a).1)
    (compose (dilatePose (registry k)) (child (representativePair a).2)) →
  normalize (child (representativePair a).1)
    (compose (dilatePose (registry k)) (child (representativePair a).2)) ∈ L

def siblingCheck (a : Fin 280) (w : ForwardFieldsWitness 5 (Fin 284)) : Bool :=
  if (representativePair a).1 = (representativePair a).2 then true else
    w.check registryFields (childFields (representativePair a).1) (childFields (representativePair a).2)

def crossCheck (a : Fin 280) (k : Fin 284) (w : ForwardFieldsWitness 5 (Fin 284)) : Bool :=
  w.check registryFields (childFields (representativePair a).1)
    ((registryFields k).dilate.compose (childFields (representativePair a).2))

theorem siblingCheck_sound (a : Fin 280) (w : ForwardFieldsWitness 5 (Fin 284))
    (h : siblingCheck a w = true) : SiblingImplication a := by
  intro hne hc
  have hi : (representativePair a).1 ≠ (representativePair a).2 := by
    intro he
    exact hne (congrArg child he)
  have hh : w.check registryFields (childFields (representativePair a).1)
      (childFields (representativePair a).2) = true := by
    simpa only [siblingCheck, if_neg hi] using h
  exact ForwardPairWitness.sound registry L registry_mem
    (ForwardFieldsWitness.check_sound registry registryFields registry_fields
      (child_fields _) (child_fields _) hh) hc

theorem crossCheck_sound (a : Fin 280) (k : Fin 284) (w : ForwardFieldsWitness 5 (Fin 284))
    (h : crossCheck a k w = true) : CrossImplication a k := by
  intro hc
  exact ForwardPairWitness.sound registry L registry_mem
    (ForwardFieldsWitness.check_sound registry registryFields registry_fields
      (child_fields _) (CoarseFields.compose_represents
        (CoarseFields.dilate_represents (registry_fields k)) (child_fields _)) h) hc

#print axioms siblingCheck_sound
#print axioms crossCheck_sound
end SparseMonotiles.CarrierHierarchy.ForwardContactCertificates5
