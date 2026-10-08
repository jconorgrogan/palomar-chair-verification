module
public import SparseMonotiles.ForwardContactCertificatesFields
public import SparseMonotiles.T7ConditionalExistence
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SparseForwardBlock
open Contact Existence.Catalog7World
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Bit i is the original geometric role at coordinate i. Role 127 is reserved
for the central child, rather than the excluded all-true outer role. -/
def maskBits (n : ℕ) : Bits 7 := fun i => n.testBit i.val

theorem maskBits_code : ∀ a : Bits 7, maskBits (bitCode a) = a := by decide +kernel

theorem proper_code_lt : ∀ a : Bits 7, Proper a → bitCode a < 127 := by decide +kernel

theorem code_maskBits : ∀ n : Fin 128, bitCode (maskBits n.val) = n.val := by decide +kernel

def sourceChild (n : Fin 128) : Pose 7 :=
  if n.val = 127 then centralPose 7 else
    outerPose (maskBits n.val) (Catalog7.childPerm (maskBits n.val))

theorem sourceChild_central : sourceChild 127 = centralPose 7 := rfl

theorem sourceChild_outer (n : Fin 128) (h : n.val ≠ 127) :
    sourceChild n = outerPose (maskBits n.val) (Catalog7.childPerm (maskBits n.val)) := by
  simp only [sourceChild, if_neg h]

theorem sourceChild_mem : ∀ n : Fin 128, sourceChild n ∈ children7 := by
  intro n
  by_cases hn : n.val = 127
  · simpa only [sourceChild, if_pos hn] using children7_covers.1
  · rw [sourceChild_outer n hn]
    apply children7_covers.2
    have hproper : ∀ n : Fin 128, n.val ≠ 127 → Proper (maskBits n.val) := by decide +kernel
    exact hproper n hn

theorem children7_covered {b : Pose 7} (hb : b ∈ children7) :
    ∃ n : Fin 128, sourceChild n = b := by
  rw [children7, Finset.mem_insert] at hb
  rcases hb with hb | hb
  · exact ⟨127, sourceChild_central.trans hb.symm⟩
  · rcases Finset.mem_image.mp hb with ⟨a, ha, rfl⟩
    have ha' := (Finset.mem_filter.mp ha).2
    let n : Fin 128 := ⟨bitCode a, by have := proper_code_lt a ha'; omega⟩
    have hn : n.val ≠ 127 := by have := proper_code_lt a ha'; dsimp [n]; omega
    refine ⟨n, ?_⟩
    rw [sourceChild_outer n hn]
    change outerPose (maskBits (bitCode a)) (Catalog7.childPerm (maskBits (bitCode a))) = _
    rw [maskBits_code]

theorem children7_exact_table : children7 = Finset.univ.image sourceChild := by
  ext b
  constructor
  · intro hb
    obtain ⟨n, hn⟩ := children7_covered hb
    exact Finset.mem_image.mpr ⟨n, Finset.mem_univ _, hn⟩
  · intro hb
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hb
    exact sourceChild_mem n

/-- The central role is separate from every outer role. -/
theorem sourceChild_central_iff : ∀ n : Fin 128,
    sourceChild n = centralPose 7 ↔ n = 127 := by decide +kernel


def parentPose : Pose 7 := Catalog7.supplied.get ⟨2, by decide⟩
def rootChild : Pose 7 := sourceChild 11

theorem rootChild_literal : rootChild =
    ⟨Catalog7.perm13, ![true,true,false,true,false,false,false], ![4,4,0,4,0,0,0]⟩ := by decide +kernel
theorem parentPose_literal : parentPose =
    ⟨Catalog7.perm13, ![true,true,false,true,false,false,false], ![3,3,-1,3,-1,-1,-1]⟩ := by decide +kernel

theorem parentPose_mem : parentPose ∈ M7 := List.get_mem _ _
theorem rootChild_mem : rootChild ∈ children7 := sourceChild_mem 11

def exactFields (p : Pose 7) : CoarseFields :=
  ⟨fun i => if h : i < 7 then (p.perm ⟨i,h⟩).val else 0,
   fun i => if h : i < 7 then p.negative ⟨i,h⟩ else false,
   fun i => if h : i < 7 then p.shift ⟨i,h⟩ else 0⟩

theorem exactFields_represents (p : Pose 7) : (exactFields p).Represents p := by
  intro i
  simp [exactFields, i.isLt]

def registry (n : Fin 408) : Pose 7 := Catalog7.supplied.get ⟨n.val, by simpa only [Catalog7.supplied_count] using n.isLt⟩
def registryFields (n : Fin 408) : CoarseFields := exactFields (registry n)
theorem registryFields_represents (n : Fin 408) : (registryFields n).Represents (registry n) := exactFields_represents _
theorem registry_mem (n : Fin 408) : registry n ∈ M7 := List.get_mem _ _

def refinedSource (n : Fin 128) : Pose 7 := compose (dilatePose parentPose) (sourceChild n)
def sourceFields (n : Fin 128) : CoarseFields := (exactFields parentPose).dilate.compose (exactFields (sourceChild n))
theorem sourceFields_represents (n : Fin 128) : (sourceFields n).Represents (refinedSource n) :=
  CoarseFields.compose_represents (CoarseFields.dilate_represents (exactFields_represents _)) (exactFields_represents _)

#print axioms children7_exact_table
#print axioms exactFields_represents
end SparseMonotiles.CarrierHierarchy.T7SparseForwardBlock
