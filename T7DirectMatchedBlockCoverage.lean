module
public import T7DirectMatchedBase
public import T7ReducedIndexData
@[expose] public section
namespace SparseMonotiles.T7DirectMatchedBlockCoverage
open Contact CarrierHierarchy T7ReducedIndexData
set_option maxRecDepth 100000

def PairLaw (a b : Fin 512) : Prop := ∀ p : Pose 7,
  (RootZeroPilot7.sourceKey (dentIndex b)).Asymmetric →
  RootZeroPilot7.sourceKey (bumpIndex a) =
    p.boxKey IndexedData7.geometry.denominator (RootZeroPilot7.sourceKey (dentIndex b)) →
  IndexedData7.geometry.LegalContact p → p ∈ M7

def sourceBlock128 (c : Fin 4) (i : Fin 128) : Fin 512 :=
  ⟨128 * c.val + i.val, by omega⟩

def sourceBlock256 (c : Fin 2) (i : Fin 256) : Fin 512 :=
  ⟨256 * c.val + i.val, by omega⟩

def BlockLaw128 (a : Fin 512) (c : Fin 4) : Prop :=
  ∀ i : Fin 128, PairLaw a (sourceBlock128 c i)

def BlockLaw256 (a : Fin 512) (c : Fin 2) : Prop :=
  ∀ i : Fin 256, PairLaw a (sourceBlock256 c i)

theorem all_pairs_of_2048_blocks (blocks : ∀ (a : Fin 512) (c : Fin 4), BlockLaw128 a c) :
    ∀ a b : Fin 512, PairLaw a b := by
  intro a b
  have h := blocks a ⟨b.val / 128, by omega⟩ ⟨b.val % 128, by omega⟩
  have he : sourceBlock128 ⟨b.val / 128, by omega⟩ ⟨b.val % 128, by omega⟩ = b := by
    apply Fin.ext; simp only [sourceBlock128]; omega
  simpa only [he] using h

theorem all_pairs_of_1024_blocks (blocks : ∀ (a : Fin 512) (c : Fin 2), BlockLaw256 a c) :
    ∀ a b : Fin 512, PairLaw a b := by
  intro a b
  have h := blocks a ⟨b.val / 256, by omega⟩ ⟨b.val % 256, by omega⟩
  have he : sourceBlock256 ⟨b.val / 256, by omega⟩ ⟨b.val % 256, by omega⟩ = b := by
    apply Fin.ext; simp only [sourceBlock256]; omega
  simpa only [he] using h

#print axioms all_pairs_of_2048_blocks
#print axioms all_pairs_of_1024_blocks
end SparseMonotiles.T7DirectMatchedBlockCoverage
