module
public import SparseMonotiles.T7GlobalSparseAssembly
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.T7SparseMemberThreeBlocks
open Contact T7SparseForwardBlock T7GlobalSparseAssembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def zeroRows : SparseRows := []
def oneRows : SparseRows := [(115,388)]
def eightRows : SparseRows :=
  [(63,155),(95,126),(111,97),(119,68),(123,41),(125,17),(126,222),(127,238)]

theorem zero_checked : sparseMemberChecks 7 registryFields (childFields 0)
    (crossFields 0) zeroRows = true := by decide +kernel

theorem one_checked : sparseMemberChecks 7 registryFields (childFields 63)
    (crossFields 0) oneRows = true := by decide +kernel

theorem eight_checked : sparseMemberChecks 7 registryFields (childFields 11)
    (crossFields 2) eightRows = true := by decide +kernel

theorem crossFields_represents (k : Fin 408) (n : Fin 128) :
    (crossFields k n).Represents (compose (dilatePose (registry k)) (sourceChild n)) :=
  CoarseFields.compose_represents (CoarseFields.dilate_represents (registryFields_represents k))
    (exactFields_represents _)

theorem sparse_row_exact {k : Fin 408} {a : Fin 128} {rows : SparseRows}
    (h : sparseMemberChecks 7 registryFields (childFields a) (crossFields k) rows = true)
    {b : Fin 128} {j : Fin 408} (hrow : (b,j) ∈ rows) :
    normalize (sourceChild a) (compose (dilatePose (registry k)) (sourceChild b)) = registry j :=
  sparseMemberChecks_sound registry registryFields registryFields_represents
    (exactFields_represents _) (crossFields_represents k) h hrow

theorem sparse_row_member {k : Fin 408} {a : Fin 128} {rows : SparseRows}
    (h : sparseMemberChecks 7 registryFields (childFields a) (crossFields k) rows = true)
    {b : Fin 128} (hb : b ∈ rows.map Prod.fst) :
    normalize (sourceChild a) (compose (dilatePose (registry k)) (sourceChild b)) ∈ M7 := by
  obtain ⟨⟨i,j⟩, hrow, he⟩ := List.mem_map.mp hb
  have heq := sparse_row_exact h hrow
  simp only [Prod.fst] at he
  subst i
  rw [heq]
  exact registry_mem j

#print axioms zero_checked
#print axioms one_checked
#print axioms eight_checked
#print axioms sparse_row_member
end SparseMonotiles.CarrierHierarchy.T7SparseMemberThreeBlocks
