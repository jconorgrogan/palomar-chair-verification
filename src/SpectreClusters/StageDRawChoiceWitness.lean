module

public import SpectreClusters.StageDRawProbeData

@[expose] public section

namespace SpectreClusters.StageD.Raw

def witnessChoicesCheck (choices : List Nat) (ws : List CandidateWitness) : Bool :=
  ws.all fun w => match w with
    | .listed i => choices.contains i
    | .overlap _ => true

/-- Reuse alignment witnesses to name an allowed owner ID directly. -/
theorem alignedChecks_choice (root : List Cell) (candidates : List ClusterPlacement)
    (c : Cell) (ws : List CandidateWitness) (choices : List Nat)
    (hlen : ws.length = (alignedAt c).length)
    (h : alignedChecks root candidates c ws = true)
    (hw : witnessChoicesCheck choices ws = true)
    (p : ClusterPlacement) (hp : p ∈ alignedAt c)
    (hd : DisjointCells root (clusterPlacementCells p)) :
    ∃ i, i ∈ choices ∧ i < candidates.length ∧ candidates.getD i fallback = p := by
  let j := (alignedAt c).idxOf p
  have hj : j < (alignedAt c).length := List.idxOf_lt_length_of_mem hp
  have he : (alignedAt c).getD j fallback = p := by
    simp [j,List.getD_eq_getElem?_getD,hj]
  have hc := List.all_eq_true.mp h j (List.mem_range.mpr hj)
  rw [he] at hc
  have hwm : ws.getD j (.listed 0) ∈ ws := by
    have hjw : j < ws.length := hlen ▸ hj
    simpa [List.getD_eq_getElem?_getD,hjw] using (List.getElem_mem hjw)
  have hchoice := List.all_eq_true.mp hw (ws.getD j (.listed 0)) hwm
  cases hcase : ws.getD j (.listed 0) with
  | listed i =>
    rw [hcase] at hc hchoice
    simp only [witnessCheck,Bool.and_eq_true,decide_eq_true_eq,poseEqB_iff] at hc
    exact ⟨i,by simpa only [List.contains_iff_mem] using hchoice,hc.1,hc.2.symm⟩
  | overlap w =>
    rw [hcase] at hc
    simp only [witnessCheck,Bool.and_eq_true,List.any_eq_true,cellEqB_iff] at hc
    obtain ⟨⟨a,ha,hea⟩,b,hb,heb⟩ := hc
    exact False.elim (hd w (by simpa only [hea] using ha) (by simpa only [heb] using hb))
end SpectreClusters.StageD.Raw
