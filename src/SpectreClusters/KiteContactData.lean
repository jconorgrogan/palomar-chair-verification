module

public import SpectreClusters.KiteGrid

@[expose] public section


namespace SpectreClusters

def cellContactB (a b : Cell) : Bool :=
  (cellVertices a).any (fun v => (cellVertices b).contains v)

theorem cellContactB_iff (a b : Cell) : cellContactB a b = true ↔ CellContact a b := by
  simp [cellContactB,CellContact,List.any_eq_true,List.contains_iff_mem]


/-- Exact ten-cell vertex-contact stencil, including the cell itself. -/
def localContacts (k : Turn) : List Cell :=
  match k.val with
  | 0 => [⟨(0,0),0⟩,⟨(0,0),1⟩,⟨(0,0),2⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩,
          ⟨(0,1),3⟩,⟨(0,1),4⟩,⟨(1,0),2⟩,⟨(1,0),3⟩]
  | 1 => [⟨(-1,1),4⟩,⟨(-1,1),5⟩,⟨(0,0),0⟩,⟨(0,0),1⟩,⟨(0,0),2⟩,⟨(0,0),3⟩,
          ⟨(0,0),4⟩,⟨(0,0),5⟩,⟨(0,1),3⟩,⟨(0,1),4⟩]
  | 2 => [⟨(-1,0),0⟩,⟨(-1,0),5⟩,⟨(-1,1),4⟩,⟨(-1,1),5⟩,⟨(0,0),0⟩,⟨(0,0),1⟩,
          ⟨(0,0),2⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩]
  | 3 => [⟨(-1,0),0⟩,⟨(-1,0),5⟩,⟨(0,-1),0⟩,⟨(0,-1),1⟩,⟨(0,0),0⟩,⟨(0,0),1⟩,
          ⟨(0,0),2⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩]
  | 4 => [⟨(0,-1),0⟩,⟨(0,-1),1⟩,⟨(0,0),0⟩,⟨(0,0),1⟩,⟨(0,0),2⟩,⟨(0,0),3⟩,
          ⟨(0,0),4⟩,⟨(0,0),5⟩,⟨(1,-1),1⟩,⟨(1,-1),2⟩]
  | _ => [⟨(0,0),0⟩,⟨(0,0),1⟩,⟨(0,0),2⟩,⟨(0,0),3⟩,⟨(0,0),4⟩,⟨(0,0),5⟩,
          ⟨(1,-1),1⟩,⟨(1,-1),2⟩,⟨(1,0),2⟩,⟨(1,0),3⟩]

end SpectreClusters
