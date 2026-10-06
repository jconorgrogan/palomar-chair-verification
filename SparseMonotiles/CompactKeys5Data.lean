module

public import SparseMonotiles.CompactBodyBridge
public import SparseMonotiles.Tile5Data

@[expose] public section
namespace SparseMonotiles.CompactBinding.Keys5
set_option maxRecDepth 100000

/-- Every compact placement interpreted as the exact frozen-model key type. -/
def compactKeys : List (KeyData 5) :=
  (PalomarMonotiles.placements5.map
    (PalomarMonotiles.placedKey PalomarMonotiles.widths5 PalomarMonotiles.offsets5)).map toKeyData

theorem compactKeys_length : compactKeys.length = 256 := by
  simp only [compactKeys, List.length_map]
  rfl

def compactAt (i : Fin 256) : KeyData 5 := compactKeys.get
  ⟨i.val, by simpa only [compactKeys_length] using i.isLt⟩
def literalAt (i : Fin 256) : KeyData 5 := keys5.get
  ⟨i.val, by simpa only [keys5_length] using i.isLt⟩
def bindingIndex (b : Fin 16) (i : Fin 16) : Fin 256 := ⟨16 * b.val + i.val, by omega⟩
end SparseMonotiles.CompactBinding.Keys5
