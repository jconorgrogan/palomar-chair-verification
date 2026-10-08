module
public import SparseMonotiles.T7SevenRepresentatives
@[expose] public section
namespace SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
open Contact ContactInverseReuse
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def block00 : Finset (Fin 408) := {1,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18}

def block01 : Finset (Fin 408) := {19,20,21,22,23,24,26,27,29,31,32,33,34,35,36,37}

def block02 : Finset (Fin 408) := {38,39,40,41,42,43,44,45,46,47,48,50,51,53,55,56}

def block03 : Finset (Fin 408) := {57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72}

def block04 : Finset (Fin 408) := {73,74,75,76,77,79,80,82,83,85,86,87,88,89,90,91}

def block05 : Finset (Fin 408) := {92,97,98,99,103,106,107,108,109,110,111,114,115,117,118,119}

def block06 : Finset (Fin 408) := {123,126,127,128,131,134,137,139,140,141,142,144,146,147,148,152}

def block07 : Finset (Fin 408) := {154,155,156,157,164,168,169,170,172,175,176,177,178,179,180,183}

def block08 : Finset (Fin 408) := {185,186,188,190,192,194,196,198,200,202,204,206,208,210,212,215}

def block09 : Finset (Fin 408) := {217,218,219,220,221,223,226,228,230,232,234,236,240,241,245,255}

def block10 : Finset (Fin 408) := {258,266,267,269,270,273,274,276,277,281,283,285,286,290,294,296}

def block11 : Finset (Fin 408) := {297,302,303,307,310,312,315,321,322,325,326,327,329,340,341,344}

def block12 : Finset (Fin 408) := {350,365,368,369,376,383,385,401,403}

/-- Exact finite equality, so no remaining index is omitted. -/
theorem blocks_cover_remainingAfterSeven :
    block00 ∪ (block01 ∪ (block02 ∪ (block03 ∪ (block04 ∪ (block05 ∪ (block06 ∪ (block07 ∪ (block08 ∪ (block09 ∪ (block10 ∪ (block11 ∪ (block12)))))))))))) = remainingAfterSeven := by
  decide +kernel

#print axioms blocks_cover_remainingAfterSeven
end SparseMonotiles.CarrierHierarchy.Existence.ProfileBridge7.Acceptance201
