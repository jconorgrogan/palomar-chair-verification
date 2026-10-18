module

public import SpectreGeometry.ReverseLocalStarGeometryValues
public import SpectreGeometry.ReverseLocalStarGeometryTable0
public import SpectreGeometry.ReverseLocalStarGeometryTable1
public import SpectreGeometry.ReverseLocalStarGeometryTable2
public import SpectreGeometry.ReverseLocalStarGeometryTable3
public import SpectreGeometry.ReverseLocalStarGeometryTable4
public import SpectreGeometry.ReverseLocalStarGeometryTable5
public import SpectreGeometry.ReverseLocalStarGeometryTable6
public import SpectreGeometry.ReverseLocalStarGeometryTable7
public import SpectreGeometry.ReverseLocalStarGeometryTable8

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def sideGeometryRows : List (List (List Nat)) := [sideGeometryRows0,sideGeometryRows1,sideGeometryRows2,sideGeometryRows3,sideGeometryRows4,sideGeometryRows5,sideGeometryRows6,sideGeometryRows7,sideGeometryRows8]
def tripleGeometryRows : List (List (List Nat)) := [tripleGeometryRows0,tripleGeometryRows1,tripleGeometryRows2,tripleGeometryRows3,tripleGeometryRows4,tripleGeometryRows5,tripleGeometryRows6,tripleGeometryRows7,tripleGeometryRows8]
def sideGeometryCode (a b : State) (d : Fin 6) (j : Nat) : Nat :=
  let rows := sideGeometryRows.getD a.1.val []
  ((rows.find? (fun row => row.take 4 == [b.1.val,b.2.val,d.val,j])).getD []).getD 4 217
def tripleGeometryCode (a b c : State) (d : Fin 6) : Nat :=
  let rows := tripleGeometryRows.getD a.1.val []
  ((rows.find? (fun row => row.take 5 == [b.1.val,b.2.val,c.1.val,c.2.val,d.val])).getD []).getD 5 49

def sideGeometryKey (a b : State) (d : Fin 6) (j : Nat) : List Nat :=
  let ids := stateBoundaryIds a d
  let ids' := stateBoundaryIds b (opposite d)
  [if a.1.val=0 then 0 else 1,ids.getD j 0,if b.1.val=0 then 0 else 1,b.2.val,
   ids'.getD (ids'.length-1-j) 0]
def tripleGeometryKey (a b c : State) (d : Fin 6) : List Nat :=
  [if a.1.val=0 then 0 else 1,(stateBoundaryIds a d).getLastD 0,
   if b.1.val=0 then 0 else 1,b.2.val,(stateBoundaryIds b (opposite d)).headD 0,
   if c.1.val=0 then 0 else 1,c.2.val,
   (stateBoundaryIds c (rotateTurn 4 (rotateTurn 1 d))).headD 0]
def SideGeometryBinding (k : Fin 9) (d : Fin 6) : Prop :=
  ∀ (bk : Fin 9) (br : Fin 6) (j : Fin 12), sideMatch (k,0) (bk,br) d →
    0<j.val → j.val+1<(stateBoundaryIds (k,0) d).length →
      let code := sideGeometryCode (k,0) (bk,br) d j.val
      code<217 ∧ (sideGeometryValues.getD code []).take 5 = sideGeometryKey (k,0) (bk,br) d j.val

def TripleGeometryBinding (k : Fin 9) (d : Fin 6) : Prop :=
  ∀ (bk : Fin 9) (br : Fin 6) (ck : Fin 9) (cr : Fin 6),
    sideMatch (k,0) (bk,br) d → sideMatch (k,0) (ck,cr) (rotateTurn 1 d) →
    sideMatch (bk,br) (ck,cr) (rotateTurn 2 d) →
      let code := tripleGeometryCode (k,0) (bk,br) (ck,cr) d
      code<49 ∧ (tripleGeometryValues.getD code []).take 8 = tripleGeometryKey (k,0) (bk,br) (ck,cr) d
end SpectreGeometry.ReverseLocalStarOccurrences

