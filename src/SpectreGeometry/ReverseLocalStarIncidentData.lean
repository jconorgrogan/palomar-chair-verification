module

public import SpectreGeometry.ReverseLocalStarStructuralChecks

@[expose] public section

namespace SpectreGeometry.ReverseLocalStarOccurrences
open SpectreClusters SpectreClusters.ReverseExistence SpectreFinite SpectreFinite.HexSearch
open ReverseClusterTriangulation
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def interiorRows : List (List (List Nat)) := [[[44,5],[45,8],[46,17],[47,20],[48,29],[49,35],[50,40],[51,46],[52,52],[53,56],[54,65],[55,34],[56,69],[57,73],[58,82],[59,88],[60,91],[61,100],[62,106],[63,112],[64,118],[65,33],[66,68],[67,121],[68,127],[69,136],[70,142],[71,145],[72,154],[73,32],[74,37],[75,43],[76,49],[77,157],[78,166],[79,31],[80,66],[81,172],[82,174],[83,185],[84,188],[85,194],[86,199],[87,193],[88,198],[89,192],[90,203],[91,196],[92,197],[93,202],[94,196],[95,201],[96,206],[97,211],[98,217],[99,223],[100,204],[101,214],[102,220],[103,226],[104,207],[105,232],[106,239],[107,242],[108,248],[109,257],[110,260],[111,266],[112,272],[113,276],[114,283],[115,289],[116,295],[117,301],[118,307],[119,313],[120,281],[121,319],[122,325],[123,331],[124,337],[125,346],[126,279]],[[46,5],[47,8],[48,17],[49,20],[50,29],[51,35],[52,40],[53,46],[54,52],[55,56],[56,65],[57,34],[58,69],[59,73],[60,82],[61,88],[62,91],[63,100],[64,106],[65,112],[66,118],[67,33],[68,38],[69,44],[70,50],[71,349],[72,358],[73,32],[74,67],[75,361],[76,366],[77,372],[78,378],[79,384],[80,390],[81,399],[82,405],[83,411],[84,31],[85,417],[86,174],[87,185],[88,188],[89,194],[90,199],[91,193],[92,198],[93,192],[94,203],[95,197],[96,202],[97,196],[98,201],[99,206],[100,211],[101,217],[102,223],[103,204],[104,215],[105,221],[106,227],[107,208],[108,207],[109,232],[110,239],[111,242],[112,248],[113,257],[114,260],[115,266],[116,272],[117,276],[118,283],[119,289],[120,295],[121,301],[122,307],[123,313],[124,421],[125,429],[126,435],[127,280],[128,442],[129,444],[130,450],[131,276],[132,330]]]

def kindMark (big : Bool) : Fin 9 := if big then 1 else 0
def calculatedIncidentRow (big : Bool) (v : Nat) : List Nat :=
  let k := kindMark big
  (List.range (meshTriangles k).length).filter (fun i =>
    decide (v ∈ triangleIndices ((meshTriangles k).getD i (0,0,0))))
def calculatedIncidentRows (big : Bool) : List (List Nat) :=
  (List.range (targetVertices (kindMark big)).length).map (calculatedIncidentRow big)

def interiorCode (big : Bool) (v : Nat) (r : Fin 6) : Nat :=
  let rows := interiorRows.getD (if big then 1 else 0) []
  let code := ((rows.find? (fun row => row.headD 133 == v)).getD []).getD 1 744
  6*(code/6)+(code%6+6-r.val)%6

def IsBoundaryIndex (k : Fin 9) (v : Nat) : Prop :=
  ∃ d : Fin 6, v ∈ boundaryIndices k d
instance (k : Fin 9) (v : Nat) : Decidable (IsBoundaryIndex k v) :=
  inferInstanceAs (Decidable (∃ d : Fin 6, v ∈ boundaryIndices k d))

def InteriorCertificate (big : Bool) : Prop := ∀ (v : Fin 133) (r : Fin 6),
  v.val < (targetVertices (kindMark big)).length → ¬IsBoundaryIndex (kindMark big) v.val →
    occurrenceStructuralB (localStar (kindMark big,r) v.val) (interiorCode big v.val r) = true
end SpectreGeometry.ReverseLocalStarOccurrences
