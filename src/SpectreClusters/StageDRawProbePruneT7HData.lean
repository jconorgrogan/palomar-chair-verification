module

public import SpectreClusters.StageDRawIndexedPruningModel
public import SpectreClusters.StageDRawProbeData

@[expose] public section

namespace SpectreClusters.StageD.Raw.IndexedPruning
def pruneChoicesT7H0 : List (List Nat) := [[1,23,44,65,88,112,131,153,174,195,219,241],[28,47,71,112,114,135,158,177,201,246],[15,34,36,38,54,57,79,83,98,101,104,121,125,142,145,165,168,184,187,190,209,213,229,232,235,253,257],[16,20,58,62,80,84,102,126,127,146,150,169,188,214,215,233,258,259],[9,30,49,51,73,95,116,118,139,160,179,181,203,205,226,248,250],[35,164]]
def pruneChoicesT7H1 : List (List Nat) := [[23,44,88,112,153,174,241],[28,47,112,114,135,177,246],[15,34,36,38,54,57,79,83,98,101,104,121,125,142,145,165,168,184,187,190,209,213,229,232,235,253,257],[126,258],[49,179],[35,164]]
def pruneChoicesT7H2 : List (List Nat) := [[23,88,153,241],[28,47,114,135,177,246],[98,229],[126,258],[49,179],[35,164]]
def pruneChoicesT7H3 : List (List Nat) := [[23,88,153,241],[47,135,177],[98,229],[126,258],[49,179],[35,164]]
def pruneChoicesT7H4 : List (List Nat) := [[23,153,241],[47,135,177],[98,229],[126,258],[49,179],[35,164]]
theorem pruneChoicesT7H_initial : pruneChoicesT7H0 = probeChoices .t7h := rfl
end SpectreClusters.StageD.Raw.IndexedPruning
