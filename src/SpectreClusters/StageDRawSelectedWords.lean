module

public import SpectreClusters.StageDRawProbeSemantics
public import SpectreClusters.StageDRawNormalizeRoot

@[expose] public section

namespace SpectreClusters.StageD.Raw

def selectedIndexWord (n : Nat) (chosen : Nat → Nat) : List Nat :=
  (List.range n).map chosen

theorem selectedIndexWord_overChoices (n : Nat) (chosen : Nat → Nat)
    (choices : List (List Nat)) (hlen : choices.length = n)
    (h : ∀ i, i < n → chosen i ∈ choices.getD i []) :
    FiniteCoverWords.OverChoices (selectedIndexWord n chosen) choices := by
  apply overChoices_of_indexed chosen (List.range n) choices (by simp [hlen])
  intro i hi
  have hin : i < n := by simpa using hi
  have hic : i < choices.length := hlen ▸ hin
  simpa [List.getD_eq_getElem?_getD,hic] using h i hin

theorem selectedIndexWord_pairwise (kind : ClusterKind) (n : Nat) (chosen : Nat → Nat)
    (h : ∀ i, i < n → ∀ j, j < n → idCompatible kind (chosen i) (chosen j) = true) :
    (selectedIndexWord n chosen).Pairwise (fun a b => idCompatible kind a b = true) := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  simp only [selectedIndexWord,List.length_map,List.length_range] at hi hj
  simpa only [selectedIndexWord,List.getElem_map,List.getElem_range] using h i hi j hj

theorem selectedIndexWord_owned (f : Cell → ClusterPlacement) (kind : ClusterKind)
    (n : Nat) (chosen : Nat → Nat)
    (h : ∀ i, i < n → ClusterRootOwned f ((candidateList kind).getD (chosen i) fallback)) :
    ∀ a ∈ selectedIndexWord n chosen, ClusterRootOwned f ((candidateList kind).getD a fallback) := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact h i (List.mem_range.mp hi)

theorem rawPatch_owned_of_selected_word (f : Cell → ClusterPlacement) (kind : ClusterKind)
    (hr : ClusterRootOwned f (canonical kind)) (w : List Nat)
    (howned : ∀ a ∈ w, ClusterRootOwned f ((candidateList kind).getD a fallback)) (i : Nat)
    (hrow : ∀ a ∈ (rawNeighborIDs kind).getD i [], a ∈ w) :
    ClusterPatchOwned f (rawPatch kind i) := by
  intro p hp
  rcases List.mem_cons.mp hp with hp | hp
  · simpa only [hp] using hr
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hp
    exact howned a (hrow a ha)

/-- Closing interface for the finite probes; all geometric and finite-list
obligations are explicit and must be discharged by their checked packets. -/
theorem normalizedRawCaptures_of_selected_words
    (hselected : ∀ f, ValidClusterGridField f → ∀ kind, LegalClusterKind kind →
      ClusterRootOwned f (canonical kind) → ∃ w : List Nat,
        FiniteCoverWords.OverChoices w (probeChoices kind) ∧
        w.Pairwise (fun a b => idCompatible kind a b = true) ∧
        ∀ a ∈ w, ClusterRootOwned f ((candidateList kind).getD a fallback))
    (hcovered : ∀ kind, LegalClusterKind kind → ∀ w,
      w ∈ FiniteCoverWords.enumerate (idCompatible kind) (probeChoices kind) →
      ∃ i, i < (rawNeighborIDs kind).length ∧
        ∀ a ∈ (rawNeighborIDs kind).getD i [], a ∈ w) : NormalizedRawCaptures := by
  intro f hf kind hk hr
  obtain ⟨w,hchoices,hpair,howned⟩ := hselected f hf kind hk hr
  have hw := (FiniteCoverWords.mem_enumerate_iff _ _ _).mpr ⟨hchoices,hpair⟩
  obtain ⟨i,hi,hrow⟩ := hcovered kind hk w hw
  exact ⟨i,hi,rawPatch_owned_of_selected_word f kind hr w howned i hrow⟩
end SpectreClusters.StageD.Raw
