module

public import SparseMonotiles.AtlasReverseChunks.Tile7Keys4
public import SparseMonotiles.AtlasReverseChunks.Tile7Keys5
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact

open Contact.IndexedData7

theorem atlasFacet7_128_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 128) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key147} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_147_mem

theorem atlasFacet7_129_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 129) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key148} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_148_mem

theorem atlasFacet7_130_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 130) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key149} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_149_mem

theorem atlasFacet7_131_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 131) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key150} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_150_mem

theorem atlasFacet7_132_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 132) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key151} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_151_mem

theorem atlasFacet7_133_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 133) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key152} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_152_mem

theorem atlasFacet7_134_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 134) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key153} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_153_mem

theorem atlasFacet7_135_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 135) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key154, key155} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_154_mem
  · exact indexedKey7_155_mem

theorem atlasFacet7_136_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 136) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key156} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_156_mem

theorem atlasFacet7_137_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 137) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key157} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_157_mem

theorem atlasFacet7_138_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 138) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key158} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_158_mem

theorem atlasFacet7_139_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 139) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key159} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_159_mem

theorem atlasFacet7_140_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 140) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key160} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_160_mem

theorem atlasFacet7_141_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 141) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key161} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_161_mem

theorem atlasFacet7_142_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 142) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key162} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_162_mem

theorem atlasFacet7_143_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 143) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key163, key164} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_163_mem
  · exact indexedKey7_164_mem

theorem atlasFacet7_144_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 144) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key165} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_165_mem

theorem atlasFacet7_145_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 145) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key166} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_166_mem

theorem atlasFacet7_146_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 146) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key167} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_167_mem

theorem atlasFacet7_147_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 147) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key168} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_168_mem

theorem atlasFacet7_148_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 148) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key169} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_169_mem

theorem atlasFacet7_149_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 149) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key170} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_170_mem

theorem atlasFacet7_150_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 150) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key171} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_171_mem

theorem atlasFacet7_151_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 151) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key172, key173} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact indexedKey7_172_mem
  · exact indexedKey7_173_mem

theorem atlasFacet7_152_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 152) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key174} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_174_mem

theorem atlasFacet7_153_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 153) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key175} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_175_mem

theorem atlasFacet7_154_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 154) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key176} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_176_mem

theorem atlasFacet7_155_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 155) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key177} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_177_mem

theorem atlasFacet7_156_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 156) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key178} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_178_mem

theorem atlasFacet7_157_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 157) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key179} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_179_mem

theorem atlasFacet7_158_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 158) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key180} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_180_mem

theorem atlasFacet7_159_literal (b : BoxKey 7) (hb : b ∈ geometry.profile 159) :
    b.toKeyData 188160 ∈ keys7 := by
  change b ∈ ({key181} : Finset (BoxKey 7)) at hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  subst b
  exact indexedKey7_181_mem

theorem atlasReverse7Chunk4 (i : Fin 32) :
    ∀ b ∈ geometry.profile ⟨128 + i.val, by omega⟩, b.toKeyData 188160 ∈ keys7 := by
  fin_cases i
  · exact atlasFacet7_128_literal
  · exact atlasFacet7_129_literal
  · exact atlasFacet7_130_literal
  · exact atlasFacet7_131_literal
  · exact atlasFacet7_132_literal
  · exact atlasFacet7_133_literal
  · exact atlasFacet7_134_literal
  · exact atlasFacet7_135_literal
  · exact atlasFacet7_136_literal
  · exact atlasFacet7_137_literal
  · exact atlasFacet7_138_literal
  · exact atlasFacet7_139_literal
  · exact atlasFacet7_140_literal
  · exact atlasFacet7_141_literal
  · exact atlasFacet7_142_literal
  · exact atlasFacet7_143_literal
  · exact atlasFacet7_144_literal
  · exact atlasFacet7_145_literal
  · exact atlasFacet7_146_literal
  · exact atlasFacet7_147_literal
  · exact atlasFacet7_148_literal
  · exact atlasFacet7_149_literal
  · exact atlasFacet7_150_literal
  · exact atlasFacet7_151_literal
  · exact atlasFacet7_152_literal
  · exact atlasFacet7_153_literal
  · exact atlasFacet7_154_literal
  · exact atlasFacet7_155_literal
  · exact atlasFacet7_156_literal
  · exact atlasFacet7_157_literal
  · exact atlasFacet7_158_literal
  · exact atlasFacet7_159_literal

#print axioms atlasReverse7Chunk4
end SparseMonotiles.Canonical
