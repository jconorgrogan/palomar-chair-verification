module

public import SparseMonotiles.ContactChecker

@[expose] public section

/-! Exact literal T3 calibration dictionary and candidate certificates.
Generated data, not a proof of completeness of the candidate-generating algorithm.
Every accepted row is recomputed; every rejected row supplies a checked witness.
Input SHA-256 pins (binding checked by the external generation receipt):
sparse_contacts_independent_20261006/tile3_certificate_dictionary.json: 3114535e2e3f873aaf1ceddde724134222ccd701b9f5e12f5861edf167287cc6
sparse_contacts_independent_20261006/tile3_candidate_certificates.jsonl.gz: fe42f9b152698b8e93c63c1b0f3784104785d8a9ce2b622b0ff30b9e15e40172
sparse_contacts_independent_20261006/tile3_accepted_poses.json: 6b464fc89ef58567b65a894747f71cce7b421b2e2f18f8fef8211920022fcf05
high_dimension_facet_replay_20261005/p3_F.json: 3dd75721ccab38cb64640ef46126fd423bf0243bd57804087d59f3eef2586395
incoming_tiles_20261006/extracted/S54_monotile_bundle/deliverables/tile3_final_spec.json: 589e549bea72c18b58032b499fab91cd670c9060cb45ac7cd9611322867e94ba
-/
namespace SparseMonotiles.Contact.Calibration3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def perm0 : Equiv.Perm (Fin 3) :=
  ⟨![0, 1, 2], ![0, 1, 2], by decide, by decide⟩
def perm1 : Equiv.Perm (Fin 3) :=
  ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def perm2 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩
def perm3 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def perm4 : Equiv.Perm (Fin 3) :=
  ⟨![2, 0, 1], ![1, 2, 0], by decide, by decide⟩
def perm5 : Equiv.Perm (Fin 3) :=
  ⟨![2, 1, 0], ![2, 1, 0], by decide, by decide⟩
def key0 : VertexKey 3 :=
  ⟨{![-8, 777, 472], ![0, 732, 456], ![0, 732, 504], ![0, 804, 456], ![0, 804, 504]}, true⟩
def key1 : VertexKey 3 :=
  ⟨{![732, 0, 456], ![732, 0, 504], ![777, 8, 472], ![804, 0, 456], ![804, 0, 504]}, false⟩
def key2 : VertexKey 3 :=
  ⟨{![456, 348, 0], ![456, 420, 0], ![472, 375, -8], ![504, 348, 0], ![504, 420, 0]}, true⟩
def key3 : VertexKey 3 :=
  ⟨{![348, 456, 0], ![348, 504, 0], ![375, 472, 8], ![420, 456, 0], ![420, 504, 0]}, false⟩
def key4 : VertexKey 3 :=
  ⟨{![0, 732, 1800], ![0, 732, 1848], ![0, 804, 1800], ![0, 804, 1848], ![8, 777, 1832]}, false⟩
def key5 : VertexKey 3 :=
  ⟨{![732, 0, 1800], ![732, 0, 1848], ![777, -8, 1832], ![804, 0, 1800], ![804, 0, 1848]}, true⟩
def key6 : VertexKey 3 :=
  ⟨{![456, 348, 2304], ![456, 420, 2304], ![472, 375, 2296], ![504, 348, 2304], ![504, 420, 2304]}, false⟩
def key7 : VertexKey 3 :=
  ⟨{![348, 456, 2304], ![348, 504, 2304], ![375, 472, 2312], ![420, 456, 2304], ![420, 504, 2304]}, true⟩
def key8 : VertexKey 3 :=
  ⟨{![-8, 1832, 777], ![0, 1800, 732], ![0, 1800, 804], ![0, 1848, 732], ![0, 1848, 804]}, true⟩
def key9 : VertexKey 3 :=
  ⟨{![456, 2304, 348], ![456, 2304, 420], ![472, 2312, 375], ![504, 2304, 348], ![504, 2304, 420]}, true⟩
def key10 : VertexKey 3 :=
  ⟨{![348, 2304, 456], ![348, 2304, 504], ![375, 2296, 472], ![420, 2304, 456], ![420, 2304, 504]}, false⟩
def key11 : VertexKey 3 :=
  ⟨{![732, 1800, 0], ![732, 1848, 0], ![777, 1832, 8], ![804, 1800, 0], ![804, 1848, 0]}, false⟩
def key12 : VertexKey 3 :=
  ⟨{![-8, 1832, 1929], ![0, 1800, 1884], ![0, 1800, 1956], ![0, 1848, 1884], ![0, 1848, 1956]}, true⟩
def key13 : VertexKey 3 :=
  ⟨{![0, 1884, 1800], ![0, 1884, 1848], ![0, 1956, 1800], ![0, 1956, 1848], ![8, 1929, 1832]}, false⟩
def key14 : VertexKey 3 :=
  ⟨{![1144, 1929, 1624], ![1152, 1884, 1608], ![1152, 1884, 1656], ![1152, 1956, 1608], ![1152, 1956, 1656]}, false⟩
def key15 : VertexKey 3 :=
  ⟨{![456, 2304, 1500], ![456, 2304, 1572], ![472, 2312, 1527], ![504, 2304, 1500], ![504, 2304, 1572]}, true⟩
def key16 : VertexKey 3 :=
  ⟨{![456, 1500, 2304], ![456, 1572, 2304], ![472, 1527, 2296], ![504, 1500, 2304], ![504, 1572, 2304]}, false⟩
def key17 : VertexKey 3 :=
  ⟨{![2296, 472, 375], ![2304, 456, 348], ![2304, 456, 420], ![2304, 504, 348], ![2304, 504, 420]}, false⟩
def key18 : VertexKey 3 :=
  ⟨{![2304, 348, 456], ![2304, 348, 504], ![2304, 420, 456], ![2304, 420, 504], ![2312, 375, 472]}, true⟩
def key19 : VertexKey 3 :=
  ⟨{![1800, 0, 732], ![1800, 0, 804], ![1832, 8, 777], ![1848, 0, 732], ![1848, 0, 804]}, false⟩
def key20 : VertexKey 3 :=
  ⟨{![1800, 732, 0], ![1800, 804, 0], ![1832, 777, -8], ![1848, 732, 0], ![1848, 804, 0]}, true⟩
def key21 : VertexKey 3 :=
  ⟨{![2296, 472, 1527], ![2304, 456, 1500], ![2304, 456, 1572], ![2304, 504, 1500], ![2304, 504, 1572]}, false⟩
def key22 : VertexKey 3 :=
  ⟨{![1800, 0, 1884], ![1800, 0, 1956], ![1832, 8, 1929], ![1848, 0, 1884], ![1848, 0, 1956]}, false⟩
def key23 : VertexKey 3 :=
  ⟨{![1884, 0, 1800], ![1884, 0, 1848], ![1929, -8, 1832], ![1956, 0, 1800], ![1956, 0, 1848]}, true⟩
def key24 : VertexKey 3 :=
  ⟨{![1884, 1152, 1608], ![1884, 1152, 1656], ![1929, 1160, 1624], ![1956, 1152, 1608], ![1956, 1152, 1656]}, true⟩
def key25 : VertexKey 3 :=
  ⟨{![1500, 456, 2304], ![1500, 504, 2304], ![1527, 472, 2312], ![1572, 456, 2304], ![1572, 504, 2304]}, true⟩
def key26 : VertexKey 3 :=
  ⟨{![2304, 1500, 456], ![2304, 1500, 504], ![2304, 1572, 456], ![2304, 1572, 504], ![2312, 1527, 472]}, true⟩
def key27 : VertexKey 3 :=
  ⟨{![1500, 2304, 456], ![1500, 2304, 504], ![1527, 2296, 472], ![1572, 2304, 456], ![1572, 2304, 504]}, false⟩
def key28 : VertexKey 3 :=
  ⟨{![1800, 1884, 0], ![1800, 1956, 0], ![1832, 1929, -8], ![1848, 1884, 0], ![1848, 1956, 0]}, true⟩
def key29 : VertexKey 3 :=
  ⟨{![1884, 1800, 0], ![1884, 1848, 0], ![1929, 1832, 8], ![1956, 1800, 0], ![1956, 1848, 0]}, false⟩
def key30 : VertexKey 3 :=
  ⟨{![1608, 1500, 1152], ![1608, 1572, 1152], ![1624, 1527, 1144], ![1656, 1500, 1152], ![1656, 1572, 1152]}, false⟩
def key31 : VertexKey 3 :=
  ⟨{![1500, 1608, 1152], ![1500, 1656, 1152], ![1527, 1624, 1160], ![1572, 1608, 1152], ![1572, 1656, 1152]}, true⟩
def facet0 : Facet 3 := ⟨![0, 0, 0], 0, false⟩
def facet1 : Facet 3 := ⟨![0, 0, 0], 1, false⟩
def facet2 : Facet 3 := ⟨![0, 0, 0], 2, false⟩
def facet3 : Facet 3 := ⟨![0, 0, 1], 0, false⟩
def facet4 : Facet 3 := ⟨![0, 0, 1], 1, false⟩
def facet5 : Facet 3 := ⟨![0, 0, 1], 2, true⟩
def facet6 : Facet 3 := ⟨![0, 1, 0], 0, false⟩
def facet7 : Facet 3 := ⟨![0, 1, 0], 1, true⟩
def facet8 : Facet 3 := ⟨![0, 1, 0], 2, false⟩
def facet9 : Facet 3 := ⟨![0, 1, 1], 0, false⟩
def facet10 : Facet 3 := ⟨![0, 1, 1], 0, true⟩
def facet11 : Facet 3 := ⟨![0, 1, 1], 1, true⟩
def facet12 : Facet 3 := ⟨![0, 1, 1], 2, true⟩
def facet13 : Facet 3 := ⟨![1, 0, 0], 0, true⟩
def facet14 : Facet 3 := ⟨![1, 0, 0], 1, false⟩
def facet15 : Facet 3 := ⟨![1, 0, 0], 2, false⟩
def facet16 : Facet 3 := ⟨![1, 0, 1], 0, true⟩
def facet17 : Facet 3 := ⟨![1, 0, 1], 1, false⟩
def facet18 : Facet 3 := ⟨![1, 0, 1], 1, true⟩
def facet19 : Facet 3 := ⟨![1, 0, 1], 2, true⟩
def facet20 : Facet 3 := ⟨![1, 1, 0], 0, true⟩
def facet21 : Facet 3 := ⟨![1, 1, 0], 1, true⟩
def facet22 : Facet 3 := ⟨![1, 1, 0], 2, false⟩
def facet23 : Facet 3 := ⟨![1, 1, 0], 2, true⟩
def geometry : Geometry 3 where
  denominator := 1152
  cells := {![0, 0, 0], ![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![1, 0, 0], ![1, 0, 1], ![1, 1, 0]}
  facets := {facet0, facet1, facet2, facet3, facet4, facet5, facet6, facet7, facet8, facet9, facet10, facet11, facet12, facet13, facet14, facet15, facet16, facet17, facet18, facet19, facet20, facet21, facet22, facet23}
  profile := fun f =>
    if f = facet0 then {key0} else
    if f = facet1 then {key1} else
    if f = facet2 then {key2, key3} else
    if f = facet3 then {key4} else
    if f = facet4 then {key5} else
    if f = facet5 then {key6, key7} else
    if f = facet6 then {key8} else
    if f = facet7 then {key9, key10} else
    if f = facet8 then {key11} else
    if f = facet9 then {key12, key13} else
    if f = facet10 then {key14} else
    if f = facet11 then {key15} else
    if f = facet12 then {key16} else
    if f = facet13 then {key17, key18} else
    if f = facet14 then {key19} else
    if f = facet15 then {key20} else
    if f = facet16 then {key21} else
    if f = facet17 then {key22, key23} else
    if f = facet18 then {key24} else
    if f = facet19 then {key25} else
    if f = facet20 then {key26} else
    if f = facet21 then {key27} else
    if f = facet22 then {key28, key29} else
    if f = facet23 then {key30, key31} else
    ∅

def chunk0 : List (Row 3) := [
  ⟨⟨perm0, ![true, false, false], ![0, 0, 0]⟩, some (.unmatchedRoot facet0 facet0 key0)⟩,
  ⟨⟨perm2, ![true, false, false], ![0, 0, 0]⟩, none⟩,
  ⟨⟨perm5, ![true, true, false], ![0, 1, 0]⟩, some (.unmatchedRoot facet0 facet2 key0)⟩,
  ⟨⟨perm4, ![true, true, false], ![0, 1, 0]⟩, some (.unmatchedSource facet0 facet2 key2)⟩,
  ⟨⟨perm0, ![true, false, true], ![0, 0, 2]⟩, some (.unmatchedRoot facet6 facet9 key8)⟩,
  ⟨⟨perm2, ![true, false, true], ![0, 0, 2]⟩, some (.unmatchedRoot facet0 facet4 key0)⟩,
  ⟨⟨perm5, ![false, true, false], ![-2, 1, 0]⟩, some (.unmatchedSource facet0 facet5 key7)⟩,
  ⟨⟨perm4, ![false, true, false], ![-2, 1, 0]⟩, some (.unmatchedRoot facet0 facet5 key0)⟩
]

end SparseMonotiles.Contact.Calibration3
