module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section

namespace SpectreFinite.HexSearch.RadiusFiveParentBinding
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
theorem parentChunk_mem120 : ParentOwnership.parentRows120 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 120) (by decide)
theorem parentRow_mem1920 : ParentOwnership.parentRow1920 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 0) (by decide)
theorem parentRow_mem1921 : ParentOwnership.parentRow1921 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 1) (by decide)
theorem parentRow_mem1922 : ParentOwnership.parentRow1922 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 2) (by decide)
theorem parentRow_mem1923 : ParentOwnership.parentRow1923 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 3) (by decide)
theorem parentRow_mem1924 : ParentOwnership.parentRow1924 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 4) (by decide)
theorem parentRow_mem1925 : ParentOwnership.parentRow1925 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 5) (by decide)
theorem parentRow_mem1926 : ParentOwnership.parentRow1926 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 6) (by decide)
theorem parentRow_mem1927 : ParentOwnership.parentRow1927 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 7) (by decide)
theorem parentRow_mem1928 : ParentOwnership.parentRow1928 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 8) (by decide)
theorem parentRow_mem1929 : ParentOwnership.parentRow1929 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 9) (by decide)
theorem parentRow_mem1930 : ParentOwnership.parentRow1930 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 10) (by decide)
theorem parentRow_mem1931 : ParentOwnership.parentRow1931 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 11) (by decide)
theorem parentRow_mem1932 : ParentOwnership.parentRow1932 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 12) (by decide)
theorem parentRow_mem1933 : ParentOwnership.parentRow1933 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 13) (by decide)
theorem parentRow_mem1934 : ParentOwnership.parentRow1934 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 14) (by decide)
theorem parentRow_mem1935 : ParentOwnership.parentRow1935 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows120, parentChunk_mem120, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows120) (n := 15) (by decide)
theorem parentChunk_mem121 : ParentOwnership.parentRows121 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 121) (by decide)
theorem parentRow_mem1936 : ParentOwnership.parentRow1936 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 0) (by decide)
theorem parentRow_mem1937 : ParentOwnership.parentRow1937 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 1) (by decide)
theorem parentRow_mem1938 : ParentOwnership.parentRow1938 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 2) (by decide)
theorem parentRow_mem1939 : ParentOwnership.parentRow1939 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 3) (by decide)
theorem parentRow_mem1940 : ParentOwnership.parentRow1940 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 4) (by decide)
theorem parentRow_mem1941 : ParentOwnership.parentRow1941 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 5) (by decide)
theorem parentRow_mem1942 : ParentOwnership.parentRow1942 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 6) (by decide)
theorem parentRow_mem1943 : ParentOwnership.parentRow1943 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 7) (by decide)
theorem parentRow_mem1944 : ParentOwnership.parentRow1944 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 8) (by decide)
theorem parentRow_mem1945 : ParentOwnership.parentRow1945 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 9) (by decide)
theorem parentRow_mem1946 : ParentOwnership.parentRow1946 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 10) (by decide)
theorem parentRow_mem1947 : ParentOwnership.parentRow1947 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 11) (by decide)
theorem parentRow_mem1948 : ParentOwnership.parentRow1948 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 12) (by decide)
theorem parentRow_mem1949 : ParentOwnership.parentRow1949 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 13) (by decide)
theorem parentRow_mem1950 : ParentOwnership.parentRow1950 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 14) (by decide)
theorem parentRow_mem1951 : ParentOwnership.parentRow1951 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows121, parentChunk_mem121, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows121) (n := 15) (by decide)
theorem parentChunk_mem122 : ParentOwnership.parentRows122 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 122) (by decide)
theorem parentRow_mem1952 : ParentOwnership.parentRow1952 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 0) (by decide)
theorem parentRow_mem1953 : ParentOwnership.parentRow1953 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 1) (by decide)
theorem parentRow_mem1954 : ParentOwnership.parentRow1954 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 2) (by decide)
theorem parentRow_mem1955 : ParentOwnership.parentRow1955 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 3) (by decide)
theorem parentRow_mem1956 : ParentOwnership.parentRow1956 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 4) (by decide)
theorem parentRow_mem1957 : ParentOwnership.parentRow1957 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 5) (by decide)
theorem parentRow_mem1958 : ParentOwnership.parentRow1958 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 6) (by decide)
theorem parentRow_mem1959 : ParentOwnership.parentRow1959 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 7) (by decide)
theorem parentRow_mem1960 : ParentOwnership.parentRow1960 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 8) (by decide)
theorem parentRow_mem1961 : ParentOwnership.parentRow1961 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 9) (by decide)
theorem parentRow_mem1962 : ParentOwnership.parentRow1962 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 10) (by decide)
theorem parentRow_mem1963 : ParentOwnership.parentRow1963 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 11) (by decide)
theorem parentRow_mem1964 : ParentOwnership.parentRow1964 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 12) (by decide)
theorem parentRow_mem1965 : ParentOwnership.parentRow1965 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 13) (by decide)
theorem parentRow_mem1966 : ParentOwnership.parentRow1966 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 14) (by decide)
theorem parentRow_mem1967 : ParentOwnership.parentRow1967 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows122, parentChunk_mem122, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows122) (n := 15) (by decide)
theorem parentChunk_mem123 : ParentOwnership.parentRows123 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 123) (by decide)
theorem parentRow_mem1968 : ParentOwnership.parentRow1968 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 0) (by decide)
theorem parentRow_mem1969 : ParentOwnership.parentRow1969 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 1) (by decide)
theorem parentRow_mem1970 : ParentOwnership.parentRow1970 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 2) (by decide)
theorem parentRow_mem1971 : ParentOwnership.parentRow1971 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 3) (by decide)
theorem parentRow_mem1972 : ParentOwnership.parentRow1972 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 4) (by decide)
theorem parentRow_mem1973 : ParentOwnership.parentRow1973 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 5) (by decide)
theorem parentRow_mem1974 : ParentOwnership.parentRow1974 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 6) (by decide)
theorem parentRow_mem1975 : ParentOwnership.parentRow1975 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 7) (by decide)
theorem parentRow_mem1976 : ParentOwnership.parentRow1976 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 8) (by decide)
theorem parentRow_mem1977 : ParentOwnership.parentRow1977 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 9) (by decide)
theorem parentRow_mem1978 : ParentOwnership.parentRow1978 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 10) (by decide)
theorem parentRow_mem1979 : ParentOwnership.parentRow1979 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 11) (by decide)
theorem parentRow_mem1980 : ParentOwnership.parentRow1980 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 12) (by decide)
theorem parentRow_mem1981 : ParentOwnership.parentRow1981 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 13) (by decide)
theorem parentRow_mem1982 : ParentOwnership.parentRow1982 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 14) (by decide)
theorem parentRow_mem1983 : ParentOwnership.parentRow1983 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows123, parentChunk_mem123, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows123) (n := 15) (by decide)
theorem parentChunk_mem124 : ParentOwnership.parentRows124 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 124) (by decide)
theorem parentRow_mem1984 : ParentOwnership.parentRow1984 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 0) (by decide)
theorem parentRow_mem1985 : ParentOwnership.parentRow1985 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 1) (by decide)
theorem parentRow_mem1986 : ParentOwnership.parentRow1986 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 2) (by decide)
theorem parentRow_mem1987 : ParentOwnership.parentRow1987 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 3) (by decide)
theorem parentRow_mem1988 : ParentOwnership.parentRow1988 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 4) (by decide)
theorem parentRow_mem1989 : ParentOwnership.parentRow1989 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 5) (by decide)
theorem parentRow_mem1990 : ParentOwnership.parentRow1990 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 6) (by decide)
theorem parentRow_mem1991 : ParentOwnership.parentRow1991 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 7) (by decide)
theorem parentRow_mem1992 : ParentOwnership.parentRow1992 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 8) (by decide)
theorem parentRow_mem1993 : ParentOwnership.parentRow1993 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 9) (by decide)
theorem parentRow_mem1994 : ParentOwnership.parentRow1994 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 10) (by decide)
theorem parentRow_mem1995 : ParentOwnership.parentRow1995 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 11) (by decide)
theorem parentRow_mem1996 : ParentOwnership.parentRow1996 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 12) (by decide)
theorem parentRow_mem1997 : ParentOwnership.parentRow1997 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 13) (by decide)
theorem parentRow_mem1998 : ParentOwnership.parentRow1998 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 14) (by decide)
theorem parentRow_mem1999 : ParentOwnership.parentRow1999 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows124, parentChunk_mem124, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows124) (n := 15) (by decide)
theorem parentChunk_mem125 : ParentOwnership.parentRows125 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 125) (by decide)
theorem parentRow_mem2000 : ParentOwnership.parentRow2000 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 0) (by decide)
theorem parentRow_mem2001 : ParentOwnership.parentRow2001 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 1) (by decide)
theorem parentRow_mem2002 : ParentOwnership.parentRow2002 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 2) (by decide)
theorem parentRow_mem2003 : ParentOwnership.parentRow2003 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 3) (by decide)
theorem parentRow_mem2004 : ParentOwnership.parentRow2004 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 4) (by decide)
theorem parentRow_mem2005 : ParentOwnership.parentRow2005 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 5) (by decide)
theorem parentRow_mem2006 : ParentOwnership.parentRow2006 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 6) (by decide)
theorem parentRow_mem2007 : ParentOwnership.parentRow2007 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 7) (by decide)
theorem parentRow_mem2008 : ParentOwnership.parentRow2008 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 8) (by decide)
theorem parentRow_mem2009 : ParentOwnership.parentRow2009 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 9) (by decide)
theorem parentRow_mem2010 : ParentOwnership.parentRow2010 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 10) (by decide)
theorem parentRow_mem2011 : ParentOwnership.parentRow2011 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 11) (by decide)
theorem parentRow_mem2012 : ParentOwnership.parentRow2012 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 12) (by decide)
theorem parentRow_mem2013 : ParentOwnership.parentRow2013 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 13) (by decide)
theorem parentRow_mem2014 : ParentOwnership.parentRow2014 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 14) (by decide)
theorem parentRow_mem2015 : ParentOwnership.parentRow2015 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows125, parentChunk_mem125, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows125) (n := 15) (by decide)
theorem parentChunk_mem126 : ParentOwnership.parentRows126 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 126) (by decide)
theorem parentRow_mem2016 : ParentOwnership.parentRow2016 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 0) (by decide)
theorem parentRow_mem2017 : ParentOwnership.parentRow2017 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 1) (by decide)
theorem parentRow_mem2018 : ParentOwnership.parentRow2018 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 2) (by decide)
theorem parentRow_mem2019 : ParentOwnership.parentRow2019 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 3) (by decide)
theorem parentRow_mem2020 : ParentOwnership.parentRow2020 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 4) (by decide)
theorem parentRow_mem2021 : ParentOwnership.parentRow2021 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 5) (by decide)
theorem parentRow_mem2022 : ParentOwnership.parentRow2022 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 6) (by decide)
theorem parentRow_mem2023 : ParentOwnership.parentRow2023 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 7) (by decide)
theorem parentRow_mem2024 : ParentOwnership.parentRow2024 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 8) (by decide)
theorem parentRow_mem2025 : ParentOwnership.parentRow2025 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 9) (by decide)
theorem parentRow_mem2026 : ParentOwnership.parentRow2026 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 10) (by decide)
theorem parentRow_mem2027 : ParentOwnership.parentRow2027 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 11) (by decide)
theorem parentRow_mem2028 : ParentOwnership.parentRow2028 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 12) (by decide)
theorem parentRow_mem2029 : ParentOwnership.parentRow2029 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 13) (by decide)
theorem parentRow_mem2030 : ParentOwnership.parentRow2030 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 14) (by decide)
theorem parentRow_mem2031 : ParentOwnership.parentRow2031 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows126, parentChunk_mem126, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows126) (n := 15) (by decide)
theorem parentChunk_mem127 : ParentOwnership.parentRows127 ∈ ParentOwnership.certifiedParentChunks := List.getElem_mem (l := ParentOwnership.certifiedParentChunks) (n := 127) (by decide)
theorem parentRow_mem2032 : ParentOwnership.parentRow2032 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 0) (by decide)
theorem parentRow_mem2033 : ParentOwnership.parentRow2033 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 1) (by decide)
theorem parentRow_mem2034 : ParentOwnership.parentRow2034 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 2) (by decide)
theorem parentRow_mem2035 : ParentOwnership.parentRow2035 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 3) (by decide)
theorem parentRow_mem2036 : ParentOwnership.parentRow2036 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 4) (by decide)
theorem parentRow_mem2037 : ParentOwnership.parentRow2037 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 5) (by decide)
theorem parentRow_mem2038 : ParentOwnership.parentRow2038 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 6) (by decide)
theorem parentRow_mem2039 : ParentOwnership.parentRow2039 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 7) (by decide)
theorem parentRow_mem2040 : ParentOwnership.parentRow2040 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 8) (by decide)
theorem parentRow_mem2041 : ParentOwnership.parentRow2041 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 9) (by decide)
theorem parentRow_mem2042 : ParentOwnership.parentRow2042 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 10) (by decide)
theorem parentRow_mem2043 : ParentOwnership.parentRow2043 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 11) (by decide)
theorem parentRow_mem2044 : ParentOwnership.parentRow2044 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 12) (by decide)
theorem parentRow_mem2045 : ParentOwnership.parentRow2045 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 13) (by decide)
theorem parentRow_mem2046 : ParentOwnership.parentRow2046 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 14) (by decide)
theorem parentRow_mem2047 : ParentOwnership.parentRow2047 ∈ ParentOwnership.certifiedParentRows := by
  apply List.mem_flatten.mpr
  refine ⟨ParentOwnership.parentRows127, parentChunk_mem127, ?_⟩
  exact List.getElem_mem (l := ParentOwnership.parentRows127) (n := 15) (by decide)

end SpectreFinite.HexSearch.RadiusFiveParentBinding
