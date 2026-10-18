module

public import SpectreFinite.ParentOwnershipFinite

@[expose] public section


/-! A kernel-checked census of every Gamma-turn-zero row in the entire
2112-row family. This asserts no occurrence completeness. -/
namespace SpectreFinite.HexSearch.ParentBoundary
open ParentOwnership

def gammaRoot (row : List State) : Bool := decide (indexedField row (0,0) = (0,0))
def gammaBoundaryRows : List (List State) := [parentRow0064,parentRow0065,parentRow0070,parentRow0071,parentRow0072,parentRow0080,parentRow0102,parentRow0103,parentRow0104,parentRow0105,parentRow0106,parentRow0107,parentRow0108,parentRow0109,parentRow0110,parentRow0111,parentRow0112,parentRow0308,parentRow0309,parentRow0514,parentRow1074,parentRow1075,parentRow1262,parentRow1263,parentRow1264,parentRow1265,parentRow1266,parentRow1273,parentRow1274,parentRow1275,parentRow1276,parentRow1277,parentRow1278,parentRow1279,parentRow1280,parentRow1281,parentRow1282,parentRow1283,parentRow1284,parentRow1285,parentRow1287,parentRow1288,parentRow1289,parentRow1290,parentRow1291]

private theorem gammaChunk000 : parentRows000.filter gammaRoot = [] := by decide
private theorem gammaChunk001 : parentRows001.filter gammaRoot = [] := by decide
private theorem gammaChunk002 : parentRows002.filter gammaRoot = [] := by decide
private theorem gammaChunk003 : parentRows003.filter gammaRoot = [] := by decide
private theorem gammaChunk004 : parentRows004.filter gammaRoot = [parentRow0064,parentRow0065,parentRow0070,parentRow0071,parentRow0072] := by decide
private theorem gammaChunk005 : parentRows005.filter gammaRoot = [parentRow0080] := by decide
private theorem gammaChunk006 : parentRows006.filter gammaRoot = [parentRow0102,parentRow0103,parentRow0104,parentRow0105,parentRow0106,parentRow0107,parentRow0108,parentRow0109,parentRow0110,parentRow0111] := by decide
private theorem gammaChunk007 : parentRows007.filter gammaRoot = [parentRow0112] := by decide
private theorem gammaChunk008 : parentRows008.filter gammaRoot = [] := by decide
private theorem gammaChunk009 : parentRows009.filter gammaRoot = [] := by decide
private theorem gammaChunk010 : parentRows010.filter gammaRoot = [] := by decide
private theorem gammaChunk011 : parentRows011.filter gammaRoot = [] := by decide
private theorem gammaChunk012 : parentRows012.filter gammaRoot = [] := by decide
private theorem gammaChunk013 : parentRows013.filter gammaRoot = [] := by decide
private theorem gammaChunk014 : parentRows014.filter gammaRoot = [] := by decide
private theorem gammaChunk015 : parentRows015.filter gammaRoot = [] := by decide
private theorem gammaChunk016 : parentRows016.filter gammaRoot = [] := by decide
private theorem gammaChunk017 : parentRows017.filter gammaRoot = [] := by decide
private theorem gammaChunk018 : parentRows018.filter gammaRoot = [] := by decide
private theorem gammaChunk019 : parentRows019.filter gammaRoot = [parentRow0308,parentRow0309] := by decide
private theorem gammaChunk020 : parentRows020.filter gammaRoot = [] := by decide
private theorem gammaChunk021 : parentRows021.filter gammaRoot = [] := by decide
private theorem gammaChunk022 : parentRows022.filter gammaRoot = [] := by decide
private theorem gammaChunk023 : parentRows023.filter gammaRoot = [] := by decide
private theorem gammaChunk024 : parentRows024.filter gammaRoot = [] := by decide
private theorem gammaChunk025 : parentRows025.filter gammaRoot = [] := by decide
private theorem gammaChunk026 : parentRows026.filter gammaRoot = [] := by decide
private theorem gammaChunk027 : parentRows027.filter gammaRoot = [] := by decide
private theorem gammaChunk028 : parentRows028.filter gammaRoot = [] := by decide
private theorem gammaChunk029 : parentRows029.filter gammaRoot = [] := by decide
private theorem gammaChunk030 : parentRows030.filter gammaRoot = [] := by decide
private theorem gammaChunk031 : parentRows031.filter gammaRoot = [] := by decide
private theorem gammaChunk032 : parentRows032.filter gammaRoot = [parentRow0514] := by decide
private theorem gammaChunk033 : parentRows033.filter gammaRoot = [] := by decide
private theorem gammaChunk034 : parentRows034.filter gammaRoot = [] := by decide
private theorem gammaChunk035 : parentRows035.filter gammaRoot = [] := by decide
private theorem gammaChunk036 : parentRows036.filter gammaRoot = [] := by decide
private theorem gammaChunk037 : parentRows037.filter gammaRoot = [] := by decide
private theorem gammaChunk038 : parentRows038.filter gammaRoot = [] := by decide
private theorem gammaChunk039 : parentRows039.filter gammaRoot = [] := by decide
private theorem gammaChunk040 : parentRows040.filter gammaRoot = [] := by decide
private theorem gammaChunk041 : parentRows041.filter gammaRoot = [] := by decide
private theorem gammaChunk042 : parentRows042.filter gammaRoot = [] := by decide
private theorem gammaChunk043 : parentRows043.filter gammaRoot = [] := by decide
private theorem gammaChunk044 : parentRows044.filter gammaRoot = [] := by decide
private theorem gammaChunk045 : parentRows045.filter gammaRoot = [] := by decide
private theorem gammaChunk046 : parentRows046.filter gammaRoot = [] := by decide
private theorem gammaChunk047 : parentRows047.filter gammaRoot = [] := by decide
private theorem gammaChunk048 : parentRows048.filter gammaRoot = [] := by decide
private theorem gammaChunk049 : parentRows049.filter gammaRoot = [] := by decide
private theorem gammaChunk050 : parentRows050.filter gammaRoot = [] := by decide
private theorem gammaChunk051 : parentRows051.filter gammaRoot = [] := by decide
private theorem gammaChunk052 : parentRows052.filter gammaRoot = [] := by decide
private theorem gammaChunk053 : parentRows053.filter gammaRoot = [] := by decide
private theorem gammaChunk054 : parentRows054.filter gammaRoot = [] := by decide
private theorem gammaChunk055 : parentRows055.filter gammaRoot = [] := by decide
private theorem gammaChunk056 : parentRows056.filter gammaRoot = [] := by decide
private theorem gammaChunk057 : parentRows057.filter gammaRoot = [] := by decide
private theorem gammaChunk058 : parentRows058.filter gammaRoot = [] := by decide
private theorem gammaChunk059 : parentRows059.filter gammaRoot = [] := by decide
private theorem gammaChunk060 : parentRows060.filter gammaRoot = [] := by decide
private theorem gammaChunk061 : parentRows061.filter gammaRoot = [] := by decide
private theorem gammaChunk062 : parentRows062.filter gammaRoot = [] := by decide
private theorem gammaChunk063 : parentRows063.filter gammaRoot = [] := by decide
private theorem gammaChunk064 : parentRows064.filter gammaRoot = [] := by decide
private theorem gammaChunk065 : parentRows065.filter gammaRoot = [] := by decide
private theorem gammaChunk066 : parentRows066.filter gammaRoot = [] := by decide
private theorem gammaChunk067 : parentRows067.filter gammaRoot = [parentRow1074,parentRow1075] := by decide
private theorem gammaChunk068 : parentRows068.filter gammaRoot = [] := by decide
private theorem gammaChunk069 : parentRows069.filter gammaRoot = [] := by decide
private theorem gammaChunk070 : parentRows070.filter gammaRoot = [] := by decide
private theorem gammaChunk071 : parentRows071.filter gammaRoot = [] := by decide
private theorem gammaChunk072 : parentRows072.filter gammaRoot = [] := by decide
private theorem gammaChunk073 : parentRows073.filter gammaRoot = [] := by decide
private theorem gammaChunk074 : parentRows074.filter gammaRoot = [] := by decide
private theorem gammaChunk075 : parentRows075.filter gammaRoot = [] := by decide
private theorem gammaChunk076 : parentRows076.filter gammaRoot = [] := by decide
private theorem gammaChunk077 : parentRows077.filter gammaRoot = [] := by decide
private theorem gammaChunk078 : parentRows078.filter gammaRoot = [parentRow1262,parentRow1263] := by decide
private theorem gammaChunk079 : parentRows079.filter gammaRoot = [parentRow1264,parentRow1265,parentRow1266,parentRow1273,parentRow1274,parentRow1275,parentRow1276,parentRow1277,parentRow1278,parentRow1279] := by decide
private theorem gammaChunk080 : parentRows080.filter gammaRoot = [parentRow1280,parentRow1281,parentRow1282,parentRow1283,parentRow1284,parentRow1285,parentRow1287,parentRow1288,parentRow1289,parentRow1290,parentRow1291] := by decide
private theorem gammaChunk081 : parentRows081.filter gammaRoot = [] := by decide
private theorem gammaChunk082 : parentRows082.filter gammaRoot = [] := by decide
private theorem gammaChunk083 : parentRows083.filter gammaRoot = [] := by decide
private theorem gammaChunk084 : parentRows084.filter gammaRoot = [] := by decide
private theorem gammaChunk085 : parentRows085.filter gammaRoot = [] := by decide
private theorem gammaChunk086 : parentRows086.filter gammaRoot = [] := by decide
private theorem gammaChunk087 : parentRows087.filter gammaRoot = [] := by decide
private theorem gammaChunk088 : parentRows088.filter gammaRoot = [] := by decide
private theorem gammaChunk089 : parentRows089.filter gammaRoot = [] := by decide
private theorem gammaChunk090 : parentRows090.filter gammaRoot = [] := by decide
private theorem gammaChunk091 : parentRows091.filter gammaRoot = [] := by decide
private theorem gammaChunk092 : parentRows092.filter gammaRoot = [] := by decide
private theorem gammaChunk093 : parentRows093.filter gammaRoot = [] := by decide
private theorem gammaChunk094 : parentRows094.filter gammaRoot = [] := by decide
private theorem gammaChunk095 : parentRows095.filter gammaRoot = [] := by decide
private theorem gammaChunk096 : parentRows096.filter gammaRoot = [] := by decide
private theorem gammaChunk097 : parentRows097.filter gammaRoot = [] := by decide
private theorem gammaChunk098 : parentRows098.filter gammaRoot = [] := by decide
private theorem gammaChunk099 : parentRows099.filter gammaRoot = [] := by decide
private theorem gammaChunk100 : parentRows100.filter gammaRoot = [] := by decide
private theorem gammaChunk101 : parentRows101.filter gammaRoot = [] := by decide
private theorem gammaChunk102 : parentRows102.filter gammaRoot = [] := by decide
private theorem gammaChunk103 : parentRows103.filter gammaRoot = [] := by decide
private theorem gammaChunk104 : parentRows104.filter gammaRoot = [] := by decide
private theorem gammaChunk105 : parentRows105.filter gammaRoot = [] := by decide
private theorem gammaChunk106 : parentRows106.filter gammaRoot = [] := by decide
private theorem gammaChunk107 : parentRows107.filter gammaRoot = [] := by decide
private theorem gammaChunk108 : parentRows108.filter gammaRoot = [] := by decide
private theorem gammaChunk109 : parentRows109.filter gammaRoot = [] := by decide
private theorem gammaChunk110 : parentRows110.filter gammaRoot = [] := by decide
private theorem gammaChunk111 : parentRows111.filter gammaRoot = [] := by decide
private theorem gammaChunk112 : parentRows112.filter gammaRoot = [] := by decide
private theorem gammaChunk113 : parentRows113.filter gammaRoot = [] := by decide
private theorem gammaChunk114 : parentRows114.filter gammaRoot = [] := by decide
private theorem gammaChunk115 : parentRows115.filter gammaRoot = [] := by decide
private theorem gammaChunk116 : parentRows116.filter gammaRoot = [] := by decide
private theorem gammaChunk117 : parentRows117.filter gammaRoot = [] := by decide
private theorem gammaChunk118 : parentRows118.filter gammaRoot = [] := by decide
private theorem gammaChunk119 : parentRows119.filter gammaRoot = [] := by decide
private theorem gammaChunk120 : parentRows120.filter gammaRoot = [] := by decide
private theorem gammaChunk121 : parentRows121.filter gammaRoot = [] := by decide
private theorem gammaChunk122 : parentRows122.filter gammaRoot = [] := by decide
private theorem gammaChunk123 : parentRows123.filter gammaRoot = [] := by decide
private theorem gammaChunk124 : parentRows124.filter gammaRoot = [] := by decide
private theorem gammaChunk125 : parentRows125.filter gammaRoot = [] := by decide
private theorem gammaChunk126 : parentRows126.filter gammaRoot = [] := by decide
private theorem gammaChunk127 : parentRows127.filter gammaRoot = [] := by decide
private theorem gammaChunk128 : parentRows128.filter gammaRoot = [] := by decide
private theorem gammaChunk129 : parentRows129.filter gammaRoot = [] := by decide
private theorem gammaChunk130 : parentRows130.filter gammaRoot = [] := by decide
private theorem gammaChunk131 : parentRows131.filter gammaRoot = [] := by decide

theorem gammaBoundaryRows_exact : certifiedParentRows.filter gammaRoot = gammaBoundaryRows := by
  unfold certifiedParentRows
  rw [List.filter_flatten]
  simp only [certifiedParentChunks, List.map_cons, List.map_nil,
    gammaChunk000, gammaChunk001, gammaChunk002, gammaChunk003, gammaChunk004, gammaChunk005, gammaChunk006, gammaChunk007, gammaChunk008, gammaChunk009, gammaChunk010, gammaChunk011, gammaChunk012, gammaChunk013, gammaChunk014, gammaChunk015, gammaChunk016, gammaChunk017, gammaChunk018, gammaChunk019, gammaChunk020, gammaChunk021, gammaChunk022, gammaChunk023, gammaChunk024, gammaChunk025, gammaChunk026, gammaChunk027, gammaChunk028, gammaChunk029, gammaChunk030, gammaChunk031, gammaChunk032, gammaChunk033, gammaChunk034, gammaChunk035, gammaChunk036, gammaChunk037, gammaChunk038, gammaChunk039, gammaChunk040, gammaChunk041, gammaChunk042, gammaChunk043, gammaChunk044, gammaChunk045, gammaChunk046, gammaChunk047, gammaChunk048, gammaChunk049, gammaChunk050, gammaChunk051, gammaChunk052, gammaChunk053, gammaChunk054, gammaChunk055, gammaChunk056, gammaChunk057, gammaChunk058, gammaChunk059, gammaChunk060, gammaChunk061, gammaChunk062, gammaChunk063, gammaChunk064, gammaChunk065, gammaChunk066, gammaChunk067, gammaChunk068, gammaChunk069, gammaChunk070, gammaChunk071, gammaChunk072, gammaChunk073, gammaChunk074, gammaChunk075, gammaChunk076, gammaChunk077, gammaChunk078, gammaChunk079, gammaChunk080, gammaChunk081, gammaChunk082, gammaChunk083, gammaChunk084, gammaChunk085, gammaChunk086, gammaChunk087, gammaChunk088, gammaChunk089, gammaChunk090, gammaChunk091, gammaChunk092, gammaChunk093, gammaChunk094, gammaChunk095, gammaChunk096, gammaChunk097, gammaChunk098, gammaChunk099, gammaChunk100, gammaChunk101, gammaChunk102, gammaChunk103, gammaChunk104, gammaChunk105, gammaChunk106, gammaChunk107, gammaChunk108, gammaChunk109, gammaChunk110, gammaChunk111, gammaChunk112, gammaChunk113, gammaChunk114, gammaChunk115, gammaChunk116, gammaChunk117, gammaChunk118, gammaChunk119, gammaChunk120, gammaChunk121, gammaChunk122, gammaChunk123, gammaChunk124, gammaChunk125, gammaChunk126, gammaChunk127, gammaChunk128, gammaChunk129, gammaChunk130, gammaChunk131]
  rfl

theorem gammaBoundaryRows_count : gammaBoundaryRows.length = 45 := rfl

theorem certifiedParentRows_gamma_count :
    (certifiedParentRows.filter gammaRoot).length = 45 := by
  rw [gammaBoundaryRows_exact, gammaBoundaryRows_count]

#print axioms gammaBoundaryRows_exact
#print axioms certifiedParentRows_gamma_count
end SpectreFinite.HexSearch.ParentBoundary
