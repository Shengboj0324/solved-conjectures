import Conjectures.LiBridge
import Conjectures.LiBasic

/-!
# Five exact three-colour evaluations of Li's tree

For `r = 1, ..., 5`, this module evaluates the actual chromatic polynomial
at `(1, r, -1-r)`. It uses the general leaf-elimination theorem contributed
by aadrianvv in PR #35. The numerical update tables are untrusted data:
every entry is proved by exact arithmetic, and the graph-theoretic
leaf conditions are checked separately before the thirty steps are joined.

These evaluations supply data for elementary-coefficient interpolation.
They are not, by themselves, a coefficient-extraction theorem.
-/

open scoped BigOperators

namespace LiEvaluation

/-- The five triples `(1,r,-1-r)`, with `r = j + 1`. -/
def colorWeights (j : Fin 5) : Fin 3 → ℚ :=
  ![1, (j.val : ℚ) + 1, -((j.val : ℚ) + 2)]

/-- The exact values, in increasing order of `r`. -/
def values : Fin 5 → ℚ :=
  ![990877086, 172175555938218, 83260158020643396,
    -919551298160859490980, -475047863403291617208270]

/-- The thirty leaf removals, leaving vertex zero. -/
def leafOrder : List (Fin 31) :=
  [30,29,28,27,26,25,24,23,22,21,20,19,18,17,16,
   14,13,12,11,10,9,15,8,7,6,5,4,3,2,1]

/-- The leaf at a numbered step. Only indices below thirty are used. -/
def leaf (i : ℕ) : Fin 31 := leafOrder.getD i 0

/-- Its parent in the actual rooted tree. -/
def parent (i : ℕ) : Fin 31 := Li.parOf (leaf i)

/-- Vertices remaining before step `i`. -/
def active (i : ℕ) : Finset (Fin 31) :=
  Finset.univ \ (leafOrder.take i).toFinset

/-- Each row is the updated parent's three weights for each of five inputs. -/
def updateTable : List (Fin 5 → Fin 3 → ℚ) := [
  ![![-1, -1, -4],
    ![-1, -4, -9],
    ![-1, -9, -16],
    ![-1, -16, -25],
    ![-1, -25, -36]],
  ![![-5, -5, 4],
    ![-13, -20, 15],
    ![-25, -51, 40],
    ![-41, -104, 85],
    ![-61, -185, 156]],
  ![![-1, -1, 20],
    ![-5, 4, 99],
    ![-11, 45, 304],
    ![-19, 176, 725],
    ![-29, 475, 1476]],
  ![![19, 19, 4],
    ![103, 188, 3],
    ![349, 879, -136],
    ![901, 2824, -785],
    ![1951, 7235, -2676]],
  ![![23, 23, -76],
    ![191, 212, -873],
    ![743, 639, -4912],
    ![2039, 464, -18625],
    ![4559, -3625, -55116]],
  ![![-53, -53, -92],
    ![-661, -1364, -1209],
    ![-4273, -12507, -5528],
    ![-18161, -66344, -12515],
    ![-58741, -252785, -5604]],
  ![![-145, -145, 212],
    ![-2573, -3740, 6075],
    ![-18035, -29403, 67120],
    ![-78859, -122704, 422525],
    ![-258389, -321725, 1869156]],
  ![![67, 67, 580],
    ![2335, 7004, 18939],
    ![37717, 147255, 189752],
    ![299821, 1374664, 1007815],
    ![1547431, 8053835, 3480684]],
  ![![647, 647, -268],
    ![25943, 42548, -28017],
    ![337007, 682407, -739888],
    ![2382479, 5230544, -8372425],
    ![11534519, 25140575, -57607596]],
  ![![379, 379, -2588],
    ![14531, -4148, -205473],
    ![-57481, -1208643, -4077656],
    ![-3141881, -23959784, -38065115],
    ![-32467021, -230365385, -220050564]],
  ![![-2209, -2209, -1516],
    ![-209621, -381884, -31149],
    ![-5286299, -12405411, 5064496],
    ![-62024899, -164827984, 135508325],
    ![-450415949, -1262587925, 1576994436]],
  ![![-3725, -3725, 8836],
    ![-413033, -481540, 1774515],
    ![-7340915, -665409, 70766840],
    ![-29319659, 293933704, 1134264415],
    ![314406511, 5632892435, 10278023244]],
  ![![5111, 5111, 14900],
    ![1292975, 2722964, 2683719],
    ![70101431, 190277775, 32025296],
    ![1428198119, 4419779024, -1323070225],
    ![15910915679, 52962148775, -35683793676]],
  ![![20011, 20011, -20444],
    ![5406683, 7953388, -12047817],
    ![222303071, 306380181, -1041516824],
    ![3096708799, 420511576, -29239885715],
    ![17278355099, -98864389985, -413238386724]],
  ![![-433, -433, -80044],
    ![-4094429, -13282268, -40080213],
    ![-735136643, -2457641259, -2114733008],
    ![-28819374139, -104572707664, -17586101875],
    ![-512102776709, -1979800158125, 489516209316]],
  ![![-1, -1, -4],
    ![-1, -4, -9],
    ![-1, -9, -16],
    ![-1, -16, -25],
    ![-1, -25, -36]],
  ![![-5, -5, 4],
    ![-13, -20, 15],
    ![-25, -51, 40],
    ![-41, -104, 85],
    ![-61, -185, 156]],
  ![![-1, -1, 20],
    ![-5, 4, 99],
    ![-11, 45, 304],
    ![-19, 176, 725],
    ![-29, 475, 1476]],
  ![![19, 19, 4],
    ![103, 188, 3],
    ![349, 879, -136],
    ![901, 2824, -785],
    ![1951, 7235, -2676]],
  ![![23, 23, -76],
    ![191, 212, -873],
    ![743, 639, -4912],
    ![2039, 464, -18625],
    ![4559, -3625, -55116]],
  ![![-53, -53, -92],
    ![-661, -1364, -1209],
    ![-4273, -12507, -5528],
    ![-18161, -66344, -12515],
    ![-58741, -252785, -5604]],
  ![![53, 53, -184],
    ![661, 2728, -3627],
    ![4273, 37521, -22112],
    ![18161, 265376, -62575],
    ![58741, 1263925, -33624]],
  ![![-131, -131, -212],
    ![-899, -5932, -10167],
    ![15409, -53517, -167176],
    ![202801, -177656, -1417685],
    ![1230301, 125585, -7935996]],
  ![![-343, -343, 524],
    ![-16099, -22132, 20493],
    ![-220693, -455301, 152432],
    ![-1595341, -4859536, -125725],
    ![-7810411, -33528475, -8135316]],
  ![![181, 181, 1372],
    ![-1639, 8788, 114693],
    ![-302869, -204783, 2703976],
    ![-4985261, -6884264, 32274385],
    ![-41663791, -79728635, 248033316]],
  ![![1553, 1553, -724],
    ![123481, 226108, -21447],
    ![2499193, 7203321, 2030608],
    ![25390121, 109156496, 59347625],
    ![168304681, 1031847625, 728354556]],
  ![![-358957, -358957, -248616664],
    ![-837969933569, -1355242933112, -14011601582457],
    ![-6788199566760347, -11132625832659459, -20518226616382112],
    ![-4856183307062326819, -8861255540564285344, -2366150513498606875],
    ![-901404424459337802329, -1775206099196841850625, 587494007434976082696]],
  ![![-1, -1, -4],
    ![-1, -4, -9],
    ![-1, -9, -16],
    ![-1, -16, -25],
    ![-1, -25, -36]],
  ![![1794785, 1794785, 497233328],
    ![10893609136397, 13552429331120, 70058007912285],
    ![169704989169008675, 189254639155210803, 205182266163821120],
    ![199103515589555399579, 230392644054671418944, 40224558729476316875],
    ![54985669892019605942069, 65682625670283148473125, -15274844193309378150096]],
  ![![-1794785, -1794785, 994466656],
    ![-10893609136397, -27104858662240, 210174023736855],
    ![-169704989169008675, -567763917465632409, 820729064655284480],
    ![-199103515589555399579, -921570576218685675776, 201122793647381584375],
    ![-54985669892019605942069, -328413128351415742365625, -91649065159856268900576]]
]

/-- One numerical parent-weight row. -/
def nextWeights (i : ℕ) : Fin 5 → Fin 3 → ℚ := updateTable.getD i 0

/-- The complete vertex weights after the indicated number of eliminations. -/
def stageWeights : ℕ → Fin 5 → Fin 31 → Fin 3 → ℚ
  | 0, j => fun _ => colorWeights j
  | i + 1, j => Function.update (stageWeights i j) (parent i) (nextWeights i j)

theorem active_zero : active 0 = Finset.univ := by decide

theorem active_thirty : active 30 = {0} := by decide

/-! The leaf hypotheses are decided in three ranges of ten stages each. One
decision over all thirty stages exceeds the CI memory cap. -/

set_option maxRecDepth 100000 in
theorem leaf_conditions_part0 : ∀ i : Fin 30, i.val / 10 = 0 →
    leaf i.val ∈ active i.val ∧ parent i.val ∈ active i.val ∧
    Li.T.Adj (leaf i.val) (parent i.val) ∧
    (∀ v ∈ active i.val, Li.T.Adj (leaf i.val) v → v = parent i.val) ∧
    active (i.val + 1) = (active i.val).erase (leaf i.val) := by
  decide

set_option maxRecDepth 100000 in
theorem leaf_conditions_part1 : ∀ i : Fin 30, i.val / 10 = 1 →
    leaf i.val ∈ active i.val ∧ parent i.val ∈ active i.val ∧
    Li.T.Adj (leaf i.val) (parent i.val) ∧
    (∀ v ∈ active i.val, Li.T.Adj (leaf i.val) v → v = parent i.val) ∧
    active (i.val + 1) = (active i.val).erase (leaf i.val) := by
  decide

set_option maxRecDepth 100000 in
theorem leaf_conditions_part2 : ∀ i : Fin 30, i.val / 10 = 2 →
    leaf i.val ∈ active i.val ∧ parent i.val ∈ active i.val ∧
    Li.T.Adj (leaf i.val) (parent i.val) ∧
    (∀ v ∈ active i.val, Li.T.Adj (leaf i.val) v → v = parent i.val) ∧
    active (i.val + 1) = (active i.val).erase (leaf i.val) := by
  decide

/-- All leaf hypotheses concern the actual graph and the actual remaining vertices. -/
theorem leaf_conditions : ∀ i : Fin 30,
    leaf i.val ∈ active i.val ∧ parent i.val ∈ active i.val ∧
    Li.T.Adj (leaf i.val) (parent i.val) ∧
    (∀ v ∈ active i.val, Li.T.Adj (leaf i.val) v → v = parent i.val) ∧
    active (i.val + 1) = (active i.val).erase (leaf i.val) := by
  intro i
  have hi := i.isLt
  rcases (by omega : i.val / 10 = 0 ∨ i.val / 10 = 1 ∨ i.val / 10 = 2) with h | h | h
  · exact leaf_conditions_part0 i h
  · exact leaf_conditions_part1 i h
  · exact leaf_conditions_part2 i h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_00 (j : Fin 5) :
    stageWeights 0 j (parent 0) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_00 (j : Fin 5) :
    stageWeights 0 j (leaf 0) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_01 (j : Fin 5) :
    stageWeights 1 j (parent 1) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_01 (j : Fin 5) :
    stageWeights 1 j (leaf 1) = nextWeights 0 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_02 (j : Fin 5) :
    stageWeights 2 j (parent 2) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_02 (j : Fin 5) :
    stageWeights 2 j (leaf 2) = nextWeights 1 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_03 (j : Fin 5) :
    stageWeights 3 j (parent 3) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_03 (j : Fin 5) :
    stageWeights 3 j (leaf 3) = nextWeights 2 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_04 (j : Fin 5) :
    stageWeights 4 j (parent 4) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_04 (j : Fin 5) :
    stageWeights 4 j (leaf 4) = nextWeights 3 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_05 (j : Fin 5) :
    stageWeights 5 j (parent 5) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_05 (j : Fin 5) :
    stageWeights 5 j (leaf 5) = nextWeights 4 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_06 (j : Fin 5) :
    stageWeights 6 j (parent 6) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_06 (j : Fin 5) :
    stageWeights 6 j (leaf 6) = nextWeights 5 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_07 (j : Fin 5) :
    stageWeights 7 j (parent 7) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_07 (j : Fin 5) :
    stageWeights 7 j (leaf 7) = nextWeights 6 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_08 (j : Fin 5) :
    stageWeights 8 j (parent 8) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_08 (j : Fin 5) :
    stageWeights 8 j (leaf 8) = nextWeights 7 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_09 (j : Fin 5) :
    stageWeights 9 j (parent 9) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_09 (j : Fin 5) :
    stageWeights 9 j (leaf 9) = nextWeights 8 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_10 (j : Fin 5) :
    stageWeights 10 j (parent 10) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_10 (j : Fin 5) :
    stageWeights 10 j (leaf 10) = nextWeights 9 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_11 (j : Fin 5) :
    stageWeights 11 j (parent 11) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_11 (j : Fin 5) :
    stageWeights 11 j (leaf 11) = nextWeights 10 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_12 (j : Fin 5) :
    stageWeights 12 j (parent 12) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_12 (j : Fin 5) :
    stageWeights 12 j (leaf 12) = nextWeights 11 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_13 (j : Fin 5) :
    stageWeights 13 j (parent 13) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_13 (j : Fin 5) :
    stageWeights 13 j (leaf 13) = nextWeights 12 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_14 (j : Fin 5) :
    stageWeights 14 j (parent 14) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_14 (j : Fin 5) :
    stageWeights 14 j (leaf 14) = nextWeights 13 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_15 (j : Fin 5) :
    stageWeights 15 j (parent 15) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_15 (j : Fin 5) :
    stageWeights 15 j (leaf 15) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_16 (j : Fin 5) :
    stageWeights 16 j (parent 16) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_16 (j : Fin 5) :
    stageWeights 16 j (leaf 16) = nextWeights 15 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_17 (j : Fin 5) :
    stageWeights 17 j (parent 17) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_17 (j : Fin 5) :
    stageWeights 17 j (leaf 17) = nextWeights 16 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_18 (j : Fin 5) :
    stageWeights 18 j (parent 18) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_18 (j : Fin 5) :
    stageWeights 18 j (leaf 18) = nextWeights 17 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_19 (j : Fin 5) :
    stageWeights 19 j (parent 19) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_19 (j : Fin 5) :
    stageWeights 19 j (leaf 19) = nextWeights 18 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_20 (j : Fin 5) :
    stageWeights 20 j (parent 20) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_20 (j : Fin 5) :
    stageWeights 20 j (leaf 20) = nextWeights 19 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_21 (j : Fin 5) :
    stageWeights 21 j (parent 21) = nextWeights 20 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_21 (j : Fin 5) :
    stageWeights 21 j (leaf 21) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_22 (j : Fin 5) :
    stageWeights 22 j (parent 22) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_22 (j : Fin 5) :
    stageWeights 22 j (leaf 22) = nextWeights 21 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_23 (j : Fin 5) :
    stageWeights 23 j (parent 23) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_23 (j : Fin 5) :
    stageWeights 23 j (leaf 23) = nextWeights 22 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_24 (j : Fin 5) :
    stageWeights 24 j (parent 24) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_24 (j : Fin 5) :
    stageWeights 24 j (leaf 24) = nextWeights 23 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_25 (j : Fin 5) :
    stageWeights 25 j (parent 25) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_25 (j : Fin 5) :
    stageWeights 25 j (leaf 25) = nextWeights 24 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_26 (j : Fin 5) :
    stageWeights 26 j (parent 26) = nextWeights 14 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_26 (j : Fin 5) :
    stageWeights 26 j (leaf 26) = nextWeights 25 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_27 (j : Fin 5) :
    stageWeights 27 j (parent 27) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_27 (j : Fin 5) :
    stageWeights 27 j (leaf 27) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_28 (j : Fin 5) :
    stageWeights 28 j (parent 28) = nextWeights 26 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_28 (j : Fin 5) :
    stageWeights 28 j (leaf 28) = nextWeights 27 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem parent_weights_29 (j : Fin 5) :
    stageWeights 29 j (parent 29) = nextWeights 28 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem leaf_weights_29 (j : Fin 5) :
    stageWeights 29 j (leaf 29) = colorWeights j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_00 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 0 j c =
      stageWeights 0 j (parent 0) c *
        ((∑ d : Fin 3, stageWeights 0 j (leaf 0) d) -
          stageWeights 0 j (leaf 0) c) := by
  intro j c
  simp only [parent_weights_00, leaf_weights_00]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_01 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 1 j c =
      stageWeights 1 j (parent 1) c *
        ((∑ d : Fin 3, stageWeights 1 j (leaf 1) d) -
          stageWeights 1 j (leaf 1) c) := by
  intro j c
  simp only [parent_weights_01, leaf_weights_01]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_02 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 2 j c =
      stageWeights 2 j (parent 2) c *
        ((∑ d : Fin 3, stageWeights 2 j (leaf 2) d) -
          stageWeights 2 j (leaf 2) c) := by
  intro j c
  simp only [parent_weights_02, leaf_weights_02]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_03 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 3 j c =
      stageWeights 3 j (parent 3) c *
        ((∑ d : Fin 3, stageWeights 3 j (leaf 3) d) -
          stageWeights 3 j (leaf 3) c) := by
  intro j c
  simp only [parent_weights_03, leaf_weights_03]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_04 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 4 j c =
      stageWeights 4 j (parent 4) c *
        ((∑ d : Fin 3, stageWeights 4 j (leaf 4) d) -
          stageWeights 4 j (leaf 4) c) := by
  intro j c
  simp only [parent_weights_04, leaf_weights_04]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_05 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 5 j c =
      stageWeights 5 j (parent 5) c *
        ((∑ d : Fin 3, stageWeights 5 j (leaf 5) d) -
          stageWeights 5 j (leaf 5) c) := by
  intro j c
  simp only [parent_weights_05, leaf_weights_05]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_06 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 6 j c =
      stageWeights 6 j (parent 6) c *
        ((∑ d : Fin 3, stageWeights 6 j (leaf 6) d) -
          stageWeights 6 j (leaf 6) c) := by
  intro j c
  simp only [parent_weights_06, leaf_weights_06]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_07 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 7 j c =
      stageWeights 7 j (parent 7) c *
        ((∑ d : Fin 3, stageWeights 7 j (leaf 7) d) -
          stageWeights 7 j (leaf 7) c) := by
  intro j c
  simp only [parent_weights_07, leaf_weights_07]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_08 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 8 j c =
      stageWeights 8 j (parent 8) c *
        ((∑ d : Fin 3, stageWeights 8 j (leaf 8) d) -
          stageWeights 8 j (leaf 8) c) := by
  intro j c
  simp only [parent_weights_08, leaf_weights_08]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_09 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 9 j c =
      stageWeights 9 j (parent 9) c *
        ((∑ d : Fin 3, stageWeights 9 j (leaf 9) d) -
          stageWeights 9 j (leaf 9) c) := by
  intro j c
  simp only [parent_weights_09, leaf_weights_09]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_10 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 10 j c =
      stageWeights 10 j (parent 10) c *
        ((∑ d : Fin 3, stageWeights 10 j (leaf 10) d) -
          stageWeights 10 j (leaf 10) c) := by
  intro j c
  simp only [parent_weights_10, leaf_weights_10]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_11 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 11 j c =
      stageWeights 11 j (parent 11) c *
        ((∑ d : Fin 3, stageWeights 11 j (leaf 11) d) -
          stageWeights 11 j (leaf 11) c) := by
  intro j c
  simp only [parent_weights_11, leaf_weights_11]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_12 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 12 j c =
      stageWeights 12 j (parent 12) c *
        ((∑ d : Fin 3, stageWeights 12 j (leaf 12) d) -
          stageWeights 12 j (leaf 12) c) := by
  intro j c
  simp only [parent_weights_12, leaf_weights_12]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_13 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 13 j c =
      stageWeights 13 j (parent 13) c *
        ((∑ d : Fin 3, stageWeights 13 j (leaf 13) d) -
          stageWeights 13 j (leaf 13) c) := by
  intro j c
  simp only [parent_weights_13, leaf_weights_13]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_14 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 14 j c =
      stageWeights 14 j (parent 14) c *
        ((∑ d : Fin 3, stageWeights 14 j (leaf 14) d) -
          stageWeights 14 j (leaf 14) c) := by
  intro j c
  simp only [parent_weights_14, leaf_weights_14]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_15 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 15 j c =
      stageWeights 15 j (parent 15) c *
        ((∑ d : Fin 3, stageWeights 15 j (leaf 15) d) -
          stageWeights 15 j (leaf 15) c) := by
  intro j c
  simp only [parent_weights_15, leaf_weights_15]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_16 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 16 j c =
      stageWeights 16 j (parent 16) c *
        ((∑ d : Fin 3, stageWeights 16 j (leaf 16) d) -
          stageWeights 16 j (leaf 16) c) := by
  intro j c
  simp only [parent_weights_16, leaf_weights_16]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_17 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 17 j c =
      stageWeights 17 j (parent 17) c *
        ((∑ d : Fin 3, stageWeights 17 j (leaf 17) d) -
          stageWeights 17 j (leaf 17) c) := by
  intro j c
  simp only [parent_weights_17, leaf_weights_17]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_18 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 18 j c =
      stageWeights 18 j (parent 18) c *
        ((∑ d : Fin 3, stageWeights 18 j (leaf 18) d) -
          stageWeights 18 j (leaf 18) c) := by
  intro j c
  simp only [parent_weights_18, leaf_weights_18]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_19 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 19 j c =
      stageWeights 19 j (parent 19) c *
        ((∑ d : Fin 3, stageWeights 19 j (leaf 19) d) -
          stageWeights 19 j (leaf 19) c) := by
  intro j c
  simp only [parent_weights_19, leaf_weights_19]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_20 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 20 j c =
      stageWeights 20 j (parent 20) c *
        ((∑ d : Fin 3, stageWeights 20 j (leaf 20) d) -
          stageWeights 20 j (leaf 20) c) := by
  intro j c
  simp only [parent_weights_20, leaf_weights_20]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_21 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 21 j c =
      stageWeights 21 j (parent 21) c *
        ((∑ d : Fin 3, stageWeights 21 j (leaf 21) d) -
          stageWeights 21 j (leaf 21) c) := by
  intro j c
  simp only [parent_weights_21, leaf_weights_21]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_22 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 22 j c =
      stageWeights 22 j (parent 22) c *
        ((∑ d : Fin 3, stageWeights 22 j (leaf 22) d) -
          stageWeights 22 j (leaf 22) c) := by
  intro j c
  simp only [parent_weights_22, leaf_weights_22]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_23 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 23 j c =
      stageWeights 23 j (parent 23) c *
        ((∑ d : Fin 3, stageWeights 23 j (leaf 23) d) -
          stageWeights 23 j (leaf 23) c) := by
  intro j c
  simp only [parent_weights_23, leaf_weights_23]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_24 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 24 j c =
      stageWeights 24 j (parent 24) c *
        ((∑ d : Fin 3, stageWeights 24 j (leaf 24) d) -
          stageWeights 24 j (leaf 24) c) := by
  intro j c
  simp only [parent_weights_24, leaf_weights_24]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_25 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 25 j c =
      stageWeights 25 j (parent 25) c *
        ((∑ d : Fin 3, stageWeights 25 j (leaf 25) d) -
          stageWeights 25 j (leaf 25) c) := by
  intro j c
  simp only [parent_weights_25, leaf_weights_25]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_26 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 26 j c =
      stageWeights 26 j (parent 26) c *
        ((∑ d : Fin 3, stageWeights 26 j (leaf 26) d) -
          stageWeights 26 j (leaf 26) c) := by
  intro j c
  simp only [parent_weights_26, leaf_weights_26]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_27 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 27 j c =
      stageWeights 27 j (parent 27) c *
        ((∑ d : Fin 3, stageWeights 27 j (leaf 27) d) -
          stageWeights 27 j (leaf 27) c) := by
  intro j c
  simp only [parent_weights_27, leaf_weights_27]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_28 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 28 j c =
      stageWeights 28 j (parent 28) c *
        ((∑ d : Fin 3, stageWeights 28 j (leaf 28) d) -
          stageWeights 28 j (leaf 28) c) := by
  intro j c
  simp only [parent_weights_28, leaf_weights_28]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem table_correct_step_29 : ∀ (j : Fin 5) (c : Fin 3),
    nextWeights 29 j c =
      stageWeights 29 j (parent 29) c *
        ((∑ d : Fin 3, stageWeights 29 j (leaf 29) d) -
          stageWeights 29 j (leaf 29) c) := by
  intro j c
  simp only [parent_weights_29, leaf_weights_29]
  fin_cases j <;> fin_cases c <;>
    norm_num [nextWeights, updateTable, colorWeights, Fin.sum_univ_three]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every numerical update is the exact three-colour leaf recurrence. -/
theorem table_correct : ∀ (i : Fin 30) (j : Fin 5) (c : Fin 3),
    nextWeights i.val j c =
      stageWeights i.val j (parent i.val) c *
        ((∑ d : Fin 3, stageWeights i.val j (leaf i.val) d) -
          stageWeights i.val j (leaf i.val) c) := by
  intro i
  fin_cases i
  · exact table_correct_step_00
  · exact table_correct_step_01
  · exact table_correct_step_02
  · exact table_correct_step_03
  · exact table_correct_step_04
  · exact table_correct_step_05
  · exact table_correct_step_06
  · exact table_correct_step_07
  · exact table_correct_step_08
  · exact table_correct_step_09
  · exact table_correct_step_10
  · exact table_correct_step_11
  · exact table_correct_step_12
  · exact table_correct_step_13
  · exact table_correct_step_14
  · exact table_correct_step_15
  · exact table_correct_step_16
  · exact table_correct_step_17
  · exact table_correct_step_18
  · exact table_correct_step_19
  · exact table_correct_step_20
  · exact table_correct_step_21
  · exact table_correct_step_22
  · exact table_correct_step_23
  · exact table_correct_step_24
  · exact table_correct_step_25
  · exact table_correct_step_26
  · exact table_correct_step_27
  · exact table_correct_step_28
  · exact table_correct_step_29

/-- The checked table gives the actual weight update used by leaf elimination. -/
theorem stageWeights_succ (i : ℕ) (hi : i < 30) (j : Fin 5) :
    Function.update (stageWeights i j) (parent i)
      (fun c => stageWeights i j (parent i) c *
        ((∑ d : Fin 3, stageWeights i j (leaf i) d) - stageWeights i j (leaf i) c)) =
      stageWeights (i + 1) j := by
  change Function.update (stageWeights i j) (parent i) _ =
    Function.update (stageWeights i j) (parent i) (nextWeights i j)
  congr 1
  funext c
  exact (table_correct ⟨i, hi⟩ j c).symm

/-- Joining the thirty genuine leaf eliminations. -/
theorem partFun_reduction (j : Fin 5) (n : ℕ) (hn : n ≤ 30) :
    LiElim.partFunOn Li.T (active 0) (stageWeights 0 j) =
      LiElim.partFunOn Li.T (active n) (stageWeights n j) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < 30 := by omega
    rcases leaf_conditions ⟨n, hlt⟩ with ⟨hl, hp, ha, hleaf, hactive⟩
    calc
      _ = LiElim.partFunOn Li.T (active n) (stageWeights n j) := ih (by omega)
      _ = LiElim.partFunOn Li.T ((active n).erase (leaf n))
          (Function.update (stageWeights n j) (parent n)
            (fun c => stageWeights n j (parent n) c *
              ((∑ d : Fin 3, stageWeights n j (leaf n) d) -
                stageWeights n j (leaf n) c))) :=
        LiElim.partFunOn_erase Li.T (active n) (leaf n) (parent n) hl hp ha hleaf
          (stageWeights n j)
      _ = LiElim.partFunOn Li.T (active (n + 1)) (stageWeights (n + 1) j) := by
        rw [stageWeights_succ n hlt j, ← hactive]

/-- Singleton evaluation; the proof follows `LiCompute.partFunOn_zero`
from aadrianvv's PR #35, here over the rationals. -/
lemma partFunOn_zero (w : Fin 31 → Fin 3 → ℚ) :
    LiElim.partFunOn Li.T ({0} : Finset (Fin 31)) w = w 0 0 + w 0 1 + w 0 2 := by
  classical
  let e0 : {v // v ∈ ({0} : Finset (Fin 31))} := ⟨0, Finset.mem_singleton_self 0⟩
  have e0_unique : ∀ a : {v // v ∈ ({0} : Finset (Fin 31))}, a = e0 := by
    intro a
    exact Subtype.ext (Finset.mem_singleton.mp a.2)
  have hproper : ∀ κ : {v // v ∈ ({0} : Finset (Fin 31))} → Fin 3,
      (∀ u v : {v // v ∈ ({0} : Finset (Fin 31))}, Li.T.Adj u v → κ u ≠ κ v) := by
    intro κ u v huv
    have hu : (u : Fin 31) = 0 := Finset.mem_singleton.mp u.2
    have hv : (v : Fin 31) = 0 := Finset.mem_singleton.mp v.2
    rw [hu, hv] at huv
    exact (Li.T.loopless.irrefl 0 huv).elim
  let ee : ({v // v ∈ ({0} : Finset (Fin 31))} → Fin 3) ≃ Fin 3 :=
    { toFun := fun κ => κ e0
      invFun := fun i => fun _ => i
      left_inv := fun κ => by
        funext a
        rw [e0_unique a]
      right_inv := fun i => rfl }
  rw [LiElim.partFunOn]
  trans ∑ κ : {v // v ∈ ({0} : Finset (Fin 31))} → Fin 3, w 0 (κ e0)
  · apply Finset.sum_congr rfl
    intro κ _
    rw [ite_eq_left (hproper κ)]
    have hattach : ({0} : Finset (Fin 31)).attach = {e0} := by
      ext a
      simp only [Finset.mem_attach, Finset.mem_singleton, true_iff]
      exact e0_unique a
    rw [hattach, Finset.prod_singleton]
  · rw [Fintype.sum_equiv ee _ _ ?_]
    · rw [Fin.sum_univ_three]
    · intro κ
      rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem root_weights (j : Fin 5) :
    stageWeights 30 j 0 = nextWeights 29 j := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The five final root sums. -/
theorem root_values : ∀ j : Fin 5,
    stageWeights 30 j 0 0 + stageWeights 30 j 0 1 + stageWeights 30 j 0 2 = values j := by
  intro j
  simp only [root_weights]
  fin_cases j <;> norm_num [nextWeights, updateTable, values]

/-- The full partition functions, obtained from the proved elimination chain. -/
theorem partFun_values (j : Fin 5) :
    LiElim.partFunOn Li.T Finset.univ (fun _ => colorWeights j) = values j := by
  have h := partFun_reduction j 30 (by decide)
  rw [active_zero, active_thirty, partFunOn_zero] at h
  change LiElim.partFunOn Li.T Finset.univ (fun _ => colorWeights j) = _ at h
  exact h.trans (root_values j)

/-- Exact evaluation of the actual three-variable chromatic polynomial. -/
theorem eval_chromPoly (j : Fin 5) :
    MvPolynomial.aeval (colorWeights j) (Li.chromPoly Li.T) = values j := by
  have hbridge : MvPolynomial.aeval (colorWeights j) (Li.chromPoly Li.T) =
      LiElim.partFunOn Li.T Finset.univ (fun _ => colorWeights j) := by
    rw [Li.aeval_chromPoly, Finset.sum_filter, ← LiBridge.partFunOn_univ]
  exact hbridge.trans (partFun_values j)

end LiEvaluation
