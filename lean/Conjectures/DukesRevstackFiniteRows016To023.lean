import Conjectures.DukesRevstackFiniteRows008To015

/-! Exact Eulerian and reduced revstack coefficient rows at orders 16 through 23. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

def e016 : Array ℤ := #[
  1, 65519, 41932745, 3572085255, 85383238549, 782115518299, 3207483178157, 6382798925475, 6382798925475,
  3207483178157, 782115518299, 85383238549, 3572085255, 41932745, 65519, 1, 0]

theorem e016_eq : e016 = eulerRows 16 := calc
  e016 = nextEulerRow 15 e015 := by decide +kernel
  _ = eulerRows 16 := congrArg (nextEulerRow 15) e015_eq

def p016 : List ℤ := [
  1, 65518, 41932378, 3572050131, 85382411177, 782107917494, 3207452031170, 6382736929731, 6382736929731,
  3207452031170, 782107917494, 85382411177, 3572050131, 41932378, 65518, 1]

private abbrev entry016 (i : ℕ) : Prop :=
  p016[i]?.getD 0=reducedEntry e016 e007 e008 i

private theorem cf016_000 : entriesFrom entry016 0 8 := by
  decide +kernel

private theorem cf016_008 : entriesFrom entry016 8 8 := by
  decide +kernel

theorem p016_eq : p016 = reducedRow 16 := calc
  p016 = combineRows 16 e016 e007 e008 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 8) cf016_000 cf016_008)
  _ = reducedRow 16 := by rw [e016_eq,e007_eq,e008_eq]; rfl

def e017 : Array ℤ := #[
  1, 131054, 126781020, 14875399450, 473353301060, 5717291972382, 31055652948388, 83137223185370,
  114890380658550, 83137223185370, 31055652948388, 5717291972382, 473353301060, 14875399450, 126781020,
  131054, 1, 0]

theorem e017_eq : e017 = eulerRows 17 := calc
  e017 = nextEulerRow 16 e016 := by decide +kernel
  _ = eulerRows 17 := congrArg (nextEulerRow 16) e016_eq

def p017 : List ℤ := [
  1, 131053, 126780526, 14875329855, 473351149080, 5717265795509, 31055511119282, 83136843006239,
  114889855770510, 83136843006239, 31055511119282, 5717265795509, 473351149080, 14875329855, 126780526,
  131053, 1]

private abbrev entry017 (i : ℕ) : Prop :=
  p017[i]?.getD 0=reducedEntry e017 e008 e008 i

private theorem cf017_000 : entriesFrom entry017 0 8 := by
  decide +kernel

private theorem cf017_008 : entriesFrom entry017 8 8 := by
  decide +kernel

private theorem cf017_016 : entriesFrom entry017 16 1 := by
  decide +kernel

theorem p017_eq : p017 = reducedRow 17 := calc
  p017 = combineRows 17 e017 e008 e008 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 9) cf017_000 (entriesFrom_join (s := 8) (n := 8) (m := 1) cf017_008 cf017_016))
  _ = reducedRow 17 := by rw [e017_eq,e008_eq]; rfl

def e018 : Array ℤ := #[
  1, 262125, 382439924, 61403313100, 2575022097600, 40457344748072, 285997074307300, 1006709967915228,
  1865385657780650, 1865385657780650, 1006709967915228, 285997074307300, 40457344748072, 2575022097600,
  61403313100, 382439924, 262125, 1, 0]

theorem e018_eq : e018 = eulerRows 18 := calc
  e018 = nextEulerRow 17 e017 := by decide +kernel
  _ = eulerRows 18 := congrArg (nextEulerRow 17) e017_eq

def p018 : List ℤ := [
  1, 262124, 382439175, 61403170205, 2575016230485, 40457252229583, 285996420844191, 1006707667138621,
  1865381394888815, 1865381394888815, 1006707667138621, 285996420844191, 40457252229583, 2575016230485,
  61403170205, 382439175, 262124, 1]

private abbrev entry018 (i : ℕ) : Prop :=
  p018[i]?.getD 0=reducedEntry e018 e008 e009 i

private theorem cf018_000 : entriesFrom entry018 0 8 := by
  decide +kernel

private theorem cf018_008 : entriesFrom entry018 8 8 := by
  decide +kernel

private theorem cf018_016 : entriesFrom entry018 16 2 := by
  decide +kernel

theorem p018_eq : p018 = reducedRow 18 := calc
  p018 = combineRows 18 e018 e008 e009 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 10) cf018_000 (entriesFrom_join (s := 8) (n := 8) (m := 2) cf018_008 cf018_016))
  _ = reducedRow 18 := by rw [e018_eq,e008_eq,e009_eq]; rfl

def e019 : Array ℤ := #[
  1, 524268, 1151775897, 251732291184, 13796160184500, 278794377854832, 2527925001876036, 11485644635009424,
  27862280567093358, 37307713155613000, 27862280567093358, 11485644635009424, 2527925001876036,
  278794377854832, 13796160184500, 251732291184, 1151775897, 524268, 1, 0]

theorem e019_eq : e019 = eulerRows 19 := calc
  e019 = nextEulerRow 18 e018 := by decide +kernel
  _ = eulerRows 19 := congrArg (nextEulerRow 18) e018_eq

def p019 : List ℤ := [
  1, 524267, 1151774893, 251732009964, 13796145341600, 278794075561852, 2527922267040264, 11485632197907476,
  27862250412044458, 37307672762528050, 27862250412044458, 11485632197907476, 2527922267040264,
  278794075561852, 13796145341600, 251732009964, 1151774893, 524267, 1]

private abbrev entry019 (i : ℕ) : Prop :=
  p019[i]?.getD 0=reducedEntry e019 e009 e009 i

private theorem cf019_000 : entriesFrom entry019 0 8 := by
  decide +kernel

private theorem cf019_008 : entriesFrom entry019 8 8 := by
  decide +kernel

private theorem cf019_016 : entriesFrom entry019 16 3 := by
  decide +kernel

theorem p019_eq : p019 = reducedRow 19 := calc
  p019 = combineRows 19 e019 e009 e009 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 11) cf019_000 (entriesFrom_join (s := 8) (n := 8) (m := 3) cf019_008 cf019_016))
  _ = reducedRow 19 := by rw [e019_eq,e009_eq]; rfl

def e020 : Array ℤ := #[
  1, 1048555, 3464764515, 1026509354985, 73008517581444, 1879708669896492, 21598596303099900,
  124748182104463860, 388588260723953310, 679562217794156938, 679562217794156938, 388588260723953310,
  124748182104463860, 21598596303099900, 1879708669896492, 73008517581444, 1026509354985, 3464764515,
  1048555, 1, 0]

theorem e020_eq : e020 = eulerRows 20 := calc
  e020 = nextEulerRow 19 e019 := by decide +kernel
  _ = eulerRows 20 := congrArg (nextEulerRow 19) e019_eq

def p020 : List ℤ := [
  1, 1048554, 3464763000, 1026508784011, 73008478224434, 1879707651695802, 21598584615123838,
  124748114579623550, 388588050403621572, 679561849975963238, 679561849975963238, 388588050403621572,
  124748114579623550, 21598584615123838, 1879707651695802, 73008478224434, 1026508784011, 3464763000,
  1048554, 1]

private abbrev entry020 (i : ℕ) : Prop :=
  p020[i]?.getD 0=reducedEntry e020 e009 e010 i

private theorem cf020_000 : entriesFrom entry020 0 8 := by
  decide +kernel

private theorem cf020_008 : entriesFrom entry020 8 8 := by
  decide +kernel

private theorem cf020_016 : entriesFrom entry020 16 4 := by
  decide +kernel

theorem p020_eq : p020 = reducedRow 20 := calc
  p020 = combineRows 20 e020 e009 e010 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 12) cf020_000 (entriesFrom_join (s := 8) (n := 8) (m := 4) cf020_008 cf020_016))
  _ = reducedRow 20 := by rw [e020_eq,e009_eq,e010_eq]; rfl

def e021 : Array ℤ := #[
  1, 2097130, 10414216090, 4168403181210, 382493246941965, 12446388300682056, 179385804170146680,
  1300365805079109480, 5119020713873609970, 11458681306629009100, 14950368791471452636, 11458681306629009100,
  5119020713873609970, 1300365805079109480, 179385804170146680, 12446388300682056, 382493246941965,
  4168403181210, 10414216090, 2097130, 1, 0]

theorem e021_eq : e021 = eulerRows 21 := calc
  e021 = nextEulerRow 20 e020 := by decide +kernel
  _ = eulerRows 21 := congrArg (nextEulerRow 20) e020_eq

def p021 : List ℤ := [
  1, 2097129, 10414214064, 4168402059361, 382493149107741, 12446385087176756, 179385757959978208,
  1300365469848994308, 5119019394651308642, 11458678353026391422, 14950364938437344736, 11458678353026391422,
  5119019394651308642, 1300365469848994308, 179385757959978208, 12446385087176756, 382493149107741,
  4168402059361, 10414214064, 2097129, 1]

private abbrev entry021 (i : ℕ) : Prop :=
  p021[i]?.getD 0=reducedEntry e021 e010 e010 i

private theorem cf021_000 : entriesFrom entry021 0 8 := by
  decide +kernel

private theorem cf021_008 : entriesFrom entry021 8 8 := by
  decide +kernel

private theorem cf021_016 : entriesFrom entry021 16 5 := by
  decide +kernel

theorem p021_eq : p021 = reducedRow 21 := calc
  p021 = combineRows 21 e021 e010 e010 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 13) cf021_000 (entriesFrom_join (s := 8) (n := 8) (m := 5) cf021_008 cf021_016))
  _ = reducedRow 21 := by rw [e021_eq,e010_eq]; rfl

def e022 : Array ℤ := #[
  1, 4194281, 31284590870, 16871482830550, 1987497491971605, 81180715002105741, 1454842842001939656,
  13093713503185076040, 64276307695970022450, 181134082346647020610, 301958232385734088196,
  301958232385734088196, 181134082346647020610, 64276307695970022450, 13093713503185076040,
  1454842842001939656, 81180715002105741, 1987497491971605, 16871482830550, 31284590870, 4194281, 1, 0]

theorem e022_eq : e022 = eulerRows 22 := calc
  e022 = nextEulerRow 21 e021 := by decide +kernel
  _ = eulerRows 22 := congrArg (nextEulerRow 21) e021_eq

def p022 : List ℤ := [
  1, 4194280, 31284587821, 16871480567605, 1987497237289404, 81180704529998937, 1454842654558307604,
  13093711815688351812, 64276299412858860270, 181134059003688973588, 301958193472430788678,
  301958193472430788678, 181134059003688973588, 64276299412858860270, 13093711815688351812,
  1454842654558307604, 81180704529998937, 1987497237289404, 16871480567605, 31284587821, 4194280, 1]

private abbrev entry022 (i : ℕ) : Prop :=
  p022[i]?.getD 0=reducedEntry e022 e010 e011 i

private theorem cf022_000 : entriesFrom entry022 0 8 := by
  decide +kernel

private theorem cf022_008 : entriesFrom entry022 8 8 := by
  decide +kernel

private theorem cf022_016 : entriesFrom entry022 16 6 := by
  decide +kernel

theorem p022_eq : p022 = reducedRow 22 := calc
  p022 = combineRows 22 e022 e010 e011 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 14) cf022_000 (entriesFrom_join (s := 8) (n := 8) (m := 6) cf022_008 cf022_016))
  _ = reducedRow 22 := by rw [e022_eq,e010_eq,e011_eq]; rfl

def e023 : Array ℤ := #[
  1, 8388584, 93941852511, 68111623139600, 10258045633638475, 522859244868123336, 11563972049049375189,
  128027193497511642816, 774892471811506342650, 2711209131210050520400, 5676283626749486238086,
  7246997577257618116704, 5676283626749486238086, 2711209131210050520400, 774892471811506342650,
  128027193497511642816, 11563972049049375189, 522859244868123336, 10258045633638475, 68111623139600,
  93941852511, 8388584, 1, 0]

theorem e023_eq : e023 = eulerRows 23 := calc
  e023 = nextEulerRow 22 e022 := by decide +kernel
  _ = eulerRows 23 := congrArg (nextEulerRow 22) e022_eq

def p023 : List ℤ := [
  1, 8388583, 93941848439, 68111618689030, 10258045007693635, 522859212577990203, 11563971336696730773,
  128027185605310649352, 774892424056009568250, 2711208964101036767710, 5676283276911523240630,
  7246997130586591266788, 5676283276911523240630, 2711208964101036767710, 774892424056009568250,
  128027185605310649352, 11563971336696730773, 522859212577990203, 10258045007693635, 68111618689030,
  93941848439, 8388583, 1]

private abbrev entry023 (i : ℕ) : Prop :=
  p023[i]?.getD 0=reducedEntry e023 e011 e011 i

private theorem cf023_000 : entriesFrom entry023 0 8 := by
  decide +kernel

private theorem cf023_008 : entriesFrom entry023 8 8 := by
  decide +kernel

private theorem cf023_016 : entriesFrom entry023 16 7 := by
  decide +kernel

theorem p023_eq : p023 = reducedRow 23 := calc
  p023 = combineRows 23 e023 e011 e011 := by
    apply combineRows_eq_of_entries (by decide)
    exact entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 15) cf023_000 (entriesFrom_join (s := 8) (n := 8) (m := 7) cf023_008 cf023_016))
  _ = reducedRow 23 := by rw [e023_eq,e011_eq]; rfl

end DukesRevstack.FiniteData
