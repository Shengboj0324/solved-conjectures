import Conjectures.DukesRevstackCutCertificate
import Conjectures.DukesRevstackFiniteRows024To031

/-! Dyadic separators for every transition from orders 16 through 23 to their successors. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

private def cuts016 : Array Cut := #[
  (-196608, 1), (-98304, 1), (-49152, 1), (-733111814841, 1073741824), (-2124410495529, 4294967296),
  (-164948171139, 2147483648), (-263862221625, 4294967296), (-11544403647, 536870912),
  (-259961697, 16777216), (-9448047, 1048576), (-215613, 32768), (-15717, 4096), (-1485, 512), (-561, 256),
  (-111, 64), (-131, 128), (-225, 256), (-79, 128), (-127, 256), (-49, 128), (-73, 256), (-161, 1024),
  (-497, 4096), (-497, 8192), (-1675, 32768), (-591, 32768), (-473, 32768), (-123, 65536), (-373, 262144),
  (-1, 32768), (-1, 65536), (0, 1)]

private theorem old016_000 : entriesFrom (oldBracket p016 cuts016) 0 8 := by
  decide +kernel

private theorem old016_008 : entriesFrom (oldBracket p016 cuts016) 8 7 := by
  decide +kernel

private theorem new016_000 : entriesFrom (newBracket p017 cuts016) 0 8 := by
  decide +kernel

private theorem new016_008 : entriesFrom (newBracket p017 cuts016) 8 8 := by
  decide +kernel

theorem literal016 : literalInterlaces 16 := by
  apply literal_interlacing_of_certificate 16 (by decide) p016 p017 cuts016 p016_eq p017_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 7) old016_000 old016_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 8) new016_000 new016_008)⟩

private def cuts017 : Array Cut := #[
  (-393216, 1), (-196608, 1), (-98304, 1), (-284925309801, 268435456), (-733111814841, 1073741824),
  (-1768213907425, 17179869184), (-164948171139, 2147483648), (-910348825857, 34359738368),
  (-11544403647, 536870912), (-713467953, 67108864), (-9448047, 1048576), (-341349, 65536), (-15717, 4096),
  (-1485, 512), (-561, 256), (-353, 256), (-131, 128), (-225, 256), (-79, 128), (-127, 256), (-49, 128),
  (-73, 256), (-453, 2048), (-497, 4096), (-1491, 16384), (-1675, 32768), (-1133, 32768), (-2961, 262144),
  (-5099, 524288), (-373, 262144), (-1127, 1048576), (-1, 65536), (-1, 131072), (0, 1)]

private theorem old017_000 : entriesFrom (oldBracket p017 cuts017) 0 8 := by
  decide +kernel

private theorem old017_008 : entriesFrom (oldBracket p017 cuts017) 8 8 := by
  decide +kernel

private theorem new017_000 : entriesFrom (newBracket p018 cuts017) 0 8 := by
  decide +kernel

private theorem new017_008 : entriesFrom (newBracket p018 cuts017) 8 8 := by
  decide +kernel

private theorem new017_016 : entriesFrom (newBracket p018 cuts017) 16 1 := by
  decide +kernel

theorem literal017 : literalInterlaces 17 := by
  apply literal_interlacing_of_certificate 17 (by decide) p017 p018 cuts017 p017_eq p018_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 8) old017_000 old017_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 9) new017_000 (entriesFrom_join (s := 8) (n := 8) (m := 1) new017_008 new017_016))⟩

private def cuts018 : Array Cut := #[
  (-786432, 1), (-393216, 1), (-196608, 1), (-1955431044105, 1073741824), (-284925309801, 268435456),
  (-597703088263, 4294967296), (-1768213907425, 17179869184), (-1342554303949, 34359738368),
  (-910348825857, 34359738368), (-28667634519, 2147483648), (-713467953, 67108864), (-25832799, 4194304),
  (-341349, 65536), (-27597, 8192), (-1485, 512), (-457, 256), (-353, 256), (-131, 128), (-225, 256),
  (-79, 128), (-127, 256), (-49, 128), (-73, 256), (-453, 2048), (-1403, 8192), (-1491, 16384),
  (-4657, 65536), (-1133, 32768), (-30153, 1048576), (-5099, 524288), (-16043, 2097152), (-1127, 1048576),
  (-1143, 2097152), (-1, 131072), (-1, 262144), (0, 1)]

private theorem old018_000 : entriesFrom (oldBracket p018 cuts018) 0 8 := by
  decide +kernel

private theorem old018_008 : entriesFrom (oldBracket p018 cuts018) 8 8 := by
  decide +kernel

private theorem old018_016 : entriesFrom (oldBracket p018 cuts018) 16 1 := by
  decide +kernel

private theorem new018_000 : entriesFrom (newBracket p019 cuts018) 0 8 := by
  decide +kernel

private theorem new018_008 : entriesFrom (newBracket p019 cuts018) 8 8 := by
  decide +kernel

private theorem new018_016 : entriesFrom (newBracket p019 cuts018) 16 2 := by
  decide +kernel

theorem literal018 : literalInterlaces 18 := by
  apply literal_interlacing_of_certificate 18 (by decide) p018 p019 cuts018 p018_eq p019_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 9) old018_000 (entriesFrom_join (s := 8) (n := 8) (m := 1) old018_008 old018_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 10) new018_000 (entriesFrom_join (s := 8) (n := 8) (m := 2) new018_008 new018_016))⟩

private def cuts019 : Array Cut := #[
  (-1572864, 1), (-786432, 1), (-393216, 1), (-693106590605, 268435456), (-1955431044105, 1073741824),
  (-1690543910095, 8589934592), (-597703088263, 4294967296), (-404197123203, 8589934592),
  (-1342554303949, 34359738368), (-142899705173, 8589934592), (-28667634519, 2147483648),
  (-1126792737, 134217728), (-25832799, 4194304), (-562125, 131072), (-27597, 8192), (-2399, 1024),
  (-457, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512), (-127, 256), (-49, 128), (-73, 256),
  (-453, 2048), (-1403, 8192), (-4297, 32768), (-4657, 65536), (-16237, 262144), (-30153, 1048576),
  (-100657, 4194304), (-16043, 2097152), (-18297, 4194304), (-1143, 2097152), (-3445, 8388608), (-1, 262144),
  (-1, 524288), (0, 1)]

private theorem old019_000 : entriesFrom (oldBracket p019 cuts019) 0 8 := by
  decide +kernel

private theorem old019_008 : entriesFrom (oldBracket p019 cuts019) 8 8 := by
  decide +kernel

private theorem old019_016 : entriesFrom (oldBracket p019 cuts019) 16 2 := by
  decide +kernel

private theorem new019_000 : entriesFrom (newBracket p020 cuts019) 0 8 := by
  decide +kernel

private theorem new019_008 : entriesFrom (newBracket p020 cuts019) 8 8 := by
  decide +kernel

private theorem new019_016 : entriesFrom (newBracket p020 cuts019) 16 3 := by
  decide +kernel

theorem literal019 : literalInterlaces 19 := by
  apply literal_interlacing_of_certificate 19 (by decide) p019 p020 cuts019 p019_eq p020_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 10) old019_000 (entriesFrom_join (s := 8) (n := 8) (m := 2) old019_008 old019_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 11) new019_000 (entriesFrom_join (s := 8) (n := 8) (m := 3) new019_008 new019_016))⟩

private def cuts020 : Array Cut := #[
  (-3145728, 1), (-1572864, 1), (-786432, 1), (-1102716003401, 268435456), (-693106590605, 268435456),
  (-1281300218883, 4294967296), (-1690543910095, 8589934592), (-1006196509737, 17179869184),
  (-404197123203, 8589934592), (-382168845753, 17179869184), (-142899705173, 8589934592),
  (-82753685895, 8589934592), (-1126792737, 134217728), (-43820799, 8388608), (-562125, 131072),
  (-46789, 16384), (-2399, 1024), (-457, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512),
  (-637, 1024), (-49, 128), (-171, 512), (-453, 2048), (-3215, 16384), (-4297, 32768), (-13251, 131072),
  (-16237, 262144), (-95101, 2097152), (-100657, 4194304), (-132743, 8388608), (-18297, 4194304),
  (-57177, 16777216), (-3445, 8388608), (-10367, 33554432), (-1, 524288), (-1, 1048576), (0, 1)]

private theorem old020_000 : entriesFrom (oldBracket p020 cuts020) 0 8 := by
  decide +kernel

private theorem old020_008 : entriesFrom (oldBracket p020 cuts020) 8 8 := by
  decide +kernel

private theorem old020_016 : entriesFrom (oldBracket p020 cuts020) 16 3 := by
  decide +kernel

private theorem new020_000 : entriesFrom (newBracket p021 cuts020) 0 8 := by
  decide +kernel

private theorem new020_008 : entriesFrom (newBracket p021 cuts020) 8 8 := by
  decide +kernel

private theorem new020_016 : entriesFrom (newBracket p021 cuts020) 16 4 := by
  decide +kernel

theorem literal020 : literalInterlaces 20 := by
  apply literal_interlacing_of_certificate 20 (by decide) p020 p021 cuts020 p020_eq p021_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 11) old020_000 (entriesFrom_join (s := 8) (n := 8) (m := 3) old020_008 old020_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 12) new020_000 (entriesFrom_join (s := 8) (n := 8) (m := 4) new020_008 new020_016))⟩

private def cuts021 : Array Cut := #[
  (-6291456, 1), (-3145728, 1), (-1572864, 1), (-1512879121623, 268435456), (-1102716003401, 268435456),
  (-1587812882345, 4294967296), (-1281300218883, 4294967296), (-162882240443, 2147483648),
  (-1006196509737, 17179869184), (-1954900783665, 68719476736), (-382168845753, 17179869184),
  (-195580381429, 17179869184), (-82753685895, 8589934592), (-3230191089, 536870912), (-43820799, 8388608),
  (-936437, 262144), (-46789, 16384), (-2399, 1024), (-457, 256), (-353, 256), (-131, 128), (-225, 256),
  (-383, 512), (-637, 1024), (-1029, 2048), (-171, 512), (-1137, 4096), (-3215, 16384), (-10727, 65536),
  (-13251, 131072), (-42739, 524288), (-95101, 2097152), (-290859, 8388608), (-132743, 8388608),
  (-434823, 33554432), (-57177, 16777216), (-178421, 67108864), (-10367, 33554432), (-10431, 67108864),
  (-1, 1048576), (-1, 2097152), (0, 1)]

private theorem old021_000 : entriesFrom (oldBracket p021 cuts021) 0 8 := by
  decide +kernel

private theorem old021_008 : entriesFrom (oldBracket p021 cuts021) 8 8 := by
  decide +kernel

private theorem old021_016 : entriesFrom (oldBracket p021 cuts021) 16 4 := by
  decide +kernel

private theorem new021_000 : entriesFrom (newBracket p022 cuts021) 0 8 := by
  decide +kernel

private theorem new021_008 : entriesFrom (newBracket p022 cuts021) 8 8 := by
  decide +kernel

private theorem new021_016 : entriesFrom (newBracket p022 cuts021) 16 5 := by
  decide +kernel

theorem literal021 : literalInterlaces 21 := by
  apply literal_interlacing_of_certificate 21 (by decide) p021 p022 cuts021 p021_eq p022_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 12) old021_000 (entriesFrom_join (s := 8) (n := 8) (m := 4) old021_008 old021_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 13) new021_000 (entriesFrom_join (s := 8) (n := 8) (m := 5) new021_008 new021_016))⟩

private def cuts022 : Array Cut := #[
  (-12582912, 1), (-6291456, 1), (-3145728, 1), (-583639500105, 67108864), (-1512879121623, 268435456),
  (-130596983217, 268435456), (-1587812882345, 4294967296), (-890412896271, 8589934592),
  (-162882240443, 2147483648), (-4323508673, 134217728), (-1954900783665, 68719476736),
  (-121113748755, 8589934592), (-195580381429, 17179869184), (-134436743319, 17179869184),
  (-3230191089, 536870912), (-73786783, 16777216), (-936437, 262144), (-46789, 16384), (-2399, 1024),
  (-457, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512), (-637, 1024), (-1713, 4096),
  (-3081, 8192), (-1137, 4096), (-7763, 32768), (-10727, 65536), (-34705, 262144), (-42739, 524288),
  (-607969, 8388608), (-290859, 8388608), (-125665, 4194304), (-434823, 33554432), (-1418823, 134217728),
  (-178421, 67108864), (-555997, 268435456), (-10431, 67108864), (-31357, 268435456), (-1, 2097152),
  (-1, 4194304), (0, 1)]

private theorem old022_000 : entriesFrom (oldBracket p022 cuts022) 0 8 := by
  decide +kernel

private theorem old022_008 : entriesFrom (oldBracket p022 cuts022) 8 8 := by
  decide +kernel

private theorem old022_016 : entriesFrom (oldBracket p022 cuts022) 16 5 := by
  decide +kernel

private theorem new022_000 : entriesFrom (newBracket p023 cuts022) 0 8 := by
  decide +kernel

private theorem new022_008 : entriesFrom (newBracket p023 cuts022) 8 8 := by
  decide +kernel

private theorem new022_016 : entriesFrom (newBracket p023 cuts022) 16 6 := by
  decide +kernel

theorem literal022 : literalInterlaces 22 := by
  apply literal_interlacing_of_certificate 22 (by decide) p022 p023 cuts022 p022_eq p023_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 13) old022_000 (entriesFrom_join (s := 8) (n := 8) (m := 5) old022_008 old022_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 14) new022_000 (entriesFrom_join (s := 8) (n := 8) (m := 6) new022_008 new022_016))⟩

private def cuts023 : Array Cut := #[
  (-25165824, 1), (-12582912, 1), (-6291456, 1), (-1989632879245, 134217728), (-583639500105, 67108864),
  (-695173200169, 1073741824), (-130596983217, 268435456), (-1176064504823, 8589934592),
  (-890412896271, 8589934592), (-370410656747, 8589934592), (-4323508673, 134217728),
  (-607703844223, 34359738368), (-121113748755, 8589934592), (-82504281187, 8589934592),
  (-134436743319, 17179869184), (-5591368145, 1073741824), (-73786783, 16777216), (-1685061, 524288),
  (-46789, 16384), (-4227, 2048), (-457, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512),
  (-637, 1024), (-4261, 8192), (-3081, 8192), (-5355, 16384), (-7763, 32768), (-26253, 131072),
  (-34705, 262144), (-112149, 1048576), (-607969, 8388608), (-224707, 4194304), (-125665, 4194304),
  (-3450783, 134217728), (-1418823, 134217728), (-4613311, 536870912), (-555997, 268435456),
  (-1709715, 1073741824), (-31357, 268435456), (-94199, 1073741824), (-1, 4194304), (-1, 8388608), (0, 1)]

private theorem old023_000 : entriesFrom (oldBracket p023 cuts023) 0 8 := by
  decide +kernel

private theorem old023_008 : entriesFrom (oldBracket p023 cuts023) 8 8 := by
  decide +kernel

private theorem old023_016 : entriesFrom (oldBracket p023 cuts023) 16 6 := by
  decide +kernel

private theorem new023_000 : entriesFrom (newBracket p024 cuts023) 0 8 := by
  decide +kernel

private theorem new023_008 : entriesFrom (newBracket p024 cuts023) 8 8 := by
  decide +kernel

private theorem new023_016 : entriesFrom (newBracket p024 cuts023) 16 7 := by
  decide +kernel

theorem literal023 : literalInterlaces 23 := by
  apply literal_interlacing_of_certificate 23 (by decide) p023 p024 cuts023 p023_eq p024_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 14) old023_000 (entriesFrom_join (s := 8) (n := 8) (m := 6) old023_008 old023_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 15) new023_000 (entriesFrom_join (s := 8) (n := 8) (m := 7) new023_008 new023_016))⟩

end DukesRevstack.FiniteData
