import Conjectures.DukesRevstackCutCertificate
import Conjectures.DukesRevstackFiniteRows032To039

/-! Dyadic separators for every transition from orders 24 through 31 to their successors. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

private def cuts024 : Array Cut := #[
  (-50331648, 1), (-25165824, 1), (-12582912, 1), (-1406161799609, 67108864), (-1989632879245, 134217728),
  (-241317196929, 268435456), (-695173200169, 1073741824), (-387861093647, 2147483648),
  (-1176064504823, 8589934592), (-870821873375, 17179869184), (-370410656747, 8589934592),
  (-732482438239, 34359738368), (-607703844223, 34359738368), (-92156648079, 8589934592),
  (-82504281187, 8589934592), (-223898633639, 34359738368), (-5591368145, 1073741824),
  (-127708735, 33554432), (-1685061, 524288), (-80605, 32768), (-4227, 2048), (-405, 256), (-353, 256),
  (-131, 128), (-225, 256), (-383, 512), (-637, 1024), (-4261, 8192), (-3081, 8192), (-5355, 16384),
  (-18473, 65536), (-26253, 131072), (-87211, 524288), (-112149, 1048576), (-1505161, 16777216),
  (-224707, 4194304), (-399893, 8388608), (-3450783, 134217728), (-2434803, 134217728),
  (-4613311, 536870912), (-14951927, 2147483648), (-1709715, 1073741824), (-5254573, 4294967296),
  (-94199, 1073741824), (-94455, 2147483648), (-1, 8388608), (-1, 16777216), (0, 1)]

private theorem old024_000 : entriesFrom (oldBracket p024 cuts024) 0 8 := by
  decide +kernel

private theorem old024_008 : entriesFrom (oldBracket p024 cuts024) 8 8 := by
  decide +kernel

private theorem old024_016 : entriesFrom (oldBracket p024 cuts024) 16 7 := by
  decide +kernel

private theorem new024_000 : entriesFrom (newBracket p025 cuts024) 0 8 := by
  decide +kernel

private theorem new024_008 : entriesFrom (newBracket p025 cuts024) 8 8 := by
  decide +kernel

private theorem new024_016 : entriesFrom (newBracket p025 cuts024) 16 8 := by
  decide +kernel

theorem literal024 : literalInterlaces 24 := by
  apply literal_interlacing_of_certificate 24 (by decide) p024 p025 cuts024 p024_eq p025_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 15) old024_000 (entriesFrom_join (s := 8) (n := 8) (m := 7) old024_008 old024_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 16) new024_000 (entriesFrom_join (s := 8) (n := 8) (m := 8) new024_008 new024_016))⟩

private def cuts025 : Array Cut := #[
  (-100663296, 1), (-50331648, 1), (-25165824, 1), (-1114711157779, 33554432), (-1406161799609, 67108864),
  (-1432512357911, 1073741824), (-241317196929, 268435456), (-1802065701261, 8589934592),
  (-387861093647, 2147483648), (-1055985265409, 17179869184), (-870821873375, 17179869184),
  (-459886242713, 17179869184), (-732482438239, 34359738368), (-1713583621171, 137438953472),
  (-92156648079, 8589934592), (-1001713025665, 137438953472), (-223898633639, 34359738368),
  (-9678047665, 2147483648), (-127708735, 33554432), (-2974741, 1048576), (-80605, 32768), (-4227, 2048),
  (-405, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512), (-637, 1024), (-4261, 8192),
  (-3081, 8192), (-5355, 16384), (-18473, 65536), (-63199, 262144), (-87211, 524288), (-286571, 2097152),
  (-1505161, 16777216), (-2403989, 33554432), (-399893, 8388608), (-9849071, 268435456),
  (-2434803, 134217728), (-33830947, 2147483648), (-48275211, 8589934592), (-85017925, 17179869184),
  (-16140515, 17179869184), (-27403253, 34359738368), (-94455, 2147483648), (-283621, 8589934592),
  (-1, 16777216), (-1, 33554432), (0, 1)]

private theorem old025_000 : entriesFrom (oldBracket p025 cuts025) 0 8 := by
  decide +kernel

private theorem old025_008 : entriesFrom (oldBracket p025 cuts025) 8 8 := by
  decide +kernel

private theorem old025_016 : entriesFrom (oldBracket p025 cuts025) 16 8 := by
  decide +kernel

private theorem new025_000 : entriesFrom (newBracket p026 cuts025) 0 8 := by
  decide +kernel

private theorem new025_008 : entriesFrom (newBracket p026 cuts025) 8 8 := by
  decide +kernel

private theorem new025_016 : entriesFrom (newBracket p026 cuts025) 16 8 := by
  decide +kernel

private theorem new025_024 : entriesFrom (newBracket p026 cuts025) 24 1 := by
  decide +kernel

theorem literal025 : literalInterlaces 25 := by
  apply literal_interlacing_of_certificate 25 (by decide) p025 p026 cuts025 p025_eq p026_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 16) old025_000 (entriesFrom_join (s := 8) (n := 8) (m := 8) old025_008 old025_016)),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 17) new025_000 (entriesFrom_join (s := 8) (n := 8) (m := 9) new025_008 (entriesFrom_join (s := 16) (n := 8) (m := 1) new025_016 new025_024)))⟩

private def cuts026 : Array Cut := #[
  (-201326592, 1), (-100663296, 1), (-50331648, 1), (-1526483725637, 33554432), (-1114711157779, 33554432),
  (-2090827246531, 1073741824), (-1432512357911, 1073741824), (-1086035494395, 4294967296),
  (-1802065701261, 8589934592), (-81990512555, 1073741824), (-1055985265409, 17179869184),
  (-1125240300757, 34359738368), (-459886242713, 17179869184), (-2017670154117, 137438953472),
  (-1713583621171, 137438953472), (-154763712183, 17179869184), (-1001713025665, 137438953472),
  (-378747396279, 68719476736), (-9678047665, 2147483648), (-222900447, 67108864), (-2974741, 1048576),
  (-80605, 32768), (-4227, 2048), (-405, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512),
  (-637, 1024), (-4261, 8192), (-3671, 8192), (-5355, 16384), (-18473, 65536), (-63199, 262144),
  (-213609, 1048576), (-286571, 2097152), (-3797729, 33554432), (-2403989, 33554432), (-8811539, 134217728),
  (-9849071, 268435456), (-34416819, 1073741824), (-33830947, 2147483648), (-454246575, 34359738368),
  (-85017925, 17179869184), (-135597145, 34359738368), (-27403253, 34359738368), (-83721039, 137438953472),
  (-283621, 8589934592), (-851375, 34359738368), (-1, 33554432), (-1, 67108864), (0, 1)]

private theorem old026_000 : entriesFrom (oldBracket p026 cuts026) 0 8 := by
  decide +kernel

private theorem old026_008 : entriesFrom (oldBracket p026 cuts026) 8 8 := by
  decide +kernel

private theorem old026_016 : entriesFrom (oldBracket p026 cuts026) 16 8 := by
  decide +kernel

private theorem old026_024 : entriesFrom (oldBracket p026 cuts026) 24 1 := by
  decide +kernel

private theorem new026_000 : entriesFrom (newBracket p027 cuts026) 0 8 := by
  decide +kernel

private theorem new026_008 : entriesFrom (newBracket p027 cuts026) 8 8 := by
  decide +kernel

private theorem new026_016 : entriesFrom (newBracket p027 cuts026) 16 8 := by
  decide +kernel

private theorem new026_024 : entriesFrom (newBracket p027 cuts026) 24 2 := by
  decide +kernel

theorem literal026 : literalInterlaces 26 := by
  apply literal_interlacing_of_certificate 26 (by decide) p026 p027 cuts026 p026_eq p027_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 17) old026_000 (entriesFrom_join (s := 8) (n := 8) (m := 9) old026_008 (entriesFrom_join (s := 16) (n := 8) (m := 1) old026_016 old026_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 18) new026_000 (entriesFrom_join (s := 8) (n := 8) (m := 10) new026_008 (entriesFrom_join (s := 16) (n := 8) (m := 2) new026_016 new026_024)))⟩

private def cuts027 : Array Cut := #[
  (-402653184, 1), (-201326592, 1), (-100663296, 1), (-73449127909, 1048576), (-1526483725637, 33554432),
  (-1307756824847, 536870912), (-2090827246531, 1073741824), (-1376286365473, 4294967296),
  (-1086035494395, 4294967296), (-1598383601085, 17179869184), (-81990512555, 1073741824),
  (-42872589321, 1073741824), (-1125240300757, 34359738368), (-1216512550507, 68719476736),
  (-2017670154117, 137438953472), (-737923329659, 68719476736), (-154763712183, 17179869184),
  (-1759207818223, 274877906944), (-378747396279, 68719476736), (-16810861969, 4294967296),
  (-222900447, 67108864), (-2974741, 1048576), (-80605, 32768), (-7467, 4096), (-405, 256), (-353, 256),
  (-131, 128), (-225, 256), (-383, 512), (-637, 1024), (-4261, 8192), (-3671, 8192), (-12697, 32768),
  (-18473, 65536), (-63199, 262144), (-213609, 1048576), (-713789, 4194304), (-3797729, 33554432),
  (-3100859, 33554432), (-8811539, 134217728), (-27472149, 536870912), (-34416819, 1073741824),
  (-240331861, 8589934592), (-454246575, 34359738368), (-1532775575, 137438953472),
  (-135597145, 34359738368), (-1696073, 536870912), (-83721039, 137438953472), (-255701053, 549755813888),
  (-851375, 34359738368), (-852399, 68719476736), (-1, 67108864), (-1, 134217728), (0, 1)]

private theorem old027_000 : entriesFrom (oldBracket p027 cuts027) 0 8 := by
  decide +kernel

private theorem old027_008 : entriesFrom (oldBracket p027 cuts027) 8 8 := by
  decide +kernel

private theorem old027_016 : entriesFrom (oldBracket p027 cuts027) 16 8 := by
  decide +kernel

private theorem old027_024 : entriesFrom (oldBracket p027 cuts027) 24 2 := by
  decide +kernel

private theorem new027_000 : entriesFrom (newBracket p028 cuts027) 0 8 := by
  decide +kernel

private theorem new027_008 : entriesFrom (newBracket p028 cuts027) 8 8 := by
  decide +kernel

private theorem new027_016 : entriesFrom (newBracket p028 cuts027) 16 8 := by
  decide +kernel

private theorem new027_024 : entriesFrom (newBracket p028 cuts027) 24 3 := by
  decide +kernel

theorem literal027 : literalInterlaces 27 := by
  apply literal_interlacing_of_certificate 27 (by decide) p027 p028 cuts027 p027_eq p028_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 18) old027_000 (entriesFrom_join (s := 8) (n := 8) (m := 10) old027_008 (entriesFrom_join (s := 16) (n := 8) (m := 2) old027_016 old027_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 19) new027_000 (entriesFrom_join (s := 8) (n := 8) (m := 11) new027_008 (entriesFrom_join (s := 16) (n := 8) (m := 3) new027_016 new027_024)))⟩

private def cuts028 : Array Cut := #[
  (-805306368, 1), (-402653184, 1), (-201326592, 1), (-124952871629, 1048576), (-73449127909, 1048576),
  (-417236013967, 134217728), (-1307756824847, 536870912), (-56655477477, 134217728),
  (-1376286365473, 4294967296), (-1941603398147, 17179869184), (-1598383601085, 17179869184),
  (-191049318901, 4294967296), (-42872589321, 1073741824), (-1475004563259, 68719476736),
  (-1216512550507, 68719476736), (-873379203359, 68719476736), (-737923329659, 68719476736),
  (-1938460712399, 274877906944), (-1759207818223, 274877906944), (-647721187783, 137438953472),
  (-16810861969, 4294967296), (-222900447, 67108864), (-2974741, 1048576), (-140341, 65536), (-7467, 4096),
  (-405, 256), (-353, 256), (-131, 128), (-225, 256), (-383, 512), (-637, 1024), (-4261, 8192),
  (-3671, 8192), (-12697, 32768), (-43867, 131072), (-63199, 262144), (-213609, 1048576), (-713789, 4194304),
  (-9508041, 67108864), (-3100859, 33554432), (-21214975, 268435456), (-27472149, 536870912),
  (-199249713, 4294967296), (-240331861, 8589934592), (-3338228907, 137438953472),
  (-1532775575, 137438953472), (-5140715305, 549755813888), (-1696073, 536870912),
  (-1386305103, 549755813888), (-255701053, 549755813888), (-780725159, 2199023255552),
  (-852399, 68719476736), (-2558221, 274877906944), (-1, 134217728), (-1, 268435456), (0, 1)]

private theorem old028_000 : entriesFrom (oldBracket p028 cuts028) 0 8 := by
  decide +kernel

private theorem old028_008 : entriesFrom (oldBracket p028 cuts028) 8 8 := by
  decide +kernel

private theorem old028_016 : entriesFrom (oldBracket p028 cuts028) 16 8 := by
  decide +kernel

private theorem old028_024 : entriesFrom (oldBracket p028 cuts028) 24 3 := by
  decide +kernel

private theorem new028_000 : entriesFrom (newBracket p029 cuts028) 0 8 := by
  decide +kernel

private theorem new028_008 : entriesFrom (newBracket p029 cuts028) 8 8 := by
  decide +kernel

private theorem new028_016 : entriesFrom (newBracket p029 cuts028) 16 8 := by
  decide +kernel

private theorem new028_024 : entriesFrom (newBracket p029 cuts028) 24 4 := by
  decide +kernel

theorem literal028 : literalInterlaces 28 := by
  apply literal_interlacing_of_certificate 28 (by decide) p028 p029 cuts028 p028_eq p029_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 19) old028_000 (entriesFrom_join (s := 8) (n := 8) (m := 11) old028_008 (entriesFrom_join (s := 16) (n := 8) (m := 3) old028_016 old028_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 20) new028_000 (entriesFrom_join (s := 8) (n := 8) (m := 12) new028_008 (entriesFrom_join (s := 16) (n := 8) (m := 4) new028_016 new028_024)))⟩

private def cuts029 : Array Cut := #[
  (-1610612736, 1), (-805306368, 1), (-402653184, 1), (-1411695784871, 8388608), (-124952871629, 1048576),
  (-557614957067, 134217728), (-417236013967, 134217728), (-1176771368367, 2147483648),
  (-56655477477, 134217728), (-596761539029, 4294967296), (-1941603398147, 17179869184),
  (-486371928487, 8589934592), (-191049318901, 4294967296), (-448053712895, 17179869184),
  (-1475004563259, 68719476736), (-479581270073, 34359738368), (-873379203359, 68719476736),
  (-1222538507759, 137438953472), (-1938460712399, 274877906944), (-763662548447, 137438953472),
  (-647721187783, 137438953472), (-31076490577, 8589934592), (-222900447, 67108864), (-5220197, 2097152),
  (-140341, 65536), (-7467, 4096), (-405, 256), (-615, 512), (-131, 128), (-225, 256), (-383, 512),
  (-637, 1024), (-9357, 16384), (-3671, 8192), (-12697, 32768), (-43867, 131072), (-150933, 524288),
  (-213609, 1048576), (-1568225, 8388608), (-9508041, 67108864), (-15709759, 134217728),
  (-21214975, 268435456), (-154761999, 2147483648), (-199249713, 4294967296), (-638831287, 17179869184),
  (-3338228907, 137438953472), (-2435502241, 137438953472), (-5140715305, 549755813888),
  (-17158924667, 2199023255552), (-1386305103, 549755813888), (-2207308181, 1099511627776),
  (-780725159, 2199023255552), (-2369452245, 8796093022208), (-2558221, 274877906944),
  (-7676711, 1099511627776), (-1, 268435456), (-1, 536870912), (0, 1)]

private theorem old029_000 : entriesFrom (oldBracket p029 cuts029) 0 8 := by
  decide +kernel

private theorem old029_008 : entriesFrom (oldBracket p029 cuts029) 8 8 := by
  decide +kernel

private theorem old029_016 : entriesFrom (oldBracket p029 cuts029) 16 8 := by
  decide +kernel

private theorem old029_024 : entriesFrom (oldBracket p029 cuts029) 24 4 := by
  decide +kernel

private theorem new029_000 : entriesFrom (newBracket p030 cuts029) 0 8 := by
  decide +kernel

private theorem new029_008 : entriesFrom (newBracket p030 cuts029) 8 8 := by
  decide +kernel

private theorem new029_016 : entriesFrom (newBracket p030 cuts029) 16 8 := by
  decide +kernel

private theorem new029_024 : entriesFrom (newBracket p030 cuts029) 24 5 := by
  decide +kernel

theorem literal029 : literalInterlaces 29 := by
  apply literal_interlacing_of_certificate 29 (by decide) p029 p030 cuts029 p029_eq p030_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 20) old029_000 (entriesFrom_join (s := 8) (n := 8) (m := 12) old029_008 (entriesFrom_join (s := 16) (n := 8) (m := 4) old029_016 old029_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 21) new029_000 (entriesFrom_join (s := 8) (n := 8) (m := 13) new029_008 (entriesFrom_join (s := 16) (n := 8) (m := 5) new029_016 new029_024)))⟩

private def cuts030 : Array Cut := #[
  (-3221225472, 1), (-1610612736, 1), (-805306368, 1), (-558996213353, 2097152), (-1411695784871, 8388608),
  (-798807966621, 134217728), (-557614957067, 134217728), (-1520459171811, 2147483648),
  (-1176771368367, 2147483648), (-1497576513117, 8589934592), (-596761539029, 4294967296),
  (-2187702599241, 34359738368), (-486371928487, 8589934592), (-2108358414289, 68719476736),
  (-448053712895, 17179869184), (-272030761481, 17179869184), (-479581270073, 34359738368),
  (-1353593482499, 137438953472), (-1222538507759, 137438953472), (-866446452323, 137438953472),
  (-763662548447, 137438953472), (-1144945037015, 274877906944), (-31076490577, 8589934592),
  (-389946751, 134217728), (-5220197, 2097152), (-140341, 65536), (-7467, 4096), (-405, 256), (-615, 512),
  (-131, 128), (-225, 256), (-383, 512), (-1403, 2048), (-9357, 16384), (-16699, 32768), (-12697, 32768),
  (-43867, 131072), (-150933, 524288), (-515475, 2097152), (-1568225, 8388608), (-22053841, 134217728),
  (-15709759, 134217728), (-52634493, 536870912), (-154761999, 2147483648), (-508773711, 8589934592),
  (-638831287, 17179869184), (-18670179795, 549755813888), (-2435502241, 137438953472),
  (-34366742197, 2199023255552), (-57021994413, 8796093022208), (-102430284571, 17592186044416),
  (-2207308181, 1099511627776), (-14024574245, 8796093022208), (-2369452245, 8796093022208),
  (-7190219807, 35184372088832), (-7676711, 1099511627776), (-23034229, 4398046511104), (-1, 536870912),
  (-1, 1073741824), (0, 1)]

private theorem old030_000 : entriesFrom (oldBracket p030 cuts030) 0 8 := by
  decide +kernel

private theorem old030_008 : entriesFrom (oldBracket p030 cuts030) 8 8 := by
  decide +kernel

private theorem old030_016 : entriesFrom (oldBracket p030 cuts030) 16 8 := by
  decide +kernel

private theorem old030_024 : entriesFrom (oldBracket p030 cuts030) 24 5 := by
  decide +kernel

private theorem new030_000 : entriesFrom (newBracket p031 cuts030) 0 8 := by
  decide +kernel

private theorem new030_008 : entriesFrom (newBracket p031 cuts030) 8 8 := by
  decide +kernel

private theorem new030_016 : entriesFrom (newBracket p031 cuts030) 16 8 := by
  decide +kernel

private theorem new030_024 : entriesFrom (newBracket p031 cuts030) 24 6 := by
  decide +kernel

theorem literal030 : literalInterlaces 30 := by
  apply literal_interlacing_of_certificate 30 (by decide) p030 p031 cuts030 p030_eq p031_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 21) old030_000 (entriesFrom_join (s := 8) (n := 8) (m := 13) old030_008 (entriesFrom_join (s := 16) (n := 8) (m := 5) old030_016 old030_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 22) new030_000 (entriesFrom_join (s := 8) (n := 8) (m := 14) new030_008 (entriesFrom_join (s := 16) (n := 8) (m := 6) new030_016 new030_024)))⟩

private def cuts031 : Array Cut := #[
  (-6442450944, 1), (-3221225472, 1), (-1610612736, 1), (-1530172813437, 4194304), (-558996213353, 2097152),
  (-142406317295, 16777216), (-798807966621, 134217728), (-123940339415, 134217728),
  (-1520459171811, 2147483648), (-1898765133161, 8589934592), (-1497576513117, 8589934592),
  (-627750328341, 8589934592), (-2187702599241, 34359738368), (-1277006333845, 34359738368),
  (-2108358414289, 68719476736), (-632072998669, 34359738368), (-272030761481, 17179869184),
  (-1494776381947, 137438953472), (-1353593482499, 137438953472), (-477734733091, 68719476736),
  (-866446452323, 137438953472), (-668067533477, 137438953472), (-1144945037015, 274877906944),
  (-56033082641, 17179869184), (-389946751, 134217728), (-5220197, 2097152), (-140341, 65536), (-7467, 4096),
  (-405, 256), (-615, 512), (-131, 128), (-225, 256), (-383, 512), (-1403, 2048), (-9357, 16384),
  (-16699, 32768), (-7349, 16384), (-43867, 131072), (-150933, 524288), (-515475, 2097152),
  (-3630125, 16777216), (-22053841, 134217728), (-2360225, 16777216), (-52634493, 536870912),
  (-365299971, 4294967296), (-508773711, 8589934592), (-3691473553, 68719476736),
  (-18670179795, 549755813888), (-65752548349, 2199023255552), (-34366742197, 2199023255552),
  (-469422900777, 35184372088832), (-102430284571, 17592186044416), (-342607784609, 70368744177664),
  (-14024574245, 8796093022208), (-11110793745, 8796093022208), (-21816314173, 140737488355328),
  (-36688063291, 281474976710656), (-23034229, 4398046511104), (-23042421, 8796093022208), (-1, 1073741824),
  (-1, 2147483648), (0, 1)]

private theorem old031_000 : entriesFrom (oldBracket p031 cuts031) 0 8 := by
  decide +kernel

private theorem old031_008 : entriesFrom (oldBracket p031 cuts031) 8 8 := by
  decide +kernel

private theorem old031_016 : entriesFrom (oldBracket p031 cuts031) 16 8 := by
  decide +kernel

private theorem old031_024 : entriesFrom (oldBracket p031 cuts031) 24 6 := by
  decide +kernel

private theorem new031_000 : entriesFrom (newBracket p032 cuts031) 0 8 := by
  decide +kernel

private theorem new031_008 : entriesFrom (newBracket p032 cuts031) 8 8 := by
  decide +kernel

private theorem new031_016 : entriesFrom (newBracket p032 cuts031) 16 8 := by
  decide +kernel

private theorem new031_024 : entriesFrom (newBracket p032 cuts031) 24 7 := by
  decide +kernel

theorem literal031 : literalInterlaces 31 := by
  apply literal_interlacing_of_certificate 31 (by decide) p031 p032 cuts031 p031_eq p032_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 22) old031_000 (entriesFrom_join (s := 8) (n := 8) (m := 14) old031_008 (entriesFrom_join (s := 16) (n := 8) (m := 6) old031_016 old031_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 23) new031_000 (entriesFrom_join (s := 8) (n := 8) (m := 15) new031_008 (entriesFrom_join (s := 16) (n := 8) (m := 7) new031_016 new031_024)))⟩

end DukesRevstack.FiniteData
