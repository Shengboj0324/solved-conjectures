import Conjectures.DukesRevstackCutCertificate
import Conjectures.DukesRevstackFiniteRows040To047

/-! Dyadic separators for every transition from orders 32 through 39 to their successors. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

private def cuts032 : Array Cut := #[
  (-12884901888, 1), (-6442450944, 1), (-3221225472, 1), (-588654936399, 1048576), (-1530172813437, 4194304),
  (-704924125103, 67108864), (-142406317295, 16777216), (-580119811061, 536870912),
  (-123940339415, 134217728), (-2160207105291, 8589934592), (-1898765133161, 8589934592),
  (-368239300719, 4294967296), (-627750328341, 8589934592), (-752340200097, 17179869184),
  (-1277006333845, 34359738368), (-184399887697, 8589934592), (-632072998669, 34359738368),
  (-917755618449, 68719476736), (-1494776381947, 137438953472), (-288632868585, 34359738368),
  (-477734733091, 68719476736), (-191814248225, 34359738368), (-668067533477, 137438953472),
  (-2041474359271, 549755813888), (-56033082641, 17179869184), (-724039359, 268435456), (-5220197, 2097152),
  (-259813, 131072), (-7467, 4096), (-1425, 1024), (-615, 512), (-131, 128), (-225, 256), (-383, 512),
  (-1403, 2048), (-9357, 16384), (-16699, 32768), (-7349, 16384), (-102659, 262144), (-150933, 524288),
  (-1119207, 4194304), (-3630125, 16777216), (-51094841, 268435456), (-2360225, 16777216),
  (-128161693, 1073741824), (-365299971, 4294967296), (-2700573537, 34359738368), (-3691473553, 68719476736),
  (-48201968219, 1099511627776), (-65752548349, 2199023255552), (-50059645273, 2199023255552),
  (-469422900777, 35184372088832), (-1613129271473, 140737488355328), (-342607784609, 70368744177664),
  (-1140019947787, 281474976710656), (-11110793745, 8796093022208), (-555134413933, 562949953421312),
  (-36688063291, 281474976710656), (-111538380529, 1125899906842624), (-23042421, 8796093022208),
  (-69135455, 35184372088832), (-1, 2147483648), (-1, 4294967296), (0, 1)]

private theorem old032_000 : entriesFrom (oldBracket p032 cuts032) 0 8 := by
  decide +kernel

private theorem old032_008 : entriesFrom (oldBracket p032 cuts032) 8 8 := by
  decide +kernel

private theorem old032_016 : entriesFrom (oldBracket p032 cuts032) 16 8 := by
  decide +kernel

private theorem old032_024 : entriesFrom (oldBracket p032 cuts032) 24 7 := by
  decide +kernel

private theorem new032_000 : entriesFrom (newBracket p033 cuts032) 0 8 := by
  decide +kernel

private theorem new032_008 : entriesFrom (newBracket p033 cuts032) 8 8 := by
  decide +kernel

private theorem new032_016 : entriesFrom (newBracket p033 cuts032) 16 8 := by
  decide +kernel

private theorem new032_024 : entriesFrom (newBracket p033 cuts032) 24 8 := by
  decide +kernel

theorem literal032 : literalInterlaces 32 := by
  apply literal_interlacing_of_certificate 32 (by decide) p032 p033 cuts032 p032_eq p033_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 23) old032_000 (entriesFrom_join (s := 8) (n := 8) (m := 15) old032_008 (entriesFrom_join (s := 16) (n := 8) (m := 7) old032_016 old032_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 24) new032_000 (entriesFrom_join (s := 8) (n := 8) (m := 16) new032_008 (entriesFrom_join (s := 16) (n := 8) (m := 8) new032_016 new032_024)))⟩

private def cuts033 : Array Cut := #[
  (-25769803776, 1), (-12884901888, 1), (-6442450944, 1), (-794777437961, 1048576), (-588654936399, 1048576),
  (-1781377014111, 134217728), (-704924125103, 67108864), (-1657349914919, 1073741824),
  (-580119811061, 536870912), (-1440851966225, 4294967296), (-2160207105291, 8589934592),
  (-1763528835807, 17179869184), (-368239300719, 4294967296), (-878130314243, 17179869184),
  (-752340200097, 17179869184), (-109056405819, 4294967296), (-184399887697, 8589934592),
  (-1004353213171, 68719476736), (-917755618449, 68719476736), (-82790870509, 8589934592),
  (-288632868585, 34359738368), (-861363229541, 137438953472), (-191814248225, 34359738368),
  (-1178436123295, 274877906944), (-2041474359271, 549755813888), (-102371601617, 34359738368),
  (-724039359, 268435456), (-9377205, 4194304), (-259813, 131072), (-13167, 8192), (-1425, 1024),
  (-615, 512), (-131, 128), (-225, 256), (-833, 1024), (-1403, 2048), (-9357, 16384), (-16699, 32768),
  (-7349, 16384), (-102659, 262144), (-356251, 1048576), (-1119207, 4194304), (-8106953, 33554432),
  (-51094841, 268435456), (-88858441, 536870912), (-128161693, 1073741824), (-877946743, 8589934592),
  (-2700573537, 34359738368), (-9092620627, 137438953472), (-48201968219, 1099511627776),
  (-354964357663, 8796093022208), (-50059645273, 2199023255552), (-359035734235, 17592186044416),
  (-1613129271473, 140737488355328), (-1381150845909, 140737488355328), (-1140019947787, 281474976710656),
  (-58993831925, 17592186044416), (-555134413933, 562949953421312), (-1738779368381, 2251799813685248),
  (-111538380529, 1125899906842624), (-337564571475, 4503599627370496), (-69135455, 35184372088832),
  (-207422749, 140737488355328), (-1, 4294967296), (-1, 8589934592), (0, 1)]

private theorem old033_000 : entriesFrom (oldBracket p033 cuts033) 0 8 := by
  decide +kernel

private theorem old033_008 : entriesFrom (oldBracket p033 cuts033) 8 8 := by
  decide +kernel

private theorem old033_016 : entriesFrom (oldBracket p033 cuts033) 16 8 := by
  decide +kernel

private theorem old033_024 : entriesFrom (oldBracket p033 cuts033) 24 8 := by
  decide +kernel

private theorem new033_000 : entriesFrom (newBracket p034 cuts033) 0 8 := by
  decide +kernel

private theorem new033_008 : entriesFrom (newBracket p034 cuts033) 8 8 := by
  decide +kernel

private theorem new033_016 : entriesFrom (newBracket p034 cuts033) 16 8 := by
  decide +kernel

private theorem new033_024 : entriesFrom (newBracket p034 cuts033) 24 8 := by
  decide +kernel

private theorem new033_032 : entriesFrom (newBracket p034 cuts033) 32 1 := by
  decide +kernel

theorem literal033 : literalInterlaces 33 := by
  apply literal_interlacing_of_certificate 33 (by decide) p033 p034 cuts033 p033_eq p034_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 24) old033_000 (entriesFrom_join (s := 8) (n := 8) (m := 16) old033_008 (entriesFrom_join (s := 16) (n := 8) (m := 8) old033_016 old033_024))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 25) new033_000 (entriesFrom_join (s := 8) (n := 8) (m := 17) new033_008 (entriesFrom_join (s := 16) (n := 8) (m := 9) new033_016 (entriesFrom_join (s := 24) (n := 8) (m := 1) new033_024 new033_032))))⟩

private def cuts034 : Array Cut := #[
  (-51539607552, 1), (-25769803776, 1), (-12884901888, 1), (-301761447253, 262144), (-794777437961, 1048576),
  (-589028735647, 33554432), (-1781377014111, 134217728), (-1958019792629, 1073741824),
  (-1657349914919, 1073741824), (-820429311933, 2147483648), (-1440851966225, 4294967296),
  (-1041569753827, 8589934592), (-1763528835807, 17179869184), (-1026837036401, 17179869184),
  (-878130314243, 17179869184), (-2061017069925, 68719476736), (-109056405819, 4294967296),
  (-140258085659, 8589934592), (-1004353213171, 68719476736), (-363092063833, 34359738368),
  (-82790870509, 8589934592), (-2015894703881, 274877906944), (-861363229541, 137438953472),
  (-339118763637, 68719476736), (-1178436123295, 274877906944), (-459927498143, 137438953472),
  (-102371601617, 34359738368), (-1324180479, 536870912), (-9377205, 4194304), (-259813, 131072),
  (-13167, 8192), (-1425, 1024), (-615, 512), (-131, 128), (-225, 256), (-833, 1024), (-1403, 2048),
  (-9357, 16384), (-16699, 32768), (-7349, 16384), (-102659, 262144), (-356251, 1048576),
  (-2544211, 8388608), (-8106953, 33554432), (-115950465, 536870912), (-88858441, 536870912),
  (-305878575, 2147483648), (-877946743, 8589934592), (-6212360509, 68719476736),
  (-9092620627, 137438953472), (-266424863267, 4398046511104), (-354964357663, 8796093022208),
  (-1265131654081, 35184372088832), (-359035734235, 17592186044416), (-1278748361639, 70368744177664),
  (-1381150845909, 140737488355328), (-1178365627905, 140737488355328), (-58993831925, 17592186044416),
  (-1554635569683, 562949953421312), (-1738779368381, 2251799813685248), (-679926858275, 1125899906842624),
  (-337564571475, 4503599627370496), (-1021543052665, 18014398509481984), (-207422749, 140737488355328),
  (-207455517, 281474976710656), (-1, 8589934592), (-1, 17179869184), (0, 1)]

private theorem old034_000 : entriesFrom (oldBracket p034 cuts034) 0 8 := by
  decide +kernel

private theorem old034_008 : entriesFrom (oldBracket p034 cuts034) 8 8 := by
  decide +kernel

private theorem old034_016 : entriesFrom (oldBracket p034 cuts034) 16 8 := by
  decide +kernel

private theorem old034_024 : entriesFrom (oldBracket p034 cuts034) 24 8 := by
  decide +kernel

private theorem old034_032 : entriesFrom (oldBracket p034 cuts034) 32 1 := by
  decide +kernel

private theorem new034_000 : entriesFrom (newBracket p035 cuts034) 0 8 := by
  decide +kernel

private theorem new034_008 : entriesFrom (newBracket p035 cuts034) 8 8 := by
  decide +kernel

private theorem new034_016 : entriesFrom (newBracket p035 cuts034) 16 8 := by
  decide +kernel

private theorem new034_024 : entriesFrom (newBracket p035 cuts034) 24 8 := by
  decide +kernel

private theorem new034_032 : entriesFrom (newBracket p035 cuts034) 32 2 := by
  decide +kernel

theorem literal034 : literalInterlaces 34 := by
  apply literal_interlacing_of_certificate 34 (by decide) p034 p035 cuts034 p034_eq p035_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 25) old034_000 (entriesFrom_join (s := 8) (n := 8) (m := 17) old034_008 (entriesFrom_join (s := 16) (n := 8) (m := 9) old034_016 (entriesFrom_join (s := 24) (n := 8) (m := 1) old034_024 old034_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 26) new034_000 (entriesFrom_join (s := 8) (n := 8) (m := 18) new034_008 (entriesFrom_join (s := 16) (n := 8) (m := 10) new034_016 (entriesFrom_join (s := 24) (n := 8) (m := 2) new034_024 new034_032))))⟩

private def cuts035 : Array Cut := #[
  (-103079215104, 1), (-51539607552, 1), (-25769803776, 1), (-126975364851, 65536), (-301761447253, 262144),
  (-195780327035, 8388608), (-589028735647, 33554432), (-1171087963819, 536870912),
  (-1958019792629, 1073741824), (-488160609651, 1073741824), (-820429311933, 2147483648),
  (-1271586526155, 8589934592), (-1041569753827, 8589934592), (-1118923511327, 17179869184),
  (-1026837036401, 17179869184), (-1211946558343, 34359738368), (-2061017069925, 68719476736),
  (-638887068615, 34359738368), (-140258085659, 8589934592), (-1730537340837, 137438953472),
  (-363092063833, 34359738368), (-2174247991983, 274877906944), (-2015894703881, 274877906944),
  (-1539600756815, 274877906944), (-339118763637, 68719476736), (-2098291119581, 549755813888),
  (-459927498143, 137438953472), (-102371601617, 34359738368), (-1324180479, 536870912), (-9377205, 4194304),
  (-259813, 131072), (-13167, 8192), (-1425, 1024), (-615, 512), (-131, 128), (-225, 256), (-833, 1024),
  (-1403, 2048), (-20581, 32768), (-16699, 32768), (-7349, 16384), (-102659, 262144), (-356251, 1048576),
  (-18283797, 67108864), (-34497703, 134217728), (-115950465, 536870912), (-102404453, 536870912),
  (-305878575, 2147483648), (-2101461043, 17179869184), (-6212360509, 68719476736),
  (-46366783681, 549755813888), (-266424863267, 4398046511104), (-887814084197, 17592186044416),
  (-1265131654081, 35184372088832), (-1983203122551, 70368744177664), (-1278748361639, 70368744177664),
  (-141463140871, 8796093022208), (-1178365627905, 140737488355328), (-1001761884779, 140737488355328),
  (-1554635569683, 562949953421312), (-637325193893, 281474976710656), (-679926858275, 1125899906842624),
  (-1062085858847, 2251799813685248), (-1021543052665, 18014398509481984),
  (-772794817467, 18014398509481984), (-207455517, 281474976710656), (-622399319, 1125899906842624),
  (-1, 17179869184), (-1, 34359738368), (0, 1)]

private theorem old035_000 : entriesFrom (oldBracket p035 cuts035) 0 8 := by
  decide +kernel

private theorem old035_008 : entriesFrom (oldBracket p035 cuts035) 8 8 := by
  decide +kernel

private theorem old035_016 : entriesFrom (oldBracket p035 cuts035) 16 8 := by
  decide +kernel

private theorem old035_024 : entriesFrom (oldBracket p035 cuts035) 24 8 := by
  decide +kernel

private theorem old035_032 : entriesFrom (oldBracket p035 cuts035) 32 2 := by
  decide +kernel

private theorem new035_000 : entriesFrom (newBracket p036 cuts035) 0 8 := by
  decide +kernel

private theorem new035_008 : entriesFrom (newBracket p036 cuts035) 8 8 := by
  decide +kernel

private theorem new035_016 : entriesFrom (newBracket p036 cuts035) 16 8 := by
  decide +kernel

private theorem new035_024 : entriesFrom (newBracket p036 cuts035) 24 8 := by
  decide +kernel

private theorem new035_032 : entriesFrom (newBracket p036 cuts035) 32 3 := by
  decide +kernel

theorem literal035 : literalInterlaces 35 := by
  apply literal_interlacing_of_certificate 35 (by decide) p035 p036 cuts035 p035_eq p036_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 26) old035_000 (entriesFrom_join (s := 8) (n := 8) (m := 18) old035_008 (entriesFrom_join (s := 16) (n := 8) (m := 10) old035_016 (entriesFrom_join (s := 24) (n := 8) (m := 2) old035_024 old035_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 27) new035_000 (entriesFrom_join (s := 8) (n := 8) (m := 19) new035_008 (entriesFrom_join (s := 16) (n := 8) (m := 11) new035_016 (entriesFrom_join (s := 24) (n := 8) (m := 3) new035_024 new035_032))))⟩

private def cuts036 : Array Cut := #[
  (-206158430208, 1), (-103079215104, 1), (-51539607552, 1), (-1428088779379, 524288),
  (-126975364851, 65536), (-1078764620173, 33554432), (-195780327035, 8388608), (-1429005832773, 536870912),
  (-1171087963819, 536870912), (-580026808587, 1073741824), (-488160609651, 1073741824),
  (-95178304147, 536870912), (-1271586526155, 8589934592), (-1359977510409, 17179869184),
  (-1118923511327, 17179869184), (-658581248825, 17179869184), (-1211946558343, 34359738368),
  (-368396217601, 17179869184), (-638887068615, 34359738368), (-232366918533, 17179869184),
  (-1730537340837, 137438953472), (-634873062831, 68719476736), (-2174247991983, 274877906944),
  (-444436932587, 68719476736), (-1539600756815, 274877906944), (-1202810307169, 274877906944),
  (-2098291119581, 549755813888), (-459927498143, 137438953472), (-102371601617, 34359738368),
  (-1324180479, 536870912), (-9377205, 4194304), (-470485, 262144), (-13167, 8192), (-1425, 1024),
  (-615, 512), (-131, 128), (-225, 256), (-833, 1024), (-1403, 2048), (-20581, 32768), (-1165, 2048),
  (-7349, 16384), (-220243, 524288), (-356251, 1048576), (-41083861, 134217728), (-34497703, 134217728),
  (-115950465, 536870912), (-102404453, 536870912), (-715496387, 4294967296), (-2101461043, 17179869184),
  (-14618204681, 137438953472), (-46366783681, 549755813888), (-637359132715, 8796093022208),
  (-887814084197, 17592186044416), (-206000504977, 4398046511104), (-1983203122551, 70368744177664),
  (-1807089432323, 70368744177664), (-141463140871, 8796093022208), (-498037274357, 35184372088832),
  (-1001761884779, 140737488355328), (-1696972273379, 281474976710656), (-637325193893, 281474976710656),
  (-260244662031, 140737488355328), (-1062085858847, 2251799813685248), (-828487614531, 2251799813685248),
  (-772794817467, 18014398509481984), (-145728850343, 4503599627370496), (-622399319, 1125899906842624),
  (-1867263493, 4503599627370496), (-1, 34359738368), (-1, 68719476736), (0, 1)]

private theorem old036_000 : entriesFrom (oldBracket p036 cuts036) 0 8 := by
  decide +kernel

private theorem old036_008 : entriesFrom (oldBracket p036 cuts036) 8 8 := by
  decide +kernel

private theorem old036_016 : entriesFrom (oldBracket p036 cuts036) 16 8 := by
  decide +kernel

private theorem old036_024 : entriesFrom (oldBracket p036 cuts036) 24 8 := by
  decide +kernel

private theorem old036_032 : entriesFrom (oldBracket p036 cuts036) 32 3 := by
  decide +kernel

private theorem new036_000 : entriesFrom (newBracket p037 cuts036) 0 8 := by
  decide +kernel

private theorem new036_008 : entriesFrom (newBracket p037 cuts036) 8 8 := by
  decide +kernel

private theorem new036_016 : entriesFrom (newBracket p037 cuts036) 16 8 := by
  decide +kernel

private theorem new036_024 : entriesFrom (newBracket p037 cuts036) 24 8 := by
  decide +kernel

private theorem new036_032 : entriesFrom (newBracket p037 cuts036) 32 4 := by
  decide +kernel

theorem literal036 : literalInterlaces 36 := by
  apply literal_interlacing_of_certificate 36 (by decide) p036 p037 cuts036 p036_eq p037_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 27) old036_000 (entriesFrom_join (s := 8) (n := 8) (m := 19) old036_008 (entriesFrom_join (s := 16) (n := 8) (m := 11) old036_016 (entriesFrom_join (s := 24) (n := 8) (m := 3) old036_024 old036_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 28) new036_000 (entriesFrom_join (s := 8) (n := 8) (m := 20) new036_008 (entriesFrom_join (s := 16) (n := 8) (m := 12) new036_016 (entriesFrom_join (s := 24) (n := 8) (m := 4) new036_024 new036_032))))⟩

private def cuts037 : Array Cut := #[
  (-412316860416, 1), (-206158430208, 1), (-103079215104, 1), (-8799527025, 2048), (-1428088779379, 524288),
  (-789119115491, 16777216), (-1078764620173, 33554432), (-2122814276365, 536870912),
  (-1429005832773, 536870912), (-1600590896937, 2147483648), (-580026808587, 1073741824),
  (-1820656867709, 8589934592), (-95178304147, 536870912), (-1507876953147, 17179869184),
  (-1359977510409, 17179869184), (-1547333628901, 34359738368), (-658581248825, 17179869184),
  (-855580965987, 34359738368), (-368396217601, 17179869184), (-1103620905681, 68719476736),
  (-232366918533, 17179869184), (-86558995591, 8589934592), (-634873062831, 68719476736),
  (-987998930583, 137438953472), (-444436932587, 68719476736), (-171400691499, 34359738368),
  (-1202810307169, 274877906944), (-492250139019, 137438953472), (-459927498143, 137438953472),
  (-187119152273, 68719476736), (-1324180479, 536870912), (-16904965, 8388608), (-470485, 262144),
  (-13167, 8192), (-1425, 1024), (-615, 512), (-131, 128), (-225, 256), (-833, 1024), (-1403, 2048),
  (-20581, 32768), (-1165, 2048), (-16669, 32768), (-220243, 524288), (-796737, 2097152),
  (-41083861, 134217728), (-18895391, 67108864), (-115950465, 536870912), (-109177459, 536870912),
  (-715496387, 4294967296), (-4963446591, 34359738368), (-14618204681, 137438953472),
  (-104839602405, 1099511627776), (-637359132715, 8796093022208), (-588996110061, 8796093022208),
  (-206000504977, 4398046511104), (-1483903420181, 35184372088832), (-1807089432323, 70368744177664),
  (-102390209749, 4398046511104), (-498037274357, 35184372088832), (-46779859097, 4398046511104),
  (-1696972273379, 281474976710656), (-358015125877, 70368744177664), (-260244662031, 140737488355328),
  (-847114352271, 562949953421312), (-828487614531, 2251799813685248), (-40344721809, 140737488355328),
  (-145728850343, 4503599627370496), (-439676148305, 18014398509481984), (-1867263493, 4503599627370496),
  (-1867394565, 9007199254740992), (-1, 68719476736), (-1, 137438953472), (0, 1)]

private theorem old037_000 : entriesFrom (oldBracket p037 cuts037) 0 8 := by
  decide +kernel

private theorem old037_008 : entriesFrom (oldBracket p037 cuts037) 8 8 := by
  decide +kernel

private theorem old037_016 : entriesFrom (oldBracket p037 cuts037) 16 8 := by
  decide +kernel

private theorem old037_024 : entriesFrom (oldBracket p037 cuts037) 24 8 := by
  decide +kernel

private theorem old037_032 : entriesFrom (oldBracket p037 cuts037) 32 4 := by
  decide +kernel

private theorem new037_000 : entriesFrom (newBracket p038 cuts037) 0 8 := by
  decide +kernel

private theorem new037_008 : entriesFrom (newBracket p038 cuts037) 8 8 := by
  decide +kernel

private theorem new037_016 : entriesFrom (newBracket p038 cuts037) 16 8 := by
  decide +kernel

private theorem new037_024 : entriesFrom (newBracket p038 cuts037) 24 8 := by
  decide +kernel

private theorem new037_032 : entriesFrom (newBracket p038 cuts037) 32 5 := by
  decide +kernel

theorem literal037 : literalInterlaces 37 := by
  apply literal_interlacing_of_certificate 37 (by decide) p037 p038 cuts037 p037_eq p038_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 28) old037_000 (entriesFrom_join (s := 8) (n := 8) (m := 20) old037_008 (entriesFrom_join (s := 16) (n := 8) (m := 12) old037_016 (entriesFrom_join (s := 24) (n := 8) (m := 4) old037_024 old037_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 29) new037_000 (entriesFrom_join (s := 8) (n := 8) (m := 21) new037_008 (entriesFrom_join (s := 16) (n := 8) (m := 13) new037_016 (entriesFrom_join (s := 24) (n := 8) (m := 5) new037_024 new037_032))))⟩

private def cuts038 : Array Cut := #[
  (-824633720832, 1), (-412316860416, 1), (-206158430208, 1), (-96164945815, 16384), (-8799527025, 2048),
  (-569988158623, 8388608), (-789119115491, 16777216), (-648964660079, 134217728),
  (-2122814276365, 536870912), (-232225678009, 268435456), (-1600590896937, 2147483648),
  (-271637695979, 1073741824), (-1820656867709, 8589934592), (-6641037307, 67108864),
  (-1507876953147, 17179869184), (-115030561055, 2147483648), (-1547333628901, 34359738368),
  (-970976348903, 34359738368), (-855580965987, 34359738368), (-598055948431, 34359738368),
  (-1103620905681, 68719476736), (-405484909715, 34359738368), (-86558995591, 8589934592),
  (-1058435729353, 137438953472), (-987998930583, 137438953472), (-787238315585, 137438953472),
  (-171400691499, 34359738368), (-2187310585207, 549755813888), (-492250139019, 137438953472),
  (-834165802689, 274877906944), (-187119152273, 68719476736), (-2406098239, 1073741824),
  (-16904965, 8388608), (-470485, 262144), (-13167, 8192), (-1425, 1024), (-615, 512), (-131, 128),
  (-487, 512), (-833, 1024), (-3069, 4096), (-20581, 32768), (-1165, 2048), (-16669, 32768),
  (-220243, 524288), (-796737, 2097152), (-92075029, 268435456), (-18895391, 67108864),
  (-267113593, 1073741824), (-109177459, 536870912), (-1588916059, 8589934592), (-4963446591, 34359738368),
  (-34471991045, 274877906944), (-104839602405, 1099511627776), (-788377397609, 8796093022208),
  (-588996110061, 8796093022208), (-1000997120015, 17592186044416), (-1483903420181, 35184372088832),
  (-1193724068171, 35184372088832), (-102390209749, 4398046511104), (-1317158952349, 70368744177664),
  (-46779859097, 4398046511104), (-333709538125, 35184372088832), (-358015125877, 70368744177664),
  (-602083854323, 140737488355328), (-847114352271, 562949953421312), (-1374232480223, 1125899906842624),
  (-40344721809, 140737488355328), (-502352768001, 2251799813685248), (-439676148305, 18014398509481984),
  (-1326497498887, 72057594037927936), (-1867394565, 9007199254740992), (-5602314767, 36028797018963968),
  (-1, 137438953472), (-1, 274877906944), (0, 1)]

private theorem old038_000 : entriesFrom (oldBracket p038 cuts038) 0 8 := by
  decide +kernel

private theorem old038_008 : entriesFrom (oldBracket p038 cuts038) 8 8 := by
  decide +kernel

private theorem old038_016 : entriesFrom (oldBracket p038 cuts038) 16 8 := by
  decide +kernel

private theorem old038_024 : entriesFrom (oldBracket p038 cuts038) 24 8 := by
  decide +kernel

private theorem old038_032 : entriesFrom (oldBracket p038 cuts038) 32 5 := by
  decide +kernel

private theorem new038_000 : entriesFrom (newBracket p039 cuts038) 0 8 := by
  decide +kernel

private theorem new038_008 : entriesFrom (newBracket p039 cuts038) 8 8 := by
  decide +kernel

private theorem new038_016 : entriesFrom (newBracket p039 cuts038) 16 8 := by
  decide +kernel

private theorem new038_024 : entriesFrom (newBracket p039 cuts038) 24 8 := by
  decide +kernel

private theorem new038_032 : entriesFrom (newBracket p039 cuts038) 32 6 := by
  decide +kernel

theorem literal038 : literalInterlaces 38 := by
  apply literal_interlacing_of_certificate 38 (by decide) p038 p039 cuts038 p038_eq p039_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 29) old038_000 (entriesFrom_join (s := 8) (n := 8) (m := 21) old038_008 (entriesFrom_join (s := 16) (n := 8) (m := 13) old038_016 (entriesFrom_join (s := 24) (n := 8) (m := 5) old038_024 old038_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 30) new038_000 (entriesFrom_join (s := 8) (n := 8) (m := 22) new038_008 (entriesFrom_join (s := 16) (n := 8) (m := 14) new038_016 (entriesFrom_join (s := 24) (n := 8) (m := 6) new038_024 new038_032))))⟩

private def cuts039 : Array Cut := #[
  (-1649267441664, 1), (-824633720832, 1), (-412316860416, 1), (-1181624688051, 131072),
  (-96164945815, 16384), (-1417108149557, 16777216), (-569988158623, 8388608), (-1651928586649, 268435456),
  (-648964660079, 134217728), (-1136198077079, 1073741824), (-232225678009, 268435456),
  (-1350879660161, 4294967296), (-271637695979, 1073741824), (-1092703798399, 8589934592),
  (-6641037307, 67108864), (-1987397093057, 34359738368), (-115030561055, 2147483648),
  (-557532834451, 17179869184), (-970976348903, 34359738368), (-165609300705, 8589934592),
  (-598055948431, 34359738368), (-884132590993, 68719476736), (-405484909715, 34359738368),
  (-305422457351, 34359738368), (-1058435729353, 137438953472), (-221904655771, 34359738368),
  (-787238315585, 137438953472), (-616215206149, 137438953472), (-2187310585207, 549755813888),
  (-1818666080727, 549755813888), (-834165802689, 274877906944), (-341109439569, 137438953472),
  (-2406098239, 1073741824), (-16904965, 8388608), (-470485, 262144), (-13167, 8192), (-1425, 1024),
  (-615, 512), (-131, 128), (-487, 512), (-833, 1024), (-3069, 4096), (-20581, 32768), (-1165, 2048),
  (-16669, 32768), (-220243, 524288), (-796737, 2097152), (-92075029, 268435456), (-167656593, 536870912),
  (-267113593, 1073741824), (-485468511, 2147483648), (-1588916059, 8589934592), (-11319110827, 68719476736),
  (-34471991045, 274877906944), (-242727566585, 2199023255552), (-788377397609, 8796093022208),
  (-688686753835, 8796093022208), (-1000997120015, 17592186044416), (-871474415053, 17592186044416),
  (-1193724068171, 35184372088832), (-550036735313, 17592186044416), (-1317158952349, 70368744177664),
  (-587494325325, 35184372088832), (-333709538125, 35184372088832), (-590068088657, 70368744177664),
  (-602083854323, 140737488355328), (-2018030151037, 562949953421312), (-1374232480223, 1125899906842624),
  (-1111363803785, 1125899906842624), (-502352768001, 2251799813685248), (-1562017822541, 9007199254740992),
  (-1326497498887, 72057594037927936), (-998607913295, 72057594037927936), (-5602314767, 36028797018963968),
  (-16807206445, 144115188075855872), (-1, 274877906944), (-1, 549755813888), (0, 1)]

private theorem old039_000 : entriesFrom (oldBracket p039 cuts039) 0 8 := by
  decide +kernel

private theorem old039_008 : entriesFrom (oldBracket p039 cuts039) 8 8 := by
  decide +kernel

private theorem old039_016 : entriesFrom (oldBracket p039 cuts039) 16 8 := by
  decide +kernel

private theorem old039_024 : entriesFrom (oldBracket p039 cuts039) 24 8 := by
  decide +kernel

private theorem old039_032 : entriesFrom (oldBracket p039 cuts039) 32 6 := by
  decide +kernel

private theorem new039_000 : entriesFrom (newBracket p040 cuts039) 0 8 := by
  decide +kernel

private theorem new039_008 : entriesFrom (newBracket p040 cuts039) 8 8 := by
  decide +kernel

private theorem new039_016 : entriesFrom (newBracket p040 cuts039) 16 8 := by
  decide +kernel

private theorem new039_024 : entriesFrom (newBracket p040 cuts039) 24 8 := by
  decide +kernel

private theorem new039_032 : entriesFrom (newBracket p040 cuts039) 32 7 := by
  decide +kernel

theorem literal039 : literalInterlaces 39 := by
  apply literal_interlacing_of_certificate 39 (by decide) p039 p040 cuts039 p039_eq p040_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 30) old039_000 (entriesFrom_join (s := 8) (n := 8) (m := 22) old039_008 (entriesFrom_join (s := 16) (n := 8) (m := 14) old039_016 (entriesFrom_join (s := 24) (n := 8) (m := 6) old039_024 old039_032)))),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 31) new039_000 (entriesFrom_join (s := 8) (n := 8) (m := 23) new039_008 (entriesFrom_join (s := 16) (n := 8) (m := 15) new039_016 (entriesFrom_join (s := 24) (n := 8) (m := 7) new039_024 new039_032))))⟩

end DukesRevstack.FiniteData
