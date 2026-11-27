import Conjectures.DukesRevstackCutCertificate
import Conjectures.DukesRevstackFiniteRows016To023

/-! Dyadic separators for every transition from orders 8 through 15 to their successors. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

private def cuts008 : Array Cut := #[
  (-768, 1), (-384, 1), (-192, 1), (-1419, 64), (-93, 8), (-33, 8), (-3, 1), (-21, 16), (-5, 8), (-3, 8),
  (-1, 4), (-5, 64), (-3, 64), (-1, 128), (-1, 256), (0, 1)]

private theorem old008_000 : entriesFrom (oldBracket p008 cuts008) 0 7 := by
  decide +kernel

private theorem new008_000 : entriesFrom (newBracket p009 cuts008) 0 8 := by
  decide +kernel

theorem literal008 : literalInterlaces 8 := by
  apply literal_interlacing_of_certificate 8 (by decide) p008 p009 cuts008 p008_eq p009_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero old008_000,
    entriesFrom_zero new008_000⟩

private def cuts009 : Array Cut := #[
  (-1536, 1), (-768, 1), (-384, 1), (-33573, 1024), (-1419, 64), (-6, 1), (-33, 8), (-69, 32), (-21, 16),
  (-5, 8), (-1, 2), (-1, 4), (-21, 128), (-3, 64), (-7, 256), (-1, 256), (-1, 512), (0, 1)]

private theorem old009_000 : entriesFrom (oldBracket p009 cuts009) 0 8 := by
  decide +kernel

private theorem new009_000 : entriesFrom (newBracket p010 cuts009) 0 8 := by
  decide +kernel

private theorem new009_008 : entriesFrom (newBracket p010 cuts009) 8 1 := by
  decide +kernel

theorem literal009 : literalInterlaces 9 := by
  apply literal_interlacing_of_certificate 9 (by decide) p009 p010 cuts009 p009_eq p010_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero old009_000,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 1) new009_000 new009_008)⟩

private def cuts010 : Array Cut := #[
  (-3072, 1), (-1536, 1), (-768, 1), (-896811, 16384), (-33573, 1024), (-2571, 256), (-6, 1), (-201, 64),
  (-69, 32), (-21, 16), (-31, 32), (-1, 2), (-3, 8), (-21, 128), (-27, 256), (-7, 256), (-11, 512),
  (-1, 512), (-1, 1024), (0, 1)]

private theorem old010_000 : entriesFrom (oldBracket p010 cuts010) 0 8 := by
  decide +kernel

private theorem old010_008 : entriesFrom (oldBracket p010 cuts010) 8 1 := by
  decide +kernel

private theorem new010_000 : entriesFrom (newBracket p011 cuts010) 0 8 := by
  decide +kernel

private theorem new010_008 : entriesFrom (newBracket p011 cuts010) 8 2 := by
  decide +kernel

theorem literal010 : literalInterlaces 10 := by
  apply literal_interlacing_of_certificate 10 (by decide) p010 p011 cuts010 p010_eq p011_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 1) old010_000 old010_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 2) new010_000 new010_008)⟩

private def cuts011 : Array Cut := #[
  (-6144, 1), (-3072, 1), (-1536, 1), (-40384053, 524288), (-896811, 16384), (-64425, 4096), (-2571, 256),
  (-585, 128), (-201, 64), (-69, 32), (-21, 16), (-31, 32), (-1, 2), (-3, 8), (-69, 256), (-27, 256),
  (-17, 256), (-11, 512), (-3, 256), (-1, 1024), (-1, 2048), (0, 1)]

private theorem old011_000 : entriesFrom (oldBracket p011 cuts011) 0 8 := by
  decide +kernel

private theorem old011_008 : entriesFrom (oldBracket p011 cuts011) 8 2 := by
  decide +kernel

private theorem new011_000 : entriesFrom (newBracket p012 cuts011) 0 8 := by
  decide +kernel

private theorem new011_008 : entriesFrom (newBracket p012 cuts011) 8 3 := by
  decide +kernel

theorem literal011 : literalInterlaces 11 := by
  apply literal_interlacing_of_certificate 11 (by decide) p011 p012 cuts011 p011_eq p012_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 2) old011_000 old011_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 3) new011_000 new011_008)⟩

private def cuts012 : Array Cut := #[
  (-12288, 1), (-6144, 1), (-3072, 1), (-2057212011, 16777216), (-40384053, 524288), (-2700711, 131072),
  (-64425, 4096), (-6081, 1024), (-585, 128), (-339, 128), (-69, 32), (-21, 16), (-31, 32), (-1, 2), (-3, 8),
  (-69, 256), (-3, 16), (-17, 256), (-45, 1024), (-3, 256), (-37, 4096), (-1, 2048), (-1, 4096), (0, 1)]

private theorem old012_000 : entriesFrom (oldBracket p012 cuts012) 0 8 := by
  decide +kernel

private theorem old012_008 : entriesFrom (oldBracket p012 cuts012) 8 3 := by
  decide +kernel

private theorem new012_000 : entriesFrom (newBracket p013 cuts012) 0 8 := by
  decide +kernel

private theorem new012_008 : entriesFrom (newBracket p013 cuts012) 8 4 := by
  decide +kernel

theorem literal012 : literalInterlaces 12 := by
  apply literal_interlacing_of_certificate 12 (by decide) p012 p013 cuts012 p012_eq p013_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 3) old012_000 old012_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 4) new012_000 new012_008)⟩

private def cuts013 : Array Cut := #[
  (-24576, 1), (-12288, 1), (-6144, 1), (-115313179893, 536870912), (-2057212011, 16777216),
  (-116003961, 4194304), (-2700711, 131072), (-137397, 16384), (-6081, 1024), (-231, 64), (-339, 128),
  (-111, 64), (-21, 16), (-47, 64), (-79, 128), (-3, 8), (-69, 256), (-3, 16), (-65, 512), (-45, 1024),
  (-147, 4096), (-37, 4096), (-39, 8192), (-1, 4096), (-1, 8192), (0, 1)]

private theorem old013_000 : entriesFrom (oldBracket p013 cuts013) 0 8 := by
  decide +kernel

private theorem old013_008 : entriesFrom (oldBracket p013 cuts013) 8 4 := by
  decide +kernel

private theorem new013_000 : entriesFrom (newBracket p014 cuts013) 0 8 := by
  decide +kernel

private theorem new013_008 : entriesFrom (newBracket p014 cuts013) 8 5 := by
  decide +kernel

theorem literal013 : literalInterlaces 13 := by
  apply literal_interlacing_of_certificate 13 (by decide) p013 p014 cuts013 p013_eq p014_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 4) old013_000 old013_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 5) new013_000 new013_008)⟩

private def cuts014 : Array Cut := #[
  (-49152, 1), (-24576, 1), (-12288, 1), (-1320408152073, 4294967296), (-115313179893, 536870912),
  (-5305322919, 134217728), (-116003961, 4194304), (-5998239, 524288), (-137397, 16384), (-9777, 2048),
  (-231, 64), (-561, 256), (-111, 64), (-21, 16), (-47, 64), (-79, 128), (-127, 256), (-69, 256), (-3, 16),
  (-65, 512), (-175, 2048), (-147, 4096), (-23, 1024), (-39, 8192), (-119, 32768), (-1, 8192), (-1, 16384),
  (0, 1)]

private theorem old014_000 : entriesFrom (oldBracket p014 cuts014) 0 8 := by
  decide +kernel

private theorem old014_008 : entriesFrom (oldBracket p014 cuts014) 8 5 := by
  decide +kernel

private theorem new014_000 : entriesFrom (newBracket p015 cuts014) 0 8 := by
  decide +kernel

private theorem new014_008 : entriesFrom (newBracket p015 cuts014) 8 6 := by
  decide +kernel

theorem literal014 : literalInterlaces 14 := by
  apply literal_interlacing_of_certificate 14 (by decide) p014 p015 cuts014 p014_eq p015_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 5) old014_000 old014_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 6) new014_000 new014_008)⟩

private def cuts015 : Array Cut := #[
  (-98304, 1), (-49152, 1), (-24576, 1), (-2124410495529, 4294967296), (-1320408152073, 4294967296),
  (-263862221625, 4294967296), (-5305322919, 134217728), (-259961697, 16777216), (-5998239, 524288),
  (-215613, 32768), (-9777, 2048), (-1485, 512), (-561, 256), (-111, 64), (-21, 16), (-47, 64), (-79, 128),
  (-127, 256), (-49, 128), (-3, 16), (-161, 1024), (-175, 2048), (-497, 8192), (-23, 1024), (-591, 32768),
  (-119, 32768), (-123, 65536), (-1, 16384), (-1, 32768), (0, 1)]

private theorem old015_000 : entriesFrom (oldBracket p015 cuts015) 0 8 := by
  decide +kernel

private theorem old015_008 : entriesFrom (oldBracket p015 cuts015) 8 6 := by
  decide +kernel

private theorem new015_000 : entriesFrom (newBracket p016 cuts015) 0 8 := by
  decide +kernel

private theorem new015_008 : entriesFrom (newBracket p016 cuts015) 8 7 := by
  decide +kernel

theorem literal015 : literalInterlaces 15 := by
  apply literal_interlacing_of_certificate 15 (by decide) p015 p016 cuts015 p015_eq p016_eq
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 6) old015_000 old015_008),
    entriesFrom_zero (entriesFrom_join (s := 0) (n := 8) (m := 7) new015_000 new015_008)⟩

end DukesRevstack.FiniteData
