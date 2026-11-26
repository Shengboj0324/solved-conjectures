import Conjectures.DukesRevstackCutCertificate
import Conjectures.DukesRevstackFiniteRows008To015

/-! Dyadic separators for every transition from orders 3 through 7 to their successors. -/

namespace DukesRevstack.FiniteData

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 80000000

private def cuts003 : Array Cut := #[
  (-12, 1), (-3, 1), (-2, 1), (-5, 8), (-1, 4), (0, 1)]

theorem literal003 : literalInterlaces 3 := by
  apply literal_interlacing_of_certificate 3 (by decide) p003 p004 cuts003 p003_eq p004_eq
  decide +kernel

private def cuts004 : Array Cut := #[
  (-24, 1), (-12, 1), (-3, 1), (-2, 1), (-5, 8), (-1, 8), (-1, 16), (0, 1)]

theorem literal004 : literalInterlaces 4 := by
  apply literal_interlacing_of_certificate 4 (by decide) p004 p005 cuts004 p004_eq p005_eq
  decide +kernel

private def cuts005 : Array Cut := #[
  (-96, 1), (-24, 1), (-12, 1), (-3, 1), (-2, 1), (-5, 8), (-3, 8), (-1, 16), (-1, 32), (0, 1)]

theorem literal005 : literalInterlaces 5 := by
  apply literal_interlacing_of_certificate 5 (by decide) p005 p006 cuts005 p005_eq p006_eq
  decide +kernel

private def cuts006 : Array Cut := #[
  (-192, 1), (-96, 1), (-24, 1), (-15, 2), (-3, 1), (-21, 16), (-5, 8), (-3, 8), (-7, 32), (-1, 32),
  (-1, 64), (0, 1)]

theorem literal006 : literalInterlaces 6 := by
  apply literal_interlacing_of_certificate 6 (by decide) p006 p007 cuts006 p006_eq p007_eq
  decide +kernel

private def cuts007 : Array Cut := #[
  (-384, 1), (-192, 1), (-96, 1), (-93, 8), (-15, 2), (-3, 1), (-21, 16), (-5, 8), (-3, 8), (-1, 8),
  (-5, 64), (-1, 64), (-1, 128), (0, 1)]

theorem literal007 : literalInterlaces 7 := by
  apply literal_interlacing_of_certificate 7 (by decide) p007 p008 cuts007 p007_eq p008_eq
  decide +kernel

end DukesRevstack.FiniteData
