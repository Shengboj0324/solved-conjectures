import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 32 through 63. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass32 : massAt 33 = 2 * nestedSum 32 massAt 32 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed32 : packedAt 33 = (1 + digitBase) * nestedSum 32 packedAt 32 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign32 : SignCertificate 32 := by decide +kernel
private theorem checked32 : IndexCertificate 32 := ⟨mass32, packed32, fun _ => sign32⟩

private theorem mass33 : massAt 34 = 2 * nestedSum 33 massAt 33 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed33 : packedAt 34 = (1 + digitBase) * nestedSum 33 packedAt 33 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign33 : SignCertificate 33 := by decide +kernel
private theorem checked33 : IndexCertificate 33 := ⟨mass33, packed33, fun _ => sign33⟩

private theorem mass34 : massAt 35 = 2 * nestedSum 34 massAt 34 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed34 : packedAt 35 = (1 + digitBase) * nestedSum 34 packedAt 34 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign34 : SignCertificate 34 := by decide +kernel
private theorem checked34 : IndexCertificate 34 := ⟨mass34, packed34, fun _ => sign34⟩

private theorem mass35 : massAt 36 = 2 * nestedSum 35 massAt 35 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed35 : packedAt 36 = (1 + digitBase) * nestedSum 35 packedAt 35 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign35 : SignCertificate 35 := by decide +kernel
private theorem checked35 : IndexCertificate 35 := ⟨mass35, packed35, fun _ => sign35⟩

private theorem mass36 : massAt 37 = 2 * nestedSum 36 massAt 36 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed36 : packedAt 37 = (1 + digitBase) * nestedSum 36 packedAt 36 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign36 : SignCertificate 36 := by decide +kernel
private theorem checked36 : IndexCertificate 36 := ⟨mass36, packed36, fun _ => sign36⟩

private theorem mass37 : massAt 38 = 2 * nestedSum 37 massAt 37 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed37 : packedAt 38 = (1 + digitBase) * nestedSum 37 packedAt 37 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign37 : SignCertificate 37 := by decide +kernel
private theorem checked37 : IndexCertificate 37 := ⟨mass37, packed37, fun _ => sign37⟩

private theorem mass38 : massAt 39 = 2 * nestedSum 38 massAt 38 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed38 : packedAt 39 = (1 + digitBase) * nestedSum 38 packedAt 38 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign38 : SignCertificate 38 := by decide +kernel
private theorem checked38 : IndexCertificate 38 := ⟨mass38, packed38, fun _ => sign38⟩

private theorem mass39 : massAt 40 = 2 * nestedSum 39 massAt 39 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed39 : packedAt 40 = (1 + digitBase) * nestedSum 39 packedAt 39 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign39 : SignCertificate 39 := by decide +kernel
private theorem checked39 : IndexCertificate 39 := ⟨mass39, packed39, fun _ => sign39⟩

private theorem mass40 : massAt 41 = 2 * nestedSum 40 massAt 40 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed40 : packedAt 41 = (1 + digitBase) * nestedSum 40 packedAt 40 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign40 : SignCertificate 40 := by decide +kernel
private theorem checked40 : IndexCertificate 40 := ⟨mass40, packed40, fun _ => sign40⟩

private theorem mass41 : massAt 42 = 2 * nestedSum 41 massAt 41 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed41 : packedAt 42 = (1 + digitBase) * nestedSum 41 packedAt 41 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign41 : SignCertificate 41 := by decide +kernel
private theorem checked41 : IndexCertificate 41 := ⟨mass41, packed41, fun _ => sign41⟩

private theorem mass42 : massAt 43 = 2 * nestedSum 42 massAt 42 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed42 : packedAt 43 = (1 + digitBase) * nestedSum 42 packedAt 42 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign42 : SignCertificate 42 := by decide +kernel
private theorem checked42 : IndexCertificate 42 := ⟨mass42, packed42, fun _ => sign42⟩

private theorem mass43 : massAt 44 = 2 * nestedSum 43 massAt 43 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed43 : packedAt 44 = (1 + digitBase) * nestedSum 43 packedAt 43 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign43 : SignCertificate 43 := by decide +kernel
private theorem checked43 : IndexCertificate 43 := ⟨mass43, packed43, fun _ => sign43⟩

private theorem mass44 : massAt 45 = 2 * nestedSum 44 massAt 44 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed44 : packedAt 45 = (1 + digitBase) * nestedSum 44 packedAt 44 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign44 : SignCertificate 44 := by decide +kernel
private theorem checked44 : IndexCertificate 44 := ⟨mass44, packed44, fun _ => sign44⟩

private theorem mass45 : massAt 46 = 2 * nestedSum 45 massAt 45 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed45 : packedAt 46 = (1 + digitBase) * nestedSum 45 packedAt 45 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign45 : SignCertificate 45 := by decide +kernel
private theorem checked45 : IndexCertificate 45 := ⟨mass45, packed45, fun _ => sign45⟩

private theorem mass46 : massAt 47 = 2 * nestedSum 46 massAt 46 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed46 : packedAt 47 = (1 + digitBase) * nestedSum 46 packedAt 46 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign46 : SignCertificate 46 := by decide +kernel
private theorem checked46 : IndexCertificate 46 := ⟨mass46, packed46, fun _ => sign46⟩

private theorem mass47 : massAt 48 = 2 * nestedSum 47 massAt 47 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed47 : packedAt 48 = (1 + digitBase) * nestedSum 47 packedAt 47 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign47 : SignCertificate 47 := by decide +kernel
private theorem checked47 : IndexCertificate 47 := ⟨mass47, packed47, fun _ => sign47⟩

private theorem mass48 : massAt 49 = 2 * nestedSum 48 massAt 48 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed48 : packedAt 49 = (1 + digitBase) * nestedSum 48 packedAt 48 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign48 : SignCertificate 48 := by decide +kernel
private theorem checked48 : IndexCertificate 48 := ⟨mass48, packed48, fun _ => sign48⟩

private theorem mass49 : massAt 50 = 2 * nestedSum 49 massAt 49 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed49 : packedAt 50 = (1 + digitBase) * nestedSum 49 packedAt 49 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign49 : SignCertificate 49 := by decide +kernel
private theorem checked49 : IndexCertificate 49 := ⟨mass49, packed49, fun _ => sign49⟩

private theorem mass50 : massAt 51 = 2 * nestedSum 50 massAt 50 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed50 : packedAt 51 = (1 + digitBase) * nestedSum 50 packedAt 50 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign50 : SignCertificate 50 := by decide +kernel
private theorem checked50 : IndexCertificate 50 := ⟨mass50, packed50, fun _ => sign50⟩

private theorem mass51 : massAt 52 = 2 * nestedSum 51 massAt 51 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed51 : packedAt 52 = (1 + digitBase) * nestedSum 51 packedAt 51 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign51 : SignCertificate 51 := by decide +kernel
private theorem checked51 : IndexCertificate 51 := ⟨mass51, packed51, fun _ => sign51⟩

private theorem mass52 : massAt 53 = 2 * nestedSum 52 massAt 52 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed52 : packedAt 53 = (1 + digitBase) * nestedSum 52 packedAt 52 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign52 : SignCertificate 52 := by decide +kernel
private theorem checked52 : IndexCertificate 52 := ⟨mass52, packed52, fun _ => sign52⟩

private theorem mass53 : massAt 54 = 2 * nestedSum 53 massAt 53 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed53 : packedAt 54 = (1 + digitBase) * nestedSum 53 packedAt 53 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign53 : SignCertificate 53 := by decide +kernel
private theorem checked53 : IndexCertificate 53 := ⟨mass53, packed53, fun _ => sign53⟩

private theorem mass54 : massAt 55 = 2 * nestedSum 54 massAt 54 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed54 : packedAt 55 = (1 + digitBase) * nestedSum 54 packedAt 54 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign54 : SignCertificate 54 := by decide +kernel
private theorem checked54 : IndexCertificate 54 := ⟨mass54, packed54, fun _ => sign54⟩

private theorem mass55 : massAt 56 = 2 * nestedSum 55 massAt 55 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed55 : packedAt 56 = (1 + digitBase) * nestedSum 55 packedAt 55 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign55 : SignCertificate 55 := by decide +kernel
private theorem checked55 : IndexCertificate 55 := ⟨mass55, packed55, fun _ => sign55⟩

private theorem mass56 : massAt 57 = 2 * nestedSum 56 massAt 56 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed56 : packedAt 57 = (1 + digitBase) * nestedSum 56 packedAt 56 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign56 : SignCertificate 56 := by decide +kernel
private theorem checked56 : IndexCertificate 56 := ⟨mass56, packed56, fun _ => sign56⟩

private theorem mass57 : massAt 58 = 2 * nestedSum 57 massAt 57 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed57 : packedAt 58 = (1 + digitBase) * nestedSum 57 packedAt 57 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign57 : SignCertificate 57 := by decide +kernel
private theorem checked57 : IndexCertificate 57 := ⟨mass57, packed57, fun _ => sign57⟩

private theorem mass58 : massAt 59 = 2 * nestedSum 58 massAt 58 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed58 : packedAt 59 = (1 + digitBase) * nestedSum 58 packedAt 58 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign58 : SignCertificate 58 := by decide +kernel
private theorem checked58 : IndexCertificate 58 := ⟨mass58, packed58, fun _ => sign58⟩

private theorem mass59 : massAt 60 = 2 * nestedSum 59 massAt 59 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed59 : packedAt 60 = (1 + digitBase) * nestedSum 59 packedAt 59 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign59 : SignCertificate 59 := by decide +kernel
private theorem checked59 : IndexCertificate 59 := ⟨mass59, packed59, fun _ => sign59⟩

private theorem mass60 : massAt 61 = 2 * nestedSum 60 massAt 60 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed60 : packedAt 61 = (1 + digitBase) * nestedSum 60 packedAt 60 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign60 : SignCertificate 60 := by decide +kernel
private theorem checked60 : IndexCertificate 60 := ⟨mass60, packed60, fun _ => sign60⟩

private theorem mass61 : massAt 62 = 2 * nestedSum 61 massAt 61 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed61 : packedAt 62 = (1 + digitBase) * nestedSum 61 packedAt 61 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign61 : SignCertificate 61 := by decide +kernel
private theorem checked61 : IndexCertificate 61 := ⟨mass61, packed61, fun _ => sign61⟩

private theorem mass62 : massAt 63 = 2 * nestedSum 62 massAt 62 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed62 : packedAt 63 = (1 + digitBase) * nestedSum 62 packedAt 62 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign62 : SignCertificate 62 := by decide +kernel
private theorem checked62 : IndexCertificate 62 := ⟨mass62, packed62, fun _ => sign62⟩

private theorem mass63 : massAt 64 = 2 * nestedSum 63 massAt 63 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed63 : packedAt 64 = (1 + digitBase) * nestedSum 63 packedAt 63 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign63 : SignCertificate 63 := by decide +kernel
private theorem checked63 : IndexCertificate 63 := ⟨mass63, packed63, fun _ => sign63⟩

theorem certificates032To063 (n : ℕ) (hn : 32 ≤ n) (hn' : n ≤ 63) : IndexCertificate n := by
  interval_cases n
  · exact checked32
  · exact checked33
  · exact checked34
  · exact checked35
  · exact checked36
  · exact checked37
  · exact checked38
  · exact checked39
  · exact checked40
  · exact checked41
  · exact checked42
  · exact checked43
  · exact checked44
  · exact checked45
  · exact checked46
  · exact checked47
  · exact checked48
  · exact checked49
  · exact checked50
  · exact checked51
  · exact checked52
  · exact checked53
  · exact checked54
  · exact checked55
  · exact checked56
  · exact checked57
  · exact checked58
  · exact checked59
  · exact checked60
  · exact checked61
  · exact checked62
  · exact checked63

end PlanePartition
