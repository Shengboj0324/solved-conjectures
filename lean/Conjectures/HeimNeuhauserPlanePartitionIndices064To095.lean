import Conjectures.HeimNeuhauserPlanePartitionCertificate
import Conjectures.HeimNeuhauserPlanePartitionFastSum

/-! Exact recurrence and sign certificates at indices 64 through 95. -/

namespace PlanePartition

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

private theorem mass64 : massAt 65 = 2 * nestedSum 64 massAt 64 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed64 : packedAt 65 = (1 + digitBase) * nestedSum 64 packedAt 64 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign64 : SignCertificate 64 := by decide +kernel
private theorem checked64 : IndexCertificate 64 := ⟨mass64, packed64, fun _ => sign64⟩

private theorem mass65 : massAt 66 = 2 * nestedSum 65 massAt 65 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed65 : packedAt 66 = (1 + digitBase) * nestedSum 65 packedAt 65 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign65 : SignCertificate 65 := by decide +kernel
private theorem checked65 : IndexCertificate 65 := ⟨mass65, packed65, fun _ => sign65⟩

private theorem mass66 : massAt 67 = 2 * nestedSum 66 massAt 66 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed66 : packedAt 67 = (1 + digitBase) * nestedSum 66 packedAt 66 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign66 : SignCertificate 66 := by decide +kernel
private theorem checked66 : IndexCertificate 66 := ⟨mass66, packed66, fun _ => sign66⟩

private theorem mass67 : massAt 68 = 2 * nestedSum 67 massAt 67 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed67 : packedAt 68 = (1 + digitBase) * nestedSum 67 packedAt 67 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign67 : SignCertificate 67 := by decide +kernel
private theorem checked67 : IndexCertificate 67 := ⟨mass67, packed67, fun _ => sign67⟩

private theorem mass68 : massAt 69 = 2 * nestedSum 68 massAt 68 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed68 : packedAt 69 = (1 + digitBase) * nestedSum 68 packedAt 68 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign68 : SignCertificate 68 := by decide +kernel
private theorem checked68 : IndexCertificate 68 := ⟨mass68, packed68, fun _ => sign68⟩

private theorem mass69 : massAt 70 = 2 * nestedSum 69 massAt 69 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed69 : packedAt 70 = (1 + digitBase) * nestedSum 69 packedAt 69 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign69 : SignCertificate 69 := by decide +kernel
private theorem checked69 : IndexCertificate 69 := ⟨mass69, packed69, fun _ => sign69⟩

private theorem mass70 : massAt 71 = 2 * nestedSum 70 massAt 70 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed70 : packedAt 71 = (1 + digitBase) * nestedSum 70 packedAt 70 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign70 : SignCertificate 70 := by decide +kernel
private theorem checked70 : IndexCertificate 70 := ⟨mass70, packed70, fun _ => sign70⟩

private theorem mass71 : massAt 72 = 2 * nestedSum 71 massAt 71 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed71 : packedAt 72 = (1 + digitBase) * nestedSum 71 packedAt 71 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign71 : SignCertificate 71 := by decide +kernel
private theorem checked71 : IndexCertificate 71 := ⟨mass71, packed71, fun _ => sign71⟩

private theorem mass72 : massAt 73 = 2 * nestedSum 72 massAt 72 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed72 : packedAt 73 = (1 + digitBase) * nestedSum 72 packedAt 72 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign72 : SignCertificate 72 := by decide +kernel
private theorem checked72 : IndexCertificate 72 := ⟨mass72, packed72, fun _ => sign72⟩

private theorem mass73 : massAt 74 = 2 * nestedSum 73 massAt 73 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed73 : packedAt 74 = (1 + digitBase) * nestedSum 73 packedAt 73 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign73 : SignCertificate 73 := by decide +kernel
private theorem checked73 : IndexCertificate 73 := ⟨mass73, packed73, fun _ => sign73⟩

private theorem mass74 : massAt 75 = 2 * nestedSum 74 massAt 74 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed74 : packedAt 75 = (1 + digitBase) * nestedSum 74 packedAt 74 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign74 : SignCertificate 74 := by decide +kernel
private theorem checked74 : IndexCertificate 74 := ⟨mass74, packed74, fun _ => sign74⟩

private theorem mass75 : massAt 76 = 2 * nestedSum 75 massAt 75 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed75 : packedAt 76 = (1 + digitBase) * nestedSum 75 packedAt 75 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign75 : SignCertificate 75 := by decide +kernel
private theorem checked75 : IndexCertificate 75 := ⟨mass75, packed75, fun _ => sign75⟩

private theorem mass76 : massAt 77 = 2 * nestedSum 76 massAt 76 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed76 : packedAt 77 = (1 + digitBase) * nestedSum 76 packedAt 76 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign76 : SignCertificate 76 := by decide +kernel
private theorem checked76 : IndexCertificate 76 := ⟨mass76, packed76, fun _ => sign76⟩

private theorem mass77 : massAt 78 = 2 * nestedSum 77 massAt 77 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed77 : packedAt 78 = (1 + digitBase) * nestedSum 77 packedAt 77 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign77 : SignCertificate 77 := by decide +kernel
private theorem checked77 : IndexCertificate 77 := ⟨mass77, packed77, fun _ => sign77⟩

private theorem mass78 : massAt 79 = 2 * nestedSum 78 massAt 78 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed78 : packedAt 79 = (1 + digitBase) * nestedSum 78 packedAt 78 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign78 : SignCertificate 78 := by decide +kernel
private theorem checked78 : IndexCertificate 78 := ⟨mass78, packed78, fun _ => sign78⟩

private theorem mass79 : massAt 80 = 2 * nestedSum 79 massAt 79 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed79 : packedAt 80 = (1 + digitBase) * nestedSum 79 packedAt 79 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign79 : SignCertificate 79 := by decide +kernel
private theorem checked79 : IndexCertificate 79 := ⟨mass79, packed79, fun _ => sign79⟩

private theorem mass80 : massAt 81 = 2 * nestedSum 80 massAt 80 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed80 : packedAt 81 = (1 + digitBase) * nestedSum 80 packedAt 80 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign80 : SignCertificate 80 := by decide +kernel
private theorem checked80 : IndexCertificate 80 := ⟨mass80, packed80, fun _ => sign80⟩

private theorem mass81 : massAt 82 = 2 * nestedSum 81 massAt 81 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed81 : packedAt 82 = (1 + digitBase) * nestedSum 81 packedAt 81 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign81 : SignCertificate 81 := by decide +kernel
private theorem checked81 : IndexCertificate 81 := ⟨mass81, packed81, fun _ => sign81⟩

private theorem mass82 : massAt 83 = 2 * nestedSum 82 massAt 82 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed82 : packedAt 83 = (1 + digitBase) * nestedSum 82 packedAt 82 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign82 : SignCertificate 82 := by decide +kernel
private theorem checked82 : IndexCertificate 82 := ⟨mass82, packed82, fun _ => sign82⟩

private theorem mass83 : massAt 84 = 2 * nestedSum 83 massAt 83 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed83 : packedAt 84 = (1 + digitBase) * nestedSum 83 packedAt 83 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign83 : SignCertificate 83 := by decide +kernel
private theorem checked83 : IndexCertificate 83 := ⟨mass83, packed83, fun _ => sign83⟩

private theorem mass84 : massAt 85 = 2 * nestedSum 84 massAt 84 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed84 : packedAt 85 = (1 + digitBase) * nestedSum 84 packedAt 84 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign84 : SignCertificate 84 := by decide +kernel
private theorem checked84 : IndexCertificate 84 := ⟨mass84, packed84, fun _ => sign84⟩

private theorem mass85 : massAt 86 = 2 * nestedSum 85 massAt 85 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed85 : packedAt 86 = (1 + digitBase) * nestedSum 85 packedAt 85 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign85 : SignCertificate 85 := by decide +kernel
private theorem checked85 : IndexCertificate 85 := ⟨mass85, packed85, fun _ => sign85⟩

private theorem mass86 : massAt 87 = 2 * nestedSum 86 massAt 86 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed86 : packedAt 87 = (1 + digitBase) * nestedSum 86 packedAt 86 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign86 : SignCertificate 86 := by decide +kernel
private theorem checked86 : IndexCertificate 86 := ⟨mass86, packed86, fun _ => sign86⟩

private theorem mass87 : massAt 88 = 2 * nestedSum 87 massAt 87 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed87 : packedAt 88 = (1 + digitBase) * nestedSum 87 packedAt 87 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign87 : SignCertificate 87 := by decide +kernel
private theorem checked87 : IndexCertificate 87 := ⟨mass87, packed87, fun _ => sign87⟩

private theorem mass88 : massAt 89 = 2 * nestedSum 88 massAt 88 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed88 : packedAt 89 = (1 + digitBase) * nestedSum 88 packedAt 88 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign88 : SignCertificate 88 := by decide +kernel
private theorem checked88 : IndexCertificate 88 := ⟨mass88, packed88, fun _ => sign88⟩

private theorem mass89 : massAt 90 = 2 * nestedSum 89 massAt 89 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed89 : packedAt 90 = (1 + digitBase) * nestedSum 89 packedAt 89 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign89 : SignCertificate 89 := by decide +kernel
private theorem checked89 : IndexCertificate 89 := ⟨mass89, packed89, fun _ => sign89⟩

private theorem mass90 : massAt 91 = 2 * nestedSum 90 massAt 90 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed90 : packedAt 91 = (1 + digitBase) * nestedSum 90 packedAt 90 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign90 : SignCertificate 90 := by decide +kernel
private theorem checked90 : IndexCertificate 90 := ⟨mass90, packed90, fun _ => sign90⟩

private theorem mass91 : massAt 92 = 2 * nestedSum 91 massAt 91 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed91 : packedAt 92 = (1 + digitBase) * nestedSum 91 packedAt 91 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign91 : SignCertificate 91 := by decide +kernel
private theorem checked91 : IndexCertificate 91 := ⟨mass91, packed91, fun _ => sign91⟩

private theorem mass92 : massAt 93 = 2 * nestedSum 92 massAt 92 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed92 : packedAt 93 = (1 + digitBase) * nestedSum 92 packedAt 92 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign92 : SignCertificate 92 := by decide +kernel
private theorem checked92 : IndexCertificate 92 := ⟨mass92, packed92, fun _ => sign92⟩

private theorem mass93 : massAt 94 = 2 * nestedSum 93 massAt 93 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed93 : packedAt 94 = (1 + digitBase) * nestedSum 93 packedAt 93 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign93 : SignCertificate 93 := by decide +kernel
private theorem checked93 : IndexCertificate 93 := ⟨mass93, packed93, fun _ => sign93⟩

private theorem mass94 : massAt 95 = 2 * nestedSum 94 massAt 94 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed94 : packedAt 95 = (1 + digitBase) * nestedSum 94 packedAt 94 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign94 : SignCertificate 94 := by decide +kernel
private theorem checked94 : IndexCertificate 94 := ⟨mass94, packed94, fun _ => sign94⟩

private theorem mass95 : massAt 96 = 2 * nestedSum 95 massAt 95 := by
  rw [nestedSum_massAt _ _ (by norm_num)]; decide +kernel
private theorem packed95 : packedAt 96 = (1 + digitBase) * nestedSum 95 packedAt 95 := by
  rw [nestedSum_packedAt _ _ (by norm_num)]; decide +kernel
private theorem sign95 : SignCertificate 95 := by decide +kernel
private theorem checked95 : IndexCertificate 95 := ⟨mass95, packed95, fun _ => sign95⟩

theorem certificates064To095 (n : ℕ) (hn : 64 ≤ n) (hn' : n ≤ 95) : IndexCertificate n := by
  interval_cases n
  · exact checked64
  · exact checked65
  · exact checked66
  · exact checked67
  · exact checked68
  · exact checked69
  · exact checked70
  · exact checked71
  · exact checked72
  · exact checked73
  · exact checked74
  · exact checked75
  · exact checked76
  · exact checked77
  · exact checked78
  · exact checked79
  · exact checked80
  · exact checked81
  · exact checked82
  · exact checked83
  · exact checked84
  · exact checked85
  · exact checked86
  · exact checked87
  · exact checked88
  · exact checked89
  · exact checked90
  · exact checked91
  · exact checked92
  · exact checked93
  · exact checked94
  · exact checked95

end PlanePartition
