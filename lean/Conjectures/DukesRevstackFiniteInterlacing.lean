import Conjectures.DukesRevstackFiniteCuts003To007
import Conjectures.DukesRevstackFiniteCuts008To015
import Conjectures.DukesRevstackFiniteCuts016To023
import Conjectures.DukesRevstackFiniteCuts024To031
import Conjectures.DukesRevstackFiniteCuts032To039
import Conjectures.DukesRevstackFiniteCuts040To047
import Conjectures.DukesRevstackFiniteCuts048To055
import Conjectures.DukesRevstackFiniteCuts056To063
import Conjectures.DukesRevstackFiniteCuts064To071
import Conjectures.DukesRevstackFiniteCuts072To079
import Conjectures.DukesRevstackFiniteCuts080To087
import Conjectures.DukesRevstackFiniteCuts088To095
import Conjectures.DukesRevstackFiniteCuts096To103
import Conjectures.DukesRevstackFiniteCuts104To111
import Conjectures.DukesRevstackFiniteCuts112To119
import Conjectures.DukesRevstackFiniteCuts120To127
import Mathlib.Tactic.IntervalCases

/-! Strict interlacing of the literal descent polynomials at every consecutive
pair of orders in the exact finite part of the revstack proof. -/

namespace DukesRevstack

theorem finite_interlacing (n : ℕ) (lo : 3≤n) (hi : n≤127) : literalInterlaces n := by
  interval_cases n
  · exact FiniteData.literal003
  · exact FiniteData.literal004
  · exact FiniteData.literal005
  · exact FiniteData.literal006
  · exact FiniteData.literal007
  · exact FiniteData.literal008
  · exact FiniteData.literal009
  · exact FiniteData.literal010
  · exact FiniteData.literal011
  · exact FiniteData.literal012
  · exact FiniteData.literal013
  · exact FiniteData.literal014
  · exact FiniteData.literal015
  · exact FiniteData.literal016
  · exact FiniteData.literal017
  · exact FiniteData.literal018
  · exact FiniteData.literal019
  · exact FiniteData.literal020
  · exact FiniteData.literal021
  · exact FiniteData.literal022
  · exact FiniteData.literal023
  · exact FiniteData.literal024
  · exact FiniteData.literal025
  · exact FiniteData.literal026
  · exact FiniteData.literal027
  · exact FiniteData.literal028
  · exact FiniteData.literal029
  · exact FiniteData.literal030
  · exact FiniteData.literal031
  · exact FiniteData.literal032
  · exact FiniteData.literal033
  · exact FiniteData.literal034
  · exact FiniteData.literal035
  · exact FiniteData.literal036
  · exact FiniteData.literal037
  · exact FiniteData.literal038
  · exact FiniteData.literal039
  · exact FiniteData.literal040
  · exact FiniteData.literal041
  · exact FiniteData.literal042
  · exact FiniteData.literal043
  · exact FiniteData.literal044
  · exact FiniteData.literal045
  · exact FiniteData.literal046
  · exact FiniteData.literal047
  · exact FiniteData.literal048
  · exact FiniteData.literal049
  · exact FiniteData.literal050
  · exact FiniteData.literal051
  · exact FiniteData.literal052
  · exact FiniteData.literal053
  · exact FiniteData.literal054
  · exact FiniteData.literal055
  · exact FiniteData.literal056
  · exact FiniteData.literal057
  · exact FiniteData.literal058
  · exact FiniteData.literal059
  · exact FiniteData.literal060
  · exact FiniteData.literal061
  · exact FiniteData.literal062
  · exact FiniteData.literal063
  · exact FiniteData.literal064
  · exact FiniteData.literal065
  · exact FiniteData.literal066
  · exact FiniteData.literal067
  · exact FiniteData.literal068
  · exact FiniteData.literal069
  · exact FiniteData.literal070
  · exact FiniteData.literal071
  · exact FiniteData.literal072
  · exact FiniteData.literal073
  · exact FiniteData.literal074
  · exact FiniteData.literal075
  · exact FiniteData.literal076
  · exact FiniteData.literal077
  · exact FiniteData.literal078
  · exact FiniteData.literal079
  · exact FiniteData.literal080
  · exact FiniteData.literal081
  · exact FiniteData.literal082
  · exact FiniteData.literal083
  · exact FiniteData.literal084
  · exact FiniteData.literal085
  · exact FiniteData.literal086
  · exact FiniteData.literal087
  · exact FiniteData.literal088
  · exact FiniteData.literal089
  · exact FiniteData.literal090
  · exact FiniteData.literal091
  · exact FiniteData.literal092
  · exact FiniteData.literal093
  · exact FiniteData.literal094
  · exact FiniteData.literal095
  · exact FiniteData.literal096
  · exact FiniteData.literal097
  · exact FiniteData.literal098
  · exact FiniteData.literal099
  · exact FiniteData.literal100
  · exact FiniteData.literal101
  · exact FiniteData.literal102
  · exact FiniteData.literal103
  · exact FiniteData.literal104
  · exact FiniteData.literal105
  · exact FiniteData.literal106
  · exact FiniteData.literal107
  · exact FiniteData.literal108
  · exact FiniteData.literal109
  · exact FiniteData.literal110
  · exact FiniteData.literal111
  · exact FiniteData.literal112
  · exact FiniteData.literal113
  · exact FiniteData.literal114
  · exact FiniteData.literal115
  · exact FiniteData.literal116
  · exact FiniteData.literal117
  · exact FiniteData.literal118
  · exact FiniteData.literal119
  · exact FiniteData.literal120
  · exact FiniteData.literal121
  · exact FiniteData.literal122
  · exact FiniteData.literal123
  · exact FiniteData.literal124
  · exact FiniteData.literal125
  · exact FiniteData.literal126
  · exact FiniteData.literal127

end DukesRevstack
