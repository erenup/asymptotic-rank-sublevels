import TR23.CWDefinitions

namespace TR23

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cw_row1 (t : ℂ) (ht : t ≠ 0) (j k : CWCoord) :
    cwFamily t 1 j k = cwRegular t 1 j k := by
  fin_cases j <;> fin_cases k
  all_goals
    norm_num [cwFamily, cwScalar, cwVector, cwRegular, cwHead, cwSum,
      cwBasis, cw8, cwRemainder, Fin.sum_univ_succ]
    field_simp
    <;> ring

end TR23
