import TR23.CWArithmetic

namespace TR23

set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem cw_row8 (t : ℂ) (ht : t ≠ 0) (j k : CWCoord) :
    cwFamily t 8 j k = cwRegular t 8 j k := by
  fin_cases j <;> fin_cases k
  all_goals
    norm_num [cwFamily, cwScalar, cwVector, cwRegular, cwHead_val, cwSum_val,
      cwBasis, cw8_val, cwRemainder_val, Fin.sum_univ_succ]
    field_simp
    <;> ring

end TR23
