import TR23.CWRow0
import TR23.CWRow1
import TR23.CWRow2
import TR23.CWRow3
import TR23.CWRow4
import TR23.CWRow5
import TR23.CWRow6
import TR23.CWRow7
import TR23.CWRow8

namespace TR23

theorem cwCertificate : CWCertificate where
  identity := by
    intro t ht i j k
    fin_cases i
    · exact cw_row0 t ht j k
    · exact cw_row1 t ht j k
    · exact cw_row2 t ht j k
    · exact cw_row3 t ht j k
    · exact cw_row4 t ht j k
    · exact cw_row5 t ht j k
    · exact cw_row6 t ht j k
    · exact cw_row7 t ht j k
    · exact cw_row8 t ht j k
  constant_term := by
    intro i j k
    simp [cwRegular]

end TR23
