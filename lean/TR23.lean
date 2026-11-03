import TR23.Statement
import TR23.Geometry
import TR23.Exchange
import TR23.CWIdentity

namespace TR23

theorem finiteCertificate : FiniteCertificate where
  geometry := Geometry.geometryCertificate
  exchange := Exchange.exchangeCertificate
  cw_identity := cwCertificate
  permutation_bridge := by
    intro i j k
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
  threshold_lower := by norm_num
  threshold_upper := by norm_num
  tight_gain := by norm_num

end TR23
