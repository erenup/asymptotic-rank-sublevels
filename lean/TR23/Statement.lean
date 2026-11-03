import TR23.GeometryDefinitions
import TR23.ExchangeDefinitions
import TR23.CWDefinitions

namespace TR23

/-- The explicit finite identities and witness geometry for TR-23.
No statement about asymptotic tensor rank or irreducibility is included. -/
structure FiniteCertificate : Prop where
  geometry : Geometry.GeometryCertificate
  exchange : Exchange.ExchangeCertificate
  cw_identity : CWCertificate
  permutation_bridge : ∀ i j k : Fin 3,
    Geometry.P ℤ (Geometry.encode i j k) = Exchange.permutationCoefficient i j k
  threshold_lower : (3 : ℤ) ^ 3 < 62
  threshold_upper : (62 : ℤ) < 4 ^ 3
  tight_gain : (4 : ℤ) ^ 3 < 81

end TR23
