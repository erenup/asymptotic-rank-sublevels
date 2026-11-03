import TR23.GeometryRows
import TR23.GeometryRank
import TR23.GeometryWitnesses

namespace TR23.Geometry

/-- Exact finite geometry facts for the TR-23 coordinate definitions. -/
theorem geometryCertificate : GeometryCertificate where
  row_enumeration := rows_complete
  appended_minor_identity := appended_minor_identity
  self_kernel := self_kernel
  P_flattening_rank := witness_P_flattening_rank
  P_minor_rank := P_minor_rank
  P_kernel := P_kernel
  x_fourth_rank := witness_x_fourth_rank
  y_fourth_rank := witness_y_fourth_rank
  y_balanced_rank := witness_y_balanced_rank
  y_outside_rank_one := witness_y_outside_rank_one
  basis_determinant := witness_basis_determinant
  basis_nonsingular := witness_basis_nonsingular
  basis_image := witness_basis_image

end TR23.Geometry
