import TR23.CWDefinitions

namespace TR23

theorem cwHead_val (i : CWCoord) :
    cwHead i = if i.val = 0 then 1 else 0 := by
  simp only [cwHead, Fin.ext_iff, Fin.val_zero]

theorem cwSum_val (i : CWCoord) :
    cwSum i = if i.val = 0 then 0 else 1 := by
  simp only [cwSum, Fin.ext_iff, Fin.val_zero]

theorem cw8_val (i j k : CWCoord) :
    cw8 i j k =
      (if i.val = 0 ∧ j.val = k.val ∧ j.val ≠ 0 then 1 else 0) +
      (if j.val = 0 ∧ i.val = k.val ∧ i.val ≠ 0 then 1 else 0) +
      (if k.val = 0 ∧ i.val = j.val ∧ i.val ≠ 0 then 1 else 0) := by
  simp only [cw8, ne_eq, Fin.ext_iff, Fin.val_zero]

theorem cwRemainder_val (i j k : CWCoord) :
    cwRemainder i j k =
      (if i.val = j.val ∧ j.val = k.val ∧ i.val ≠ 0 then 1 else 0) -
      (cwHead i * cwSum j * cwSum k +
       cwSum i * cwHead j * cwSum k +
       cwSum i * cwSum j * cwHead k) := by
  simp only [cwRemainder, ne_eq, Fin.ext_iff, Fin.val_zero]

end TR23
