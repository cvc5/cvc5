(benchmark ite_real_valid
:logic QF_LRA
:status unsat
:extrafuns ((x Real))
:extrapreds ((b))
:formula
  (not (implies (= x (ite b 0 1)) (>= x 0)))
)
