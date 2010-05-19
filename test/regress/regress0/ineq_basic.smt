(benchmark ineq_basic
:status unsat
:logic QF_LRA
:extrafuns ((x Real))
:formula
 (and (<= 0 x)
      (< x 0)
 )
)
