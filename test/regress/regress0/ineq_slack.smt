(benchmark ineq_basic
:status unsat
:logic QF_LRA
:extrafuns ((x Real))
:extrafuns ((y Real))
:formula
 (and (<= (+ x y) 0)
      (< 1 x)
      (<= 0 y)
 )
)
