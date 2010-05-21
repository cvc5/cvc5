(benchmark ite_real_int_type
:logic QF_LRA
:status sat
:extrafuns ((x Real))
:extrafuns ((y Real))
:formula
  (and (= 0 (ite true x 1)) (= 0 (ite (= x 0) 0 1)) (= x  (ite true y 0)) (= 0 (ite true 0 0)) )
)
