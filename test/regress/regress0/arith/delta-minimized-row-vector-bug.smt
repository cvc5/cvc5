(benchmark delta_minimized_row_vector_bug.smt
:logic QF_LRA
:extrafuns ((x_120 Real))
:extrafuns ((x_11 Real))
:extrafuns ((x_102 Real))
:status sat
:formula
  (and (>= x_11 0)
    (or (= x_120 x_102) (<= x_102 (~ x_11)) (= x_120 (+ x_102 x_11) ))
  )

)
