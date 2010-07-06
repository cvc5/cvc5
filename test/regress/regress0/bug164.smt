(benchmark Carpark2_t1_1.smt
:logic QF_LRA
:extrafuns ((x_34 Real))
:extrafuns ((x_13 Real))
:extrafuns ((x_30 Real))
:extrafuns ((x_59 Real))
:status unsat
:formula
(and (not (<= x_59 0))
     (= x_30 x_59)
     (= x_30 0)
     (or true (= x_13 x_34)))
)
