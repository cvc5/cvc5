(benchmark delta
:logic QF_UFLIA
:extrafuns ((f Int Int))
:extrafuns ((x Int))
:status sat
:formula
(not (= x (f 0)))
)
