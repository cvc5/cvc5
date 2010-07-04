(benchmark gasburner_prop3_15.smt
:logic QF_LRA
:extrafuns ((x_98 Real))
:status sat
:formula
(let (?n1 0)
(flet ($n2 (>= x_98 ?n1))
(let (?n3 1)
(flet ($n4 (<= x_98 ?n3))
(flet ($n5 (and $n2 $n4))
$n5
))))))
