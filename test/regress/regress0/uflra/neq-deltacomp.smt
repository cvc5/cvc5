(benchmark fuzzsmt
:logic QF_UFLRA
:extrafuns ((v2 Real))
:extrafuns ((v1 Real))
:extrafuns ((v0 Real))
:status sat
:formula
(let (?n1 (~ v1))
(flet ($n2 (>= ?n1 v0))
(let (?n3 1)
(let (?n4 (ite $n2 v1 ?n3))
(flet ($n5 (<= ?n4 v2))
$n5
))))))
