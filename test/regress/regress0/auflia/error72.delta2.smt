(benchmark fuzzsmt
:logic QF_AUFLIA
:extrafuns ((v1 Int))
:status sat
:formula
(let (?n1 0)
(flet ($n2 (distinct v1 ?n1))
(let (?n3 (ite $n2 v1 ?n1))
(let (?n4 (~ ?n3))
(flet ($n5 (>= ?n4 ?n1))
$n5
))))))
