(benchmark uart
:logic QF_LRA
:extrafuns ((x_1 Real))
:status unsat
:formula
(let (?n1 10)
(flet ($n2 (= x_1 ?n1))
(let (?n3 1)
(flet ($n4 (< x_1 ?n3))
(flet ($n5 (and $n2 $n4))
$n5
))))))
