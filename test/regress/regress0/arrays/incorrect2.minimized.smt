(benchmark fuzzsmt
:logic QF_AX
:extrafuns ((v3 Index))
:extrafuns ((v4 Index))
:extrafuns ((v2 Index))
:status unsat
:formula
(flet ($n1 true)
(flet ($n2 (= v4 v3))
(flet ($n3 (xor $n1 $n2))
(flet ($n4 (distinct v2 v3))
(let (?n5 (ite $n4 v3 v4))
(let (?n6 (ite $n4 ?n5 v3))
(flet ($n7 (distinct v4 ?n6))
(flet ($n8 false)
(flet ($n9 (if_then_else $n7 $n8 $n1))
(flet ($n10 (and $n3 $n9))
$n10
)))))))))))
