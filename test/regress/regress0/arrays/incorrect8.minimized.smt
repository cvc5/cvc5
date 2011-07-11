(benchmark fuzzsmt
:logic QF_AX
:extrafuns ((v4 Index))
:extrafuns ((v3 Index))
:extrafuns ((v5 Element))
:extrafuns ((v1 Array))
:status unsat
:formula
(let (?n1 (store v1 v4 v5))
(let (?n2 (select ?n1 v3))
(let (?n3 (select v1 v3))
(flet ($n4 (distinct ?n2 ?n3))
(let (?n5 (ite $n4 v4 v3))
(let (?n6 (store ?n1 v4 v5))
(let (?n7 (select ?n6 v3))
(flet ($n8 (= ?n2 ?n7))
(let (?n9 (ite $n8 v3 v4))
(flet ($n10 (distinct ?n5 ?n9))
$n10
)))))))))))
