(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v0 BitVec[16]))
:extrafuns ((v1 BitVec[1]))
:extrafuns ((a4 Array[1:7]))
:status sat
:formula
(let (?n1 (select a4 v1))
(let (?n2 bv0[7])
(flet ($n3 (bvsle ?n1 ?n2))
(let (?n4 bv0[16])
(let (?n5 bv0[1])
(flet ($n6 (= v1 ?n5))
(let (?n7 (ite $n6 ?n4 v0))
(flet ($n8 (= ?n4 ?n7))
(flet ($n9 (not $n8))
(flet ($n10 (and $n3 $n9))
$n10
)))))))))))
