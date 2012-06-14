(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v0 BitVec[16]))
:extrafuns ((a2 Array[16:7]))
:status sat
:formula
(let (?n1 bv0[7])
(let (?n2 (store a2 v0 ?n1))
(let (?n3 bv1[16])
(let (?n4 (select ?n2 ?n3))
(flet ($n5 (bvult ?n1 ?n4))
(let (?n6 bv1[1])
(let (?n7 bv0[1])
(let (?n8 (ite $n5 ?n6 ?n7))
(let (?n9 (sign_extend[15] ?n8))
(flet ($n10 (distinct v0 ?n9))
(flet ($n11 (not $n10))
$n11
))))))))))))
