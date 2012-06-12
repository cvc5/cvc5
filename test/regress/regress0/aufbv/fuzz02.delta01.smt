(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((a5 Array[5:13]))
:extrafuns ((v4 BitVec[11]))
:status sat
:formula
(let (?n1 bv0[11])
(flet ($n2 (bvsle v4 ?n1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 bv0[5])
(let (?n7 (select a5 ?n6))
(let (?n8 bv0[13])
(flet ($n9 (bvugt ?n7 ?n8))
(let (?n10 (ite $n9 ?n3 ?n4))
(flet ($n11 (bvslt ?n5 ?n10))
$n11
))))))))))))
