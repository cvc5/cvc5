(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v2 BitVec[4]))
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 bv1[1])
(let (?n2 bv0[4])
(flet ($n3 (bvslt ?n2 v1))
(let (?n4 bv0[1])
(let (?n5 (ite $n3 ?n1 ?n4))
(let (?n6 (sign_extend[3] ?n5))
(flet ($n7 (bvsgt ?n2 ?n6))
(let (?n8 (ite $n7 ?n1 ?n4))
(flet ($n9 (= v2 ?n2))
(let (?n10 (ite $n9 ?n1 ?n4))
(flet ($n11 (bvsle ?n4 ?n10))
(let (?n12 (ite $n11 ?n1 ?n4))
(let (?n13 (bvand ?n8 ?n12))
(let (?n14 (bvsub ?n1 ?n13))
(flet ($n15 (= ?n1 ?n14))
$n15
))))))))))))))))
