(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[13]))
:status sat
:formula
(let (?n1 bv1[13])
(flet ($n2 (bvult v1 ?n1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 (zero_extend[12] ?n5))
(flet ($n7 (bvuge ?n6 v1))
(let (?n8 (ite $n7 ?n3 ?n4))
(let (?n9 (zero_extend[12] ?n8))
(flet ($n10 (bvult ?n9 ?n1))
(let (?n11 (ite $n10 ?n3 ?n4))
(let (?n12 (sign_extend[5] ?n5))
(let (?n13 bv0[6])
(flet ($n14 (bvsgt ?n12 ?n13))
(let (?n15 (ite $n14 ?n3 ?n4))
(flet ($n16 (= ?n11 ?n15))
$n16
)))))))))))))))))
