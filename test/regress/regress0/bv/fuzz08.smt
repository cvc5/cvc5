(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[9]))
:status sat
:formula
(let (?n1 bv0[6])
(let (?n2 bv0[9])
(flet ($n3 (bvult ?n2 v1))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (sign_extend[5] ?n6))
(flet ($n8 (bvsgt ?n1 ?n7))
(let (?n9 (ite $n8 ?n4 ?n5))
(let (?n10 (sign_extend[8] ?n9))
(let (?n11 (bvcomp v1 ?n10))
(flet ($n12 (= ?n9 ?n11))
$n12
)))))))))))))
