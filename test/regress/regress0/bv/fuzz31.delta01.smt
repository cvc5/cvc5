(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 bv8[4])
(let (?n2 bv12[4])
(let (?n3 (repeat[1] ?n2))
(flet ($n4 (bvule ?n1 v1))
(let (?n5 bv1[1])
(let (?n6 bv0[1])
(let (?n7 (ite $n4 ?n5 ?n6))
(let (?n8 (sign_extend[3] ?n7))
(let (?n9 (bvmul ?n3 ?n8))
(let (?n10 (bvmul ?n1 ?n9))
(let (?n11 bv0[4])
(flet ($n12 (= ?n10 ?n11))
$n12
)))))))))))))
