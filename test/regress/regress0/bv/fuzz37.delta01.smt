(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 bv1[4])
(flet ($n2 (bvugt ?n1 v1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 (zero_extend[3] ?n5))
(let (?n7 (bvmul v1 ?n6))
(let (?n8 bv0[4])
(let (?n9 (bvsub ?n8 ?n7))
(flet ($n10 (= ?n7 ?n9))
$n10
)))))))))))
