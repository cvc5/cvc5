(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 bv0[4])
(flet ($n2 (bvule v0 ?n1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 (sign_extend[3] ?n5))
(let (?n7 (bvmul v1 ?n6))
(let (?n8 (bvsub v0 ?n7))
(flet ($n9 (distinct ?n7 ?n8))
$n9
))))))))))
