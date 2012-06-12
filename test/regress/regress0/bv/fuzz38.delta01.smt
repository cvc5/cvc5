(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[1]))
:status unsat
:formula
(let (?n1 bv416[10])
(let (?n2 (zero_extend[9] v1))
(flet ($n3 (bvsgt ?n2 ?n2))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (zero_extend[9] ?n6))
(let (?n8 (bvmul ?n1 ?n7))
(let (?n9 (sign_extend[9] v1))
(let (?n10 (bvmul ?n8 ?n9))
(let (?n11 bv0[10])
(flet ($n12 (= ?n10 ?n11))
(flet ($n13 (not $n12))
$n13
))))))))))))))
