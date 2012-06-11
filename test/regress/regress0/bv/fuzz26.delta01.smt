(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status unsat
:formula
(let (?n1 bv0[4])
(let (?n2 bv14[4])
(flet ($n3 (bvslt v1 v1))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (sign_extend[3] ?n6))
(flet ($n8 (= ?n2 ?n7))
(let (?n9 (ite $n8 ?n4 ?n5))
(let (?n10 (zero_extend[3] ?n9))
(let (?n11 (bvcomp ?n1 ?n10))
(let (?n12 (zero_extend[3] ?n11))
(let (?n13 bv8[4])
(let (?n14 (repeat[1] ?n2))
(let (?n15 (bvmul ?n13 ?n14))
(let (?n16 (bvmul ?n12 ?n15))
(flet ($n17 (bvugt ?n16 ?n1))
$n17
))))))))))))))))))
