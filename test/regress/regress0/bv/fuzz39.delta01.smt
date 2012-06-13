(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v2 BitVec[14]))
:status sat
:formula
(let (?n1 bv2692[12])
(let (?n2 bv1[14])
(flet ($n3 (bvugt ?n2 v2))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (sign_extend[11] ?n6))
(let (?n8 (bvsub ?n1 ?n7))
(let (?n9 (bvmul ?n1 ?n8))
(let (?n10 bv1[12])
(flet ($n11 (bvuge ?n9 ?n10))
$n11
))))))))))))
