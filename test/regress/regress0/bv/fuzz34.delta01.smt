(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status sat
:formula
(let (?n1 bv0[1])
(let (?n2 bv0[4])
(let (?n3 (bvcomp v0 ?n2))
(flet ($n4 (distinct v0 ?n2))
(let (?n5 bv1[1])
(let (?n6 (ite $n4 ?n5 ?n1))
(let (?n7 (zero_extend[3] ?n6))
(flet ($n8 (bvslt ?n7 ?n2))
(let (?n9 (ite $n8 ?n5 ?n1))
(let (?n10 (sign_extend[3] ?n9))
(flet ($n11 (bvslt ?n2 ?n10))
(let (?n12 (ite $n11 ?n5 ?n1))
(let (?n13 (bvor ?n3 ?n12))
(let (?n14 (bvsub ?n13 ?n5))
(flet ($n15 (distinct ?n1 ?n14))
$n15
))))))))))))))))
