(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v2 BitVec[4]))
:status unsat
:formula
(let (?n1 bv1[1])
(let (?n2 bv0[4])
(flet ($n3 (distinct v2 ?n2))
(let (?n4 bv0[1])
(let (?n5 (ite $n3 ?n1 ?n4))
(let (?n6 (zero_extend[3] ?n5))
(flet ($n7 (bvslt ?n6 ?n2))
(let (?n8 (ite $n7 ?n1 ?n4))
(let (?n9 (bvnot ?n8))
(let (?n10 (bvsub ?n1 ?n9))
(flet ($n11 (= ?n1 ?n10))
$n11
))))))))))))
