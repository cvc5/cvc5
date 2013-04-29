(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v2 BitVec[9]))
:status unsat
:formula
(let (?n1 bv0[2])
(let (?n2 bv0[6])
(flet ($n3 (bvult v2 v2))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (concat ?n2 ?n6))
(let (?n8 bv0[7])
(let (?n9 (bvcomp ?n7 ?n8))
(let (?n10 (zero_extend[1] ?n9))
(flet ($n11 (= ?n1 ?n10))
$n11
))))))))))))
