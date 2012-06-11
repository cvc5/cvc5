(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status unsat
:formula
(let (?n1 bv0[4])
(flet ($n2 (bvslt v1 ?n1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 (bvnot ?n5))
(let (?n7 (bvneg ?n5))
(flet ($n8 (= ?n6 ?n7))
$n8
)))))))))
