(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[11]))
:status unsat
:formula
(let (?n1 bv0[16])
(let (?n2 (zero_extend[5] v0))
(flet ($n3 (bvsge ?n1 ?n2))
(let (?n4 bv1[1])
(let (?n5 bv0[1])
(let (?n6 (ite $n3 ?n4 ?n5))
(let (?n7 (zero_extend[10] ?n6))
(flet ($n8 (= v0 ?n7))
$n8
)))))))))
