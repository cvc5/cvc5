(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status sat
:formula
(let (?n1 bv0[4])
(flet ($n2 (bvslt v0 ?n1))
(let (?n3 bv1[1])
(let (?n4 bv0[1])
(let (?n5 (ite $n2 ?n3 ?n4))
(let (?n6 (bvneg ?n5))
(let (?n7 (bvnot ?n5))
(flet ($n8 (distinct ?n6 ?n7))
$n8
)))))))))
