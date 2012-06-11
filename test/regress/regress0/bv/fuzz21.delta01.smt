(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 (bvmul v1 v1))
(let (?n2 bv0[4])
(let (?n3 (bvsub ?n2 ?n1))
(flet ($n4 (distinct ?n1 ?n3))
$n4
)))))
