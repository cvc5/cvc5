(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v2 BitVec[4]))
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 (bvmul v1 v2))
(let (?n2 (bvneg ?n1))
(flet ($n3 (distinct ?n1 ?n2))
$n3
))))
