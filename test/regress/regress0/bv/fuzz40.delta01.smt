(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status sat
:formula
(let (?n1 bv1[4])
(let (?n2 (bvmul ?n1 v0))
(let (?n3 (extract[3:0] ?n2))
(let (?n4 bv0[4])
(flet ($n5 (bvsge ?n3 ?n4))
$n5
))))))
