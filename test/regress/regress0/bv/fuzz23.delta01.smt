(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v1 BitVec[4]))
:status sat
:formula
(let (?n1 bv1[1])
(let (?n2 (bvnot v1))
(let (?n3 bv1[4])
(let (?n4 (bvsub ?n2 ?n3))
(let (?n5 (extract[0:0] ?n4))
(flet ($n6 (= ?n1 ?n5))
$n6
)))))))
