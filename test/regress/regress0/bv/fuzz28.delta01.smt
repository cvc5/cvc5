(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status sat
:formula
(let (?n1 (bvnot v0))
(let (?n2 bv1[4])
(let (?n3 (bvadd ?n1 ?n2))
(let (?n4 (extract[0:0] ?n3))
(let (?n5 bv0[1])
(flet ($n6 (= ?n4 ?n5))
$n6
)))))))
