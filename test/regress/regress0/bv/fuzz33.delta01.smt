(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status sat
:formula
(let (?n1 bv0[1])
(let (?n2 bv1[4])
(let (?n3 (bvnot v0))
(let (?n4 (bvadd ?n2 ?n3))
(let (?n5 (extract[0:0] ?n4))
(flet ($n6 (= ?n1 ?n5))
$n6
)))))))
