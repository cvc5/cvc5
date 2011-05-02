(benchmark B_
:logic QF_BV
:extrafuns ((a BitVec[32]))
:status sat
:formula
(let (?n1 (extract[6:2] a))
(let (?n2 bv0[3])
(let (?n3 (extract[6:5] a))
(let (?n4 (concat ?n2 ?n3))
(flet ($n5 (= ?n1 ?n4))
$n5
))))))
