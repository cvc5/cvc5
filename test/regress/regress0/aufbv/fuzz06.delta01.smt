(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((a5 Array[6:11]))
:extrafuns ((v2 BitVec[1]))
:status sat
:formula
(let (?n1 bv0[11])
(let (?n2 (sign_extend[9] v2))
(let (?n3 (extract[7:2] ?n2))
(let (?n4 (select a5 ?n3))
(flet ($n5 (= ?n1 ?n4))
(let (?n6 bv0[6])
(let (?n7 (select a5 ?n6))
(flet ($n8 (bvule ?n7 ?n1))
(flet ($n9 (implies $n5 $n8))
$n9
))))))))))
