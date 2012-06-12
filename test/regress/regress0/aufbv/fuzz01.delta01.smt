(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v1 BitVec[3]))
:extrafuns ((v2 BitVec[11]))
:extrafuns ((a9 Array[8:5]))
:extrafuns ((a6 Array[1:13]))
:status sat
:formula
(let (?n1 bv0[15])
(let (?n2 bv0[1])
(let (?n3 (zero_extend[8] v1))
(let (?n4 (bvnor v2 ?n3))
(let (?n5 (extract[7:0] ?n4))
(let (?n6 bv0[5])
(let (?n7 (store a9 ?n5 ?n6))
(let (?n8 bv0[8])
(let (?n9 (select ?n7 ?n8))
(let (?n10 (zero_extend[8] ?n9))
(let (?n11 (store a6 ?n2 ?n10))
(let (?n12 (extract[0:0] ?n4))
(let (?n13 (select ?n11 ?n12))
(let (?n14 (zero_extend[2] ?n13))
(flet ($n15 (= ?n1 ?n14))
$n15
))))))))))))))))
