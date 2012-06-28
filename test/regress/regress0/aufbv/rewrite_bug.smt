(benchmark B_
:logic QF_AUFBV
:extrafuns ((a Array[32:8]))
:status sat
:formula
(flet ($n1 true)
(let (?n2 bv0[8])
(let (?n3 (sign_extend[24] ?n2))
(let (?n4 bv1[32])
(let (?n5 bv1[8])
(let (?n6 (store a ?n4 ?n5))
(let (?n7 bv0[32])
(let (?n8 (select a ?n4))
(let (?n9 (sign_extend[24] ?n8))
(let (?n10 (extract[7:0] ?n9))
(let (?n11 (store ?n6 ?n7 ?n10))
(let (?n12 (select ?n11 ?n4))
(let (?n13 (store ?n11 ?n4 ?n12))
(let (?n14 (select ?n13 ?n7))
(let (?n15 (sign_extend[24] ?n14))
(flet ($n16 (bvslt ?n3 ?n15))
(flet ($n17 (not $n16))
(let (?n18 (select ?n13 ?n4))
(let (?n19 (sign_extend[24] ?n18))
(flet ($n20 (bvslt ?n7 ?n19))
(flet ($n21 (and $n1 $n1 $n1 $n1 $n17 $n20))
$n21
))))))))))))))))))))))
