(benchmark B_
:logic QF_AUFBV
:extrafuns ((R_ESP_1_58 BitVec[32]))
:extrafuns ((mem_35_197 Array[32:8]))
:status sat
:formula
(let (?n1 bv0[32])
(let (?n2 bv0[24])
(let (?n3 bv1[32])
(let (?n4 (bvadd ?n3 R_ESP_1_58))
(let (?n5 bv0[8])
(let (?n6 (store mem_35_197 ?n4 ?n5))
(let (?n7 (bvadd ?n3 ?n4))
(let (?n8 (store ?n6 ?n7 ?n5))
(let (?n9 (store ?n8 ?n1 ?n5))
(let (?n10 (select ?n6 R_ESP_1_58))
(let (?n11 (concat ?n2 ?n10))
(let (?n12 (bvadd ?n3 ?n11))
(let (?n13 (select ?n9 ?n12))
(let (?n14 (concat ?n2 ?n13))
(let (?n15 (bvxor ?n3 ?n14))
(let (?n16 (extract[7:0] ?n15))
(let (?n17 (store ?n9 ?n12 ?n16))
(let (?n18 (select ?n17 ?n1))
(let (?n19 (concat ?n2 ?n18))
(flet ($n20 (= ?n1 ?n19))
$n20
)))))))))))))))))))))
