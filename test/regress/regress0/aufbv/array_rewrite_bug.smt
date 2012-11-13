(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((a1 Array[14:11]))
:status sat
:formula
(let (?n1 bv1[16])
(let (?n2 (extract[13:0] ?n1))
(let (?n3 bv0[11])
(let (?n4 (store a1 ?n2 ?n3))
(let (?n5 bv0[14])
(let (?n6 (select a1 ?n5))
(let (?n7 (store ?n4 ?n5 ?n6))
(let (?n8 (zero_extend[3] ?n6))
(let (?n9 (select ?n7 ?n8))
(let (?n10 (sign_extend[2] ?n9))
(let (?n11 (zero_extend[3] ?n10))
(flet ($n12 (bvugt ?n1 ?n11))
$n12
)))))))))))))
