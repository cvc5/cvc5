(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((a2 Array[12:9]))
:status sat
:formula
(let (?n1 bv0[13])
(let (?n2 (bvsdiv ?n1 ?n1))
(let (?n3 bv0[12])
(let (?n4 (select a2 ?n3))
(let (?n5 (sign_extend[4] ?n4))
(let (?n6 (bvmul ?n2 ?n5))
(flet ($n7 (bvsge ?n1 ?n6))
$n7
))))))))
