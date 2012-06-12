(benchmark fuzzsmt
:logic QF_AUFBV
:extrafuns ((v0 BitVec[12]))
:extrafuns ((v1 BitVec[11]))
:extrafuns ((a3 Array[1:6]))
:status sat
:formula
(let (?n1 bv0[6])
(let (?n2 bv0[1])
(let (?n3 (store a3 ?n2 ?n1))
(let (?n4 (sign_extend[1] v1))
(let (?n5 (bvor ?n4 v0))
(let (?n6 (extract[11:11] ?n5))
(let (?n7 (select ?n3 ?n6))
(flet ($n8 (bvult ?n1 ?n7))
$n8
)))))))))
