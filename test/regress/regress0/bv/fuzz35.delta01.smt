(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[4]))
:status unsat
:formula
(let (?n1 bv4[4])
(let (?n2 bv12[4])
(let (?n3 (bvsub ?n1 ?n2))
(let (?n4 (bvmul v0 ?n3))
(let (?n5 (bvadd ?n4 ?n4))
(let (?n6 bv0[4])
(flet ($n7 (bvsgt ?n5 ?n6))
$n7
))))))))
