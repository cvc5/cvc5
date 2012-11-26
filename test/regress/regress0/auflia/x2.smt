(benchmark fuzzsmt
:logic QF_AUFLIA
:extrafuns ((v4 Array))
:extrafuns ((f0 Int Int))
:extrapreds ((p0 Int Int Int))
:status sat
:formula
(let (?n1 0)
(flet ($n2 (p0 ?n1 ?n1 ?n1))
(let (?n3 1)
(let (?n4 (ite $n2 ?n3 ?n1))
(flet ($n5 (< ?n1 ?n4))
(flet ($n6 (p0 ?n3 ?n1 ?n1))
(let (?n7 (ite $n6 ?n3 ?n1))
(let (?n8 (ite $n5 ?n7 ?n3))
(flet ($n9 (< ?n1 ?n8))
(flet ($n10 true)
(let (?n11 3)
(let (?n12 (f0 ?n1))
(let (?n13 (* ?n11 ?n12))
(let (?n14 (select v4 ?n1))
(flet ($n15 (> ?n13 ?n14))
(flet ($n16 (xor $n10 $n15))
(flet ($n17 false)
(flet ($n18 (implies $n16 $n17))
(flet ($n19 (and $n9 $n18))
$n19
))))))))))))))))))))
