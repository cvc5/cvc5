(benchmark pd_init_op_accs.induction.smt
:logic QF_LRA
:extrafuns ((x_0 Real))
:extrapreds ((x_5))
:extrafuns ((x_12 Real))
:status unknown
:formula
(let (?n1 0)
(flet ($n2 (= x_12 ?n1))
(flet ($n3 (= x_12 x_0))
(let (?n4 2)
(flet ($n5 (= x_12 ?n4))
(let (?n6 1)
(flet ($n7 (= x_12 ?n6))
(flet ($n8 (or x_5 $n7))
(flet ($n9 (or $n5 $n8))
(flet ($n10 (>= x_12 ?n1))
(flet ($n11 (not x_5))
(flet ($n12 (= ?n1 x_0))
(flet ($n13 (not $n12))
(flet ($n14 (or $n11 $n13))
(flet ($n15 (and $n10 $n14))
(flet ($n16 (and $n9 $n15))
(flet ($n17 (and $n3 $n16))
(flet ($n18 (and $n2 $n17))
$n18
)))))))))))))))))))
