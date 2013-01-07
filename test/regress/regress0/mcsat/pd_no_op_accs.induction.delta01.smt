(benchmark pd_no_op_accs.induction.smt
:logic QF_LRA
:extrafuns ((x_0 Real))
:extrafuns ((x_15 Real))
:status unknown
:formula
(let (?n1 0)
(flet ($n2 (= ?n1 x_0))
(flet ($n3 (not $n2))
(flet ($n4 true)
(let (?n5 2)
(let (?n6 (ite $n4 x_0 ?n5))
(flet ($n7 (= ?n6 x_15))
(flet ($n8 (or $n3 $n7))
(flet ($n9 (<= x_15 ?n5))
(flet ($n10 (>= x_0 ?n1))
(flet ($n11 (and $n9 $n10))
(flet ($n12 (and $n8 $n11))
$n12
)))))))))))))
