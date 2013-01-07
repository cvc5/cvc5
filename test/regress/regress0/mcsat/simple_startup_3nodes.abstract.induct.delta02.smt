(benchmark tta_startup
:logic QF_LRA
:extrafuns ((x_12 Real))
:extrafuns ((x_23 Real))
:extrafuns ((x_25 Real))
:extrafuns ((x_40 Real))
:extrafuns ((x_38 Real))
:status unknown
:formula
(flet ($n1 false)
(let (?n2 1)
(flet ($n3 (= ?n2 x_38))
(flet ($n4 (not $n3))
(let (?n5 (- x_23 x_25))
(flet ($n6 (<= ?n5 x_12))
(flet ($n7 (or $n4 $n6))
(flet ($n8 (= ?n2 x_40))
(flet ($n9 (not $n8))
(flet ($n10 (<= x_23 x_12))
(flet ($n11 (not $n10))
(let (?n12 (- x_25 x_23))
(flet ($n13 (<= ?n12 x_12))
(flet ($n14 (or $n9 $n13))
(flet ($n15 (and $n11 $n14))
(flet ($n16 (and $n9 $n15))
(flet ($n17 (and $n7 $n16))
(flet ($n18 (iff $n1 $n17))
$n18
)))))))))))))))))))
