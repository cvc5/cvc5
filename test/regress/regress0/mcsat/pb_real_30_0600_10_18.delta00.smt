(benchmark B_
:logic QF_UFLRA
:extrafuns ((f0_1 Real Real))
:extrafuns ((x2 Real))
:extrafuns ((x6 Real))
:status unknown
:formula
(flet ($n1 (= x2 x6))
(let (?n2 (f0_1 x6))
(let (?n3 19)
(flet ($n4 (< ?n2 ?n3))
(flet ($n5 (not $n4))
(let (?n6 (f0_1 x2))
(let (?n7 20)
(let (?n8 (~ ?n7))
(flet ($n9 (< ?n6 ?n8))
(flet ($n10 (and $n5 $n9))
(flet ($n11 (and $n1 $n10))
$n11
))))))))))))
