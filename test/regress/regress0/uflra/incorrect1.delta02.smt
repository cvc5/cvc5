(benchmark fuzzsmt
:logic QF_UFLRA
:extrafuns ((f1 Real Real Real))
:status sat
:formula
(let (?n1 6)
(let (?n2 (~ ?n1))
(let (?n3 (/ ?n1 ?n2))
(let (?n4 1)
(let (?n5 (+ ?n3 ?n4))
(let (?n6 (f1 ?n4 ?n4))
(flet ($n7 (distinct ?n5 ?n6))
$n7
))))))))
