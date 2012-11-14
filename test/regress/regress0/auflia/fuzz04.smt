(benchmark fuzzsmt
:logic QF_AUFLIA
:extrapreds ((p1 Array Array))
:extrafuns ((f1 Array Array Array Array))
:extrafuns ((v3 Array))
:status sat
:formula
(let (?n1 (f1 v3 v3 v3))
(let (?n2 0)
(let (?n3 (store v3 ?n2 ?n2))
(let (?n4 (f1 v3 v3 ?n3))
(let (?n5 (f1 v3 ?n4 v3))
(flet ($n6 (p1 ?n1 ?n5))
$n6
)))))))
