(benchmark fuzzsmt
:logic QF_AUFLIA
:extrapreds ((p1 Array Array Array))
:extrafuns ((v1 Array))
:extrafuns ((f1 Array Array Array Array))
:status sat
:formula
(let (?n1 0)
(let (?n2 (store v1 ?n1 ?n1))
(let (?n3 (f1 v1 v1 ?n2))
(let (?n4 (f1 v1 ?n2 v1))
(let (?n5 (f1 v1 ?n4 ?n2))
(flet ($n6 (p1 ?n3 ?n5 v1))
$n6
)))))))
