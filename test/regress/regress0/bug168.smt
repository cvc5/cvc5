(benchmark fuzzsmt
:logic QF_LRA
:extrafuns ((v0 Real))
:status sat
:formula
(let (?n1 3)
(flet ($n2 (distinct ?n1 v0))
$n2
)))
