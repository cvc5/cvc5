(benchmark fuzzsmt
:logic QF_BV
:extrafuns ((v0 BitVec[1]))
:status unsat:formula
(flet ($n1 (bvsgt v0 v0))
$n1
))
