(benchmark read5.smt
:logic QF_AX
:status unsat
:extrafuns ((a Index))
:extrafuns ((S Array))
:extrafuns ((SS Array))
:status unknown
:formula
(flet ($n1 (= S SS))
(let (?n2 (select S a))
(let (?n3 (store SS a ?n2))
(flet ($n4 (= S ?n3))
(flet ($n5 true)
(flet ($n6 (if_then_else $n1 $n4 $n5))
(flet ($n7 (not $n6))
$n7
))))))))
