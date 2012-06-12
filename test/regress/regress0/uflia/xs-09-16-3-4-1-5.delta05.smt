(benchmark mathsat
:logic QF_UFLIA
:extrafuns ((select_format Int Int))
:extrafuns ((adr_lo Int))
:extrafuns ((arg1 Int))
:status unknown
:formula
(let (?n1 (select_format arg1))
(flet ($n2 (= ?n1 adr_lo))
(let (?n3 0)
(flet ($n4 (= adr_lo ?n3))
(let (?n5 1)
(let (?n6 (select_format ?n5))
(flet ($n7 (= adr_lo ?n6))
(flet ($n8 (or $n4 $n7))
(flet ($n9 (and $n2 $n8))
$n9
))))))))))
