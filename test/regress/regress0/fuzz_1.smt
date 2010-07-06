(benchmark fuzzsmt
:logic QF_LRA
:status unsat
:extrafuns ((v0 Real))
:formula
(let (?e1 11)
(let (?e2 1)
(let (?e3 (* v0 ?e2))
(let (?e4 (/ ?e1 (~ ?e1)))
(flet ($e5 (< v0 ?e4))
(flet ($e6 (< ?e3 ?e3))
(let (?e7 (ite $e5 ?e3 ?e4))
(let (?e8 (ite $e5 ?e3 ?e3))
(let (?e9 (ite $e6 v0 ?e4))
(flet ($e10 (< ?e3 ?e7))
(flet ($e11 (< v0 ?e9))
(flet ($e12 (= ?e8 ?e4))
(flet ($e13 (and $e10 $e6))
(flet ($e14 (implies $e12 $e5))
(flet ($e15 (iff $e14 $e14))
(flet ($e16 (iff $e11 $e11))
(flet ($e17 (iff $e16 $e16))
(flet ($e18 (not $e13))
(flet ($e19 (or $e18 $e18))
(flet ($e20 (if_then_else $e15 $e15 $e17))
(flet ($e21 (not $e20))
(flet ($e22 (not $e19))
(flet ($e23 (xor $e21 $e21))
(flet ($e24 (xor $e23 $e22))
$e24
)))))))))))))))))))))))))

