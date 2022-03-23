; COMMAND-LINE: --solve-int-as-bv=4
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (> (- 1) x))
(assert (>= y x))
(assert (< 0 y))
(set-info :status sat)
(check-sat)
