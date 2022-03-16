; COMMAND-LINE: --solve-int-as-bv=5
(set-logic QF_NIA)
(set-info :status sat)
(declare-const x Int)
(assert (< x 0))
(check-sat)
