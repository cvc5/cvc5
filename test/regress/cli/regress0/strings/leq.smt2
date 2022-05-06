; COMMAND-LINE: --strings-exp
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (or
  (not (str.<= (str.++ "A" x) (str.++ "B" y)))
  (not (str.<= (str.++ "A" x) (str.++ "BC" y)))
  (str.<= (str.++ "A" "D" x) (str.++ "AC" y))))
(set-info :status unsat)
(check-sat)
