; COMMAND-LINE: --strings-exp
(set-logic SLIA)
(declare-fun a () String)
(assert (>= (str.len a) 2))
(assert (str.in.re a (re.+ (re.range "0" "1"))))
(assert (<= 3 (str.to.int (str.substr a (+ (- 2) (str.len a)) 1))))
(set-info :status unsat)
(check-sat)
