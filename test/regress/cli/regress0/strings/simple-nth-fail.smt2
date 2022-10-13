; COMMAND-LINE: --no-strings-code-elim
; COMMAND-LINE: --strings-code-elim
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const i Int)
(declare-const n Int)
(assert (>= n 0))
(assert (= i (str.to_int (str.from_code n))))
(assert (>= i 0))
(check-sat)
