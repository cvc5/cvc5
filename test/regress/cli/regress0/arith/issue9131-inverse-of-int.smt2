; COMMAND-LINE: -q

; This is a minimized version of the problem in the original issue. It
; triggered the same type checking exception before the fix (without triggering
; the secondary assertion failure of decisionLevel() == 0.
(set-logic QF_NIRAT)
(declare-const x Int)
(assert (= (to_int (arcsin x)) x))
(set-info :status sat)
(check-sat)
