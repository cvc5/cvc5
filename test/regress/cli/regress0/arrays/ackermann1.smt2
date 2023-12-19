; EXPECT:
; SCRUBBER: grep -v "Ackermannization is not supported for kind"
; EXIT: 1
(set-logic QF_AX)
(declare-const x4 Bool)
(set-option :ackermann true)
(declare-const x (Array Bool Bool))
(assert (select x false))
(assert (select (store x true false) x4))
(check-sat)
