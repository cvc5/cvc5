; SCRUBBER: grep -o "Cannot translate to BV"
; EXPECT: Cannot translate to BV
; EXIT: 1
(set-option :solve-int-as-bv 1)
(set-logic ALL)
(declare-fun a () String)
(assert (ite (= (- 1) (str.to_int a)) false true))
(check-sat)
