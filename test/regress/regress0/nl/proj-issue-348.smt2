; EXIT: 1
; EXPECT: Cannot translate to BV
; SCRUBBER: sed -n "s/.*\(Cannot translate to BV\).*/\1/p"
(set-logic ALL)
(set-option :solve-int-as-bv 1)
(declare-const x Real)
(assert (>= 0.0 x))
(check-sat)
