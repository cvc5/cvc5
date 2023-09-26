; COMMAND-LINE: --solve-int-as-bv=5524936381719514648
; EXPECT-ERROR: Error in option parsing
; ERROR-SCRUBBER: grep -o "Error in option parsing"
; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXIT: 1
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* x x) y))
(check-sat)

