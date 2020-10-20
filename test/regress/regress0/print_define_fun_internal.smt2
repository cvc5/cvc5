; REQUIRES: dumping
; COMMAND-LINE: --solve-real-as-int --dump=assertions:post-real-to-int
; EXIT: 0
; SCRUBBER: grep -v -E '.*'
(set-logic QF_NRA)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a a) 4))
(assert (= (* b b) 0))
(assert (= (+ (* a a) (* b b)) 4))
(check-sat)
