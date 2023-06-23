; DISABLE-TESTER: dump
; SCRUBBER: grep -o '(error "Parse Error:'
; EXPECT: (error "Parse Error:
; EXIT: 1
(set-logic ALL)
(declare-fun real_2 () Real)
(declare-fun real_0 () Real)
(assert (not (= (or (not (= real_0 (to_real 0))) (not (= real_2 (to_real 0))) (not (= ((_ extract 1.0 real_1) (to_real 0)))) bool_0))))
