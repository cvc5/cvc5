; COMMAND-LINE: -o block-model -i
; SCRUBBER: grep -o "block-model"
; EXPECT: block-model
; EXPECT: block-model
; EXIT: 0
; DISABLE-TESTER: dump
(set-logic ALL)
(set-option :incremental true)
(set-option :produce-models true)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (or (= x 4) (= x 5)))
(assert (> x 0))
(assert (> y 0))
(check-sat)
(block-model :literals)
(check-sat)
(block-model :literals)
