; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(assert (= c d))
(assert (> (+ a (div 0 b)) c))
(assert (= b (- 1)))
(check-sat)
