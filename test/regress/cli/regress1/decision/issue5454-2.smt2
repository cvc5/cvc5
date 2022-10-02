; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic ANIA)
(declare-fun i () Int)
(declare-fun a () (Array Int Bool))
(declare-fun b () (Array Bool (Array Int Bool)))
(assert (= (store b (>= i 0) a) (store b false (store (store a 0 true) i true))))
(check-sat)
