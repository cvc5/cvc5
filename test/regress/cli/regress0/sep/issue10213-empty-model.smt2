; EXPECT: sat
; EXPECT: (
; EXPECT: (define-fun x () Int 0)
; EXPECT: )
; EXPECT: (heap
; EXPECT: sep.emp
; EXPECT: (= (as sep.nil Int) 0)
; EXPECT: )
; DISABLE-TESTER: model
(set-logic ALL)
(set-option :produce-models true)
(declare-heap (Int Int))
(declare-fun x () Int)
(assert (= x (as sep.nil Int)))
(check-sat)
(get-model)
