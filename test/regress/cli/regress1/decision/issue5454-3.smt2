; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-logic AUFLIA)
(declare-fun v () Bool)
(declare-fun i () Int)
(declare-fun i8 () Int)
(declare-fun u (Int Int Int Int Int Int) Bool)
(declare-fun ar () (Array Bool Bool))
(declare-fun a () (Array Int Int))
(declare-fun arr-- () (Array Bool Int))
(declare-fun arr () (Array Bool (Array Int Bool)))
(declare-fun arr- () (Array Bool (Array Bool (Array Int Bool))))
(assert (= arr- (store (store arr- false arr) (or (u (- 1) (select a i8) i (- 1) (select arr-- (select ar (= ar (store ar v true)))) 0) (not (u (- 1) (select a i8) i (- 1) (select arr-- (select ar (= ar (store ar v true)))) 0))) arr)))
(check-sat)
