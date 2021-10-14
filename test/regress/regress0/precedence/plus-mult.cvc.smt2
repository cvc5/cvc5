; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(check-sat-assuming ( (not (let ((_let_1 (- (+ (- (+ a (/ (* 2 b) 3)) (* (/ c 4) 5)) (/ d 6)) e))) (= _let_1 _let_1))) ))
