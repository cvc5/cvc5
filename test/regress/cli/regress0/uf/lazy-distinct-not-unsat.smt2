; EXPECT: unsat
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun f () Int)
(assert (not (distinct a b c d e f)))
(assert 
(and (not (= a b)) (not (= a c)) (not (= a d)) (not (= a e)) (not (= a f)) (not (= b c)) (not (= b d)) (not (= b e)) (not (= b f)) (not (= c d)) (not (= c e)) (not (= c f)) (not (= d e)) (not (= d f)) (not (= e f))))
(check-sat)
