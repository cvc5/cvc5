; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(declare-fun f () Int)
(assert (<= 0 a))
(assert (= 0 c))
(assert (not (= a b)))
(assert (= b c))
(assert (not (= d f)))
(check-sat)
(push)
(check-sat)
(pop)
(assert (> e a))
(assert (= e 0))
(check-sat)
